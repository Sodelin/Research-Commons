"""Declared RNA endpoint calculations, independent of any model SDK.

The public service accepts an entire matched scenario mapping, including REF.
Non-reference tracks must already be mapped to reference-retained per-base
coordinates by the caller. Insertions are excluded, deletions zero-filled, and
the original mask denominator is unchanged. The caller authenticates each ALT
sequence digest before mapping; this service cannot reconstruct ALT sequences.

Direct describes the source model modality, not a measured quantity. Scalar
aggregates and their changes are derived calculations. A difference of two
maxima is not the maximum of positional differences. The explicit two-window
PAS proxy below is not AlphaGenome's recommended multisplit PAS scorer.
"""
from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict
import json
import math
import re

from .contracts import (CONTRACT_VERSION, Context, EndpointSpec, MolecularError,
                        Prediction, PredictionTrack, require, sequence_sha256,
                        validate_prediction)

_OUTPUT_BY_FAMILY = {"expression": "RNA_SEQ", "splice_sites": "SPLICE_SITES",
                     "splice_usage": "SPLICE_SITE_USAGE",
                     "splice_junctions": "SPLICE_JUNCTIONS",
                     "polyadenylation": "RNA_SEQ"}


def _endpoint_identity(endpoint: EndpointSpec) -> dict:
    return {"id": endpoint.id, "family": endpoint.family,
            "output_type": endpoint.output_type,
            "aggregation": endpoint.aggregation, "scale": endpoint.scale,
            "pseudocount": endpoint.pseudocount,
            "alignment": endpoint.alignment,
            "region": {"start0": endpoint.start0, "end0": endpoint.end0,
                       "coordinate_convention": "0-based-half-open"},
            "site_windows": [list(w) for w in endpoint.site_windows],
            "site_annotation_source": endpoint.site_annotation_source,
            "site_annotation_version": endpoint.site_annotation_version}


def _unavailable(endpoint: EndpointSpec, error: MolecularError) -> dict:
    return {**_endpoint_identity(endpoint), "status": error.status,
            "semantics": "unavailable", "code": error.code,
            "reason": error.message, "value": None,
            "raw_values_by_scenario": {}, "values_by_scenario": {},
            "changes_vs_reference": {}, "successful_computation": False,
            "biological_conclusion_established": False}


def _track(context: Context, prediction: Prediction, output_type: str) -> PredictionTrack:
    tracks = [t for t in prediction.tracks if t.output_type == output_type]
    require(bool(tracks), "MISSING_OUTPUT", f"no {output_type} track for {prediction.scenario}", "UNSUPPORTED")
    require(len(tracks) == 1, "AMBIGUOUS_TRACK", f"select exactly one {output_type} track before scoring", "UNSUPPORTED")
    track = tracks[0]
    require(track.bin_size == 1, "PER_BASE_REQUIRED", "initial endpoint scorer requires per-base tracks; no implicit bin expansion", "UNSUPPORTED")
    if prediction.scenario != "REF":
        require(track.metadata.get("alignment") == "reference_retained",
                "UNALIGNED_ALTERNATIVE", "ALT tracks require explicit reference-retained alignment", "UNSUPPORTED")
    if output_type in {"SPLICE_SITES", "SPLICE_SITE_USAGE"}:
        require(all(v <= 1 for v in track.values), "PROBABILITY_RANGE",
                "splice probability/usage values must lie in [0,1]")
    return track


def _aggregate(track: PredictionTrack, windows: tuple[tuple[int, int], ...], aggregation: str) -> float:
    count = sum(end - start for start, end in windows)
    require(count > 0, "EMPTY_MASK", "endpoint contains no annotated reference bases", "UNSUPPORTED")
    values = (track.values[pos - track.interval_start0]
              for start, end in windows for pos in range(start, end))
    try:
        if aggregation == "max":
            value = float(max(values))
        else:
            value = math.fsum(values)
            if aggregation == "mean":
                value /= count
    except (OverflowError, ValueError) as error:
        raise MolecularError("UNKNOWN", "NUMERICAL_RANGE", "aggregate exceeds finite floating-point range") from error
    require(math.isfinite(value), "NUMERICAL_RANGE", "aggregate is nonfinite", "UNKNOWN")
    return value


def _track_identity(track: PredictionTrack) -> tuple:
    name = track.metadata.get("name")
    require(isinstance(name, str) and bool(name) and not any(ord(c) < 32 for c in name),
            "TRACK_ID", "identify the exact model track before aggregation", "UNSUPPORTED")
    return (track.output_type, name, track.bin_size, track.interval_start0,
            track.tissue, track.strand, track.gene_id, track.transcript_id,
            track.metadata.get("tissue_specific"))


def _log_smoothed(value: float, pseudocount: float) -> float:
    # Avoid an overflowing addition even when both finite operands are large.
    larger, smaller = max(value, pseudocount), min(value, pseudocount)
    return math.log(larger) + math.log1p(smaller / larger)


def _scaled(value: float, scale: str, pseudocount: float) -> float:
    if scale == "linear":
        return value
    result = _log_smoothed(value, pseudocount)
    return result if scale == "log" else result / math.log(2)


def _windows(context: Context, endpoint: EndpointSpec) -> tuple[tuple[int, int], ...]:
    transcript = context.transcript
    if endpoint.family == "expression":
        return tuple((max(start, endpoint.start0), min(end, endpoint.end0))
                     for start, end in transcript.exons
                     if max(start, endpoint.start0) < min(end, endpoint.end0))
    start, end = max(transcript.start0, endpoint.start0), min(transcript.end0, endpoint.end0)
    return ((start, end),) if start < end else ()


def _score_endpoint(context: Context, endpoint: EndpointSpec,
                    predictions: Mapping[str, Prediction]) -> dict:
    if endpoint.family.lower() in {"psi", "psi3", "psi5"}:
        raise MolecularError("UNSUPPORTED", "PSI_METHOD_UNAVAILABLE", "PSI needs an explicit validated derived method; it is not a direct model output")
    endpoint.validate(context)
    require(endpoint.output_type == _OUTPUT_BY_FAMILY[endpoint.family],
            "FAMILY_OUTPUT", "endpoint family and model output do not match", "UNSUPPORTED")
    if endpoint.family == "splice_junctions":
        raise MolecularError("UNSUPPORTED", "JUNCTION_ADAPTER_UNAVAILABLE",
                             "paired splice-junction coordinates/counts need a typed junction adapter; a per-base track is insufficient")
    require(endpoint.aggregation in ({"site_ratio"} if endpoint.family == "polyadenylation" else {"sum", "mean", "max"}),
            "FAMILY_AGGREGATION", "aggregation is unavailable for this endpoint family", "UNSUPPORTED")
    require(endpoint.family != "expression" or endpoint.aggregation in {"sum", "mean"},
            "EXPRESSION_AGGREGATION", "expression uses an explicit exon-mask sum or mean", "UNSUPPORTED")
    tracks = {scenario: _track(context, prediction, endpoint.output_type)
              for scenario, prediction in predictions.items()}
    reference_identity = _track_identity(tracks["REF"])
    require(all(_track_identity(t) == reference_identity for t in tracks.values()),
            "MISMATCHED_TRACKS", "exact track name/modality/bin/tissue/strand/annotation differs across scenarios")
    windows = _windows(context, endpoint)
    raw, values, auxiliary = {}, {}, {}
    method = "annotated_transcript_exon_coverage_proxy_v1" if endpoint.family == "expression" else "declared_per_base_splice_aggregate_v1"
    semantics = "derived"
    if endpoint.family == "polyadenylation":
        require(len(endpoint.site_windows) == 2, "PAS_WINDOWS_REQUIRED",
                "declare exactly two annotation windows: proximal first, distal second", "UNSUPPORTED")
        proximal, distal = endpoint.site_windows
        require(context.transcript.start0 <= proximal[0] < proximal[1] <= context.transcript.end0
                and context.transcript.start0 <= distal[0] < distal[1] <= context.transcript.end0,
                "PAS_TRANSCRIPT_WINDOW", "PAS windows must lie within the annotated transcript")
        ordered = proximal[1] <= distal[0] if context.transcript.strand == "+" else distal[1] <= proximal[0]
        require(ordered, "PAS_WINDOW_ORDER", "proximal/distal windows must be disjoint and ordered along transcript strand")
        method, semantics = "two_annotated_window_coverage_ratio_v1", "derived"
        windows = endpoint.site_windows
        for scenario, track in tracks.items():
            prox = _aggregate(track, (proximal,), "mean")
            dist = _aggregate(track, (distal,), "mean")
            log_ratio = _log_smoothed(dist, endpoint.pseudocount) - _log_smoothed(prox, endpoint.pseudocount)
            # Scale both positive sums to avoid overflow in numerator/denominator.
            normalizer = max(dist, prox, endpoint.pseudocount)
            numerator = dist / normalizer + endpoint.pseudocount / normalizer
            denominator = prox / normalizer + endpoint.pseudocount / normalizer
            require(denominator > 0, "NUMERICAL_RANGE", "PAS denominator underflows finite range", "UNKNOWN")
            ratio = numerator / denominator
            require(math.isfinite(ratio) and ratio > 0, "NUMERICAL_RANGE", "PAS ratio cannot be represented finitely", "UNKNOWN")
            raw[scenario] = ratio
            values[scenario] = ratio if endpoint.scale == "linear" else log_ratio if endpoint.scale == "log" else log_ratio / math.log(2)
            auxiliary[scenario] = {"proximal_mean": prox, "distal_mean": dist}
    else:
        for scenario, track in tracks.items():
            raw[scenario] = _aggregate(track, windows, endpoint.aggregation)
            values[scenario] = _scaled(raw[scenario], endpoint.scale, endpoint.pseudocount)
    changes = {scenario: value - values["REF"] for scenario, value in values.items()}
    require(all(math.isfinite(v) for v in (*values.values(), *changes.values())),
            "NUMERICAL_RANGE", "scaled value or difference is nonfinite", "UNKNOWN")
    result = {**_endpoint_identity(endpoint), "status": "SUCCESS", "semantics": semantics,
              "source_output_semantics": "direct_model_prediction",
              "method": method, "value": values["REF"],
              "raw_values_by_scenario": raw, "values_by_scenario": values,
              "changes_vs_reference": changes,
              "direction_by_scenario": {s: "increase" if v > 0 else "decrease" if v < 0 else "unchanged" for s, v in changes.items()},
              "reference_mask_windows": [list(w) for w in windows],
              "reference_mask_base_count": sum(end - start for start, end in windows),
              "track_metadata_by_scenario": {s: {**t.metadata, "tissue": t.tissue, "strand": t.strand} for s, t in tracks.items()},
              "formula_matches_recommended_expression_transform": False,
              "successful_computation": True, "biological_conclusion_established": False}
    if endpoint.family == "expression":
        result["scale_definition"] = "raw aggregation" if endpoint.scale == "linear" else f"{endpoint.scale}(raw aggregation + pseudocount)"
        result["formula_matches_recommended_expression_transform"] = endpoint.aggregation == "mean" and endpoint.scale == "log" and endpoint.pseudocount == 0.001
        result["limitations"] = ["Declared transcript-exon coverage proxy; not a measured gene count or the SDK gene scorer's union of all gene exons."]
    elif endpoint.family == "polyadenylation":
        result.update({"window_values_by_scenario": auxiliary,
                       "scale_definition": "(distal_mean+p)/(proximal_mean+p), then declared log if requested",
                       "limitations": ["Declared two-window coverage proxy; not normalized isoform usage or the official maximum across all proximal/distal splits."]})
    else:
        # Separate diagnostic on the direct modality, never substitute it for y.
        ref = tracks["REF"]
        result["max_absolute_positional_change_vs_reference"] = {
            s: max(abs(t.values[pos-t.interval_start0] - ref.values[pos-ref.interval_start0])
                   for start, end in windows for pos in range(start, end))
            for s, t in tracks.items()}
        result["scale_definition"] = "raw aggregation" if endpoint.scale == "linear" else f"{endpoint.scale}(raw aggregation + pseudocount)"
        result["limitations"] = ["Per-scenario scalar change is a difference of declared aggregates; it is distinct from the positional maximum-change diagnostic."]
    return result


def analyse_rna(context: Context, endpoint_specs: tuple[EndpointSpec, ...],
                predictions_by_scenario: Mapping[str, Prediction]) -> dict:
    """Score matched predictions; unavailable endpoints remain explicit.

    Context/identity failures raise MolecularError. Endpoint capability failures
    return unavailable entries. Mixed success/unavailable yields UNKNOWN, all
    unavailable yields UNSUPPORTED, and all successful yields SUCCESS. A caller
    may use only SUCCESS endpoints for a declared-scale interaction.
    """
    context.validate()
    require(bool(endpoint_specs) and len({e.id for e in endpoint_specs}) == len(endpoint_specs),
            "ENDPOINTS", "unique nonempty endpoint list required")
    require(isinstance(predictions_by_scenario, Mapping) and "REF" in predictions_by_scenario
            and 1 <= len(predictions_by_scenario) <= 4, "SCENARIOS", "provide REF and at most four matched scenarios")
    for scenario, prediction in predictions_by_scenario.items():
        require(isinstance(scenario, str) and bool(scenario) and not any(ord(c) < 32 for c in scenario)
                and prediction.scenario == scenario, "SCENARIO", "prediction scenario and mapping key must match")
        require(isinstance(prediction.sequence_sha256, str) and re.fullmatch(r"[0-9a-f]{64}", prediction.sequence_sha256) is not None,
                "SEQUENCE_HASH", "explicit lowercase SHA256 sequence digest required")
        validate_prediction(context, prediction,
                            expected_sequence_sha256=sequence_sha256(context.window.sequence) if scenario == "REF" else None)
        for track in prediction.tracks:
            try:
                json.dumps(track.metadata, allow_nan=False)
            except (TypeError, ValueError) as error:
                raise MolecularError("INVALID_INPUT", "TRACK_METADATA", "track metadata must be finite JSON") from error
    evidence = {p.evidence for p in predictions_by_scenario.values()}
    require(len(evidence) == 1, "MIXED_EVIDENCE", "do not combine synthetic and real-model predictions")
    endpoints = {}
    for endpoint in endpoint_specs:
        try:
            endpoints[endpoint.id] = _score_endpoint(context, endpoint, predictions_by_scenario)
        except MolecularError as error:
            if error.status == "INVALID_INPUT":
                raise
            endpoints[endpoint.id] = _unavailable(endpoint, error)
    statuses = {entry["status"] for entry in endpoints.values()}
    status = "SUCCESS" if statuses == {"SUCCESS"} else "UNSUPPORTED" if statuses == {"UNSUPPORTED"} else "UNKNOWN"
    transcript = context.transcript
    return {"contract_version": CONTRACT_VERSION, "application": "rna_processing",
            "status": status, "evidence": next(iter(evidence)),
            "successful_computation": status == "SUCCESS",
            "biological_conclusion_established": False,
            "settings_sha256": context.settings_sha256,
            "input_sequence_sha256": {s: p.sequence_sha256 for s, p in predictions_by_scenario.items()},
            "identity": {"assembly": context.window.assembly, "chromosome": context.window.chromosome,
                         "window_start0": context.window.start0, "window_end0": context.window.end0,
                         "reference_source": context.window.source, "reference_guard_sha256": context.window.sha256,
                         "gene_id": transcript.gene_id, "transcript_id": transcript.transcript_id,
                         "annotation_source": transcript.source, "annotation_version": transcript.version,
                         "transcript_start0": transcript.start0, "transcript_end0": transcript.end0,
                         "strand": transcript.strand, "tissue": context.tissue,
                         "model_version": context.model_version, "preprocessing": context.preprocessing},
            "endpoint_specs": [asdict(e) for e in endpoint_specs], "endpoints": endpoints}
