"""Matched single-sequence haplotype predictions; no diploid aggregation.

Native assembly uses original coordinates. Indel endpoint alignment retains
reference bases, excludes inserted bases and zero-fills deletions. This is our
explicit endpoint policy, not the SDK variant scorer's insertion-max policy.
"""
from __future__ import annotations

from dataclasses import asdict, replace
import hashlib
import json
import math
import os
from pathlib import Path
import subprocess
from typing import TYPE_CHECKING

from .contracts import (
    CONTRACT_VERSION, Context, HaplotypeRequest, MolecularError, Prediction,
    PredictionTrack, identity_sha256, require, sequence_sha256,
    validate_prediction, preflight_endpoints,
)

if TYPE_CHECKING:
    from .providers import PredictionProvider

MAX_BRIDGE_BYTES = 8 * 2**20
SCENARIOS = ("REF", "A", "B", "AB")
ALIGNMENT_POLICY = "reference_retained_exclude_insertions_zero_deletions_fixed_reference_denominator"


def _core_path(core_binary: str | Path | None) -> Path:
    if core_binary is None:
        core_binary = os.environ.get("MOLECULAR_HAPLOTYPE_CORE")
    if core_binary is None:
        core_binary = Path(__file__).resolve().parents[1] / "core" / "target" / "debug" / "molecular-haplotype-core"
    path = Path(core_binary)
    require(path.is_file(), "CORE_UNAVAILABLE", "configure the already-built native core binary", "UNSUPPORTED")
    require(path.stat().st_size <= 32 * 2**20, "CORE_SIZE", "native binary exceeds local build bound", "RESOURCE_LIMIT")
    return path


def _bridge_text(request: HaplotypeRequest) -> bytes:
    w = request.context.window
    rows = ["molecular-haplotype-v1",
            "\t".join(("window", w.assembly, w.chromosome, str(w.start0), w.sequence, w.guard_sequence)),
            "\t".join(("phase", request.phase.kind, "true" if request.phase.evidence else "false"))]
    for variant in request.variants:
        rows.append("\t".join(("variant", variant.id, variant.chromosome,
                               str(variant.position), variant.ref, variant.alt)))
    # The declared envelope makes crop refusal deterministic before prediction.
    rows.append(f"roi\t{min(e.start0 for e in request.endpoints)}\t{max(e.end0 for e in request.endpoints)}")
    encoded = ("\n".join(rows) + "\n").encode("utf-8")
    require(len(encoded) <= MAX_BRIDGE_BYTES, "INPUT_SIZE", "native request exceeds 8MiB", "RESOURCE_LIMIT")
    return encoded


def assemble_haplotypes(request: HaplotypeRequest, *, core_binary: str | Path | None = None) -> dict:
    """Validate and invoke the versioned stdin bridge; raise structured errors."""
    request.validate()
    path = _core_path(core_binary)
    binary_sha = hashlib.sha256(path.read_bytes()).hexdigest()
    payload = _bridge_text(request)
    try:
        process = subprocess.run([str(path)], input=payload, capture_output=True, timeout=30)
    except subprocess.TimeoutExpired as error:
        raise MolecularError("RESOURCE_LIMIT", "CORE_TIMEOUT", "native sequence construction exceeded time limit") from error
    except OSError as error:
        raise MolecularError("EXECUTION_FAILURE", "CORE_EXECUTION", "native core could not execute") from error
    require(hashlib.sha256(path.read_bytes()).hexdigest() == binary_sha,
            "CORE_IDENTITY", "native binary changed during execution", "EXECUTION_FAILURE")
    require(len(process.stdout) <= MAX_BRIDGE_BYTES, "CORE_OUTPUT_SIZE", "native output exceeds 8MiB", "RESOURCE_LIMIT")
    try:
        result = json.loads(process.stdout)
    except (ValueError, UnicodeDecodeError) as error:
        raise MolecularError("EXECUTION_FAILURE", "CORE_PROTOCOL", "native core returned malformed JSON") from error
    require(isinstance(result, dict) and result.get("schema") == "molecular-haplotype-result-v1",
            "CORE_PROTOCOL", "native result schema differs", "EXECUTION_FAILURE")
    if result.get("status") != "SUCCESS":
        status = result.get("status")
        require(status in {"INVALID_INPUT", "UNSUPPORTED", "RESOURCE_LIMIT"},
                "CORE_PROTOCOL", "unknown native refusal status", "EXECUTION_FAILURE")
        raise MolecularError(status, str(result.get("code", "CORE_REFUSAL")), str(result.get("message", "native refusal")))
    require(process.returncode == 0 and not process.stderr,
            "CORE_EXECUTION", "native execution did not complete cleanly", "EXECUTION_FAILURE")
    w = request.context.window
    require(result.get("assembly") == w.assembly and result.get("chromosome") == w.chromosome
            and result.get("window_start0") == w.start0 and result.get("sequence_length") == len(w.sequence)
            and result.get("coordinate_policy") == "fixed_left_edit_guard_crop_first_L",
            "CORE_PROTOCOL", "native result does not bind this window/policy", "EXECUTION_FAILURE")
    require(result.get("phase") == {"kind": request.phase.kind, "evidence_present": bool(request.phase.evidence)},
            "CORE_PROTOCOL", "native phase result differs", "EXECUTION_FAILURE")
    require(isinstance(result.get("scenarios"), dict) and set(result["scenarios"]) == set(SCENARIOS),
            "CORE_PROTOCOL", "native result does not contain the four conditions", "EXECUTION_FAILURE")
    for scenario, details in result["scenarios"].items():
        require(isinstance(details, dict) and isinstance(details.get("sequence"), str)
                and len(details["sequence"]) == len(w.sequence) and set(details["sequence"]) <= set("ACGTN"),
                "CORE_PROTOCOL", "native scenario sequence differs from fixed-length contract", "EXECUTION_FAILURE")
        require(details.get("counterfactual") is (scenario == "AB" and request.phase.kind != "cis"),
                "CORE_PROTOCOL", "native counterfactual label differs", "EXECUTION_FAILURE")
        _validate_coordinate_map(request.context, details)
    result["native_binary_sha256"] = binary_sha
    result["native_request_sha256"] = hashlib.sha256(payload).hexdigest()
    return result


def _validate_coordinate_map(context: Context, details: dict) -> None:
    maps = details.get("coordinate_map")
    require(isinstance(maps, list) and bool(maps), "CORE_MAP", "missing coordinate map", "EXECUTION_FAILURE")
    cursor = 0
    previous_ref = context.window.start0
    for piece in maps:
        require(isinstance(piece, dict), "CORE_MAP", "malformed coordinate map", "EXECUTION_FAILURE")
        a, b = piece.get("sequence_start"), piece.get("sequence_end")
        r, z = piece.get("reference_start0"), piece.get("reference_end0")
        require(type(a) is int and type(b) is int and a == cursor < b <= len(context.window.sequence),
                "CORE_MAP", "map does not tile the fixed sequence", "EXECUTION_FAILURE")
        if r is None or z is None:
            require(r is None and z is None, "CORE_MAP", "inserted segment has partial reference mapping", "EXECUTION_FAILURE")
        else:
            require(type(r) is int and type(z) is int and previous_ref <= r < z
                    and z-r == b-a and z <= context.window.end0 + len(context.window.guard_sequence),
                    "CORE_MAP", "reference segment is invalid or nonmonotone", "EXECUTION_FAILURE")
            previous_ref = z
        cursor = b
    require(cursor == len(context.window.sequence), "CORE_MAP", "incomplete map", "EXECUTION_FAILURE")
    for field in ("deleted_reference_ranges", "cropped_reference_ranges"):
        require(isinstance(details.get(field), list), "CORE_MAP", "missing reference-range records", "EXECUTION_FAILURE")


def _identity_map(context: Context, details: dict) -> bool:
    return details["coordinate_map"] == [{"sequence_start": 0, "sequence_end": len(context.window.sequence),
            "reference_start0": context.window.start0, "reference_end0": context.window.end0}]


def _reference_align(context: Context, prediction: Prediction, details: dict) -> Prediction:
    """Align only unambiguous per-base predictions; preserve actual sequence identity."""
    _validate_coordinate_map(context, details)
    tracks = []
    for track in prediction.tracks:
        require(track.metadata.get("coordinate_space") == "edited_sequence",
                "COORDINATE_SPACE", "provider must declare edited-sequence track coordinates", "UNSUPPORTED")
        metadata = {**track.metadata, "coordinate_space": "reference", "alignment": "reference_retained",
                    "alignment_policy": ALIGNMENT_POLICY,
                    "fixed_reference_denominator": True}
        if _identity_map(context, details):
            tracks.append(replace(track, metadata=metadata))
            continue
        require(track.bin_size == 1, "INDEL_RESOLUTION", "indel alignment requires explicit per-base predictions", "UNSUPPORTED")
        values = [0.0] * len(context.window.sequence)
        for piece in details["coordinate_map"]:
            if piece["reference_start0"] is None:
                continue
            for source in range(piece["sequence_start"], piece["sequence_end"]):
                target = piece["reference_start0"] + source - piece["sequence_start"] - context.window.start0
                if 0 <= target < len(values):
                    values[target] = track.values[source]
        tracks.append(replace(track, values=tuple(values), metadata=metadata))
    return replace(prediction, tracks=tuple(tracks))


def _track_identity(prediction: Prediction) -> tuple:
    identities = []
    for track in prediction.tracks:
        require(isinstance(track.metadata, dict) and isinstance(track.metadata.get("name"), str)
                and bool(track.metadata["name"]), "TRACK_ID", "provider must identify the exact track", "UNSUPPORTED")
        identities.append((track.output_type, track.metadata["name"], track.bin_size,
                           track.strand, track.tissue, track.gene_id, track.transcript_id))
    return tuple(sorted(identities))


def analyse_haplotype(request: HaplotypeRequest, provider: PredictionProvider, *, core_binary: str | Path | None = None) -> dict:
    """Compute four matched model endpoints and their predeclared interaction."""
    try:
        request.validate()
        preflight_endpoints(request.context, request.endpoints)
        native = assemble_haplotypes(request, core_binary=core_binary)
        capabilities = provider.capabilities(request.context)
        require(isinstance(capabilities, dict), "PROVIDER_CAPABILITIES", "provider capabilities must be explicit", "EXECUTION_FAILURE")
        evidence = capabilities.get("evidence")
        require(evidence in {"MOCK_SYNTHETIC", "REAL_MODEL_PREDICTION"}, "EVIDENCE", "provider evidence missing", "EXECUTION_FAILURE")
        # Imported lazily so native assembly has no dependency on endpoint scoring.
        from .rna_processing import analyse_rna
        scenario_results = {}; aligned_predictions = {}; track_identity = None
        for scenario in SCENARIOS:
            details = native["scenarios"][scenario]
            digest = sequence_sha256(details["sequence"])
            prediction = provider.predict_sequence(request.context, scenario, details["sequence"])
            validate_prediction(request.context, prediction, expected_sequence_sha256=digest)
            require(prediction.scenario == scenario, "MISMATCHED_SCENARIO", "provider scenario differs")
            require(prediction.evidence == evidence, "EVIDENCE", "provider changed evidence class between conditions")
            identity = _track_identity(prediction)
            if track_identity is None:
                track_identity = identity
            require(identity == track_identity, "MISMATCHED_TRACKS", "track identity differs between matched conditions")
            aligned = _reference_align(request.context, prediction, details)
            aligned_predictions[scenario] = aligned
            scenario_results[scenario] = {"sequence_sha256": digest, "sequence_length": len(details["sequence"]),
                "counterfactual": details["counterfactual"], "coordinate_map": details["coordinate_map"],
                "deleted_reference_ranges": details["deleted_reference_ranges"],
                "cropped_reference_ranges": details["cropped_reference_ranges"],
                "cropped_bases": details["cropped_bases"]}
        rna = analyse_rna(request.context, request.endpoints, aligned_predictions)
        return _combine(request, native, capabilities, scenario_results, rna)
    except MolecularError as error:
        return {**error.to_result(), "module": "haplotype"}
    except Exception:
        return {**MolecularError("EXECUTION_FAILURE", "HAPLOTYPE_EXECUTION", "haplotype computation failed; no biological result established").to_result(), "module": "haplotype"}


def _combine(request: HaplotypeRequest, native: dict, capabilities: dict, scenarios: dict, rna: dict) -> dict:
    """Consume the shared RNA scorer's per-endpoint values on declared scales."""
    interactions = []
    for endpoint in request.endpoints:
        row = rna["endpoints"][endpoint.id]
        if row["status"] != "SUCCESS":
            interactions.append({"id": endpoint.id, "status": row["status"], "interaction": None,
                "reason": row.get("reason", row.get("message", "matched endpoint unavailable"))})
            continue
        values = row["values_by_scenario"]
        require(set(values) == set(SCENARIOS), "ENDPOINT_VALUES", "endpoint omitted a matched condition", "UNKNOWN")
        require(all(type(y) in {int, float} and math.isfinite(y) for y in values.values()), "ENDPOINT_VALUES", "endpoint returned nonfinite or missing scalar", "UNKNOWN")
        try:
            interaction = math.fsum((values["AB"], -values["A"], -values["B"], values["REF"]))
        except OverflowError as error:
            raise MolecularError("UNKNOWN", "INTERACTION", "interaction exceeded finite numeric range") from error
        require(math.isfinite(interaction), "INTERACTION", "interaction overflowed", "UNKNOWN")
        deltas = {sid: values[sid]-values["REF"] for sid in ("A", "B", "AB")}
        require(all(math.isfinite(v) for v in deltas.values()), "INTERACTION", "endpoint difference overflowed", "UNKNOWN")
        interactions.append({"id": endpoint.id, "status": "SUCCESS", "values": values,
            "delta_A": deltas["A"], "delta_B": deltas["B"],
            "delta_AB": deltas["AB"], "interaction": interaction,
            "formula": "yAB-yA-yB+yREF", "scale": endpoint.scale,
            "endpoint": asdict(endpoint), "interpretation": "predicted nonadditivity on the declared scale"})
    available = all(row["status"] == "SUCCESS" for row in interactions)
    status = "SUCCESS" if available else rna.get("status", "UNSUPPORTED")
    if not available and status == "SUCCESS":
        status = "UNKNOWN"
    if available and request.phase.kind == "unknown":
        status = "UNKNOWN"
    context = asdict(request.context)
    context["window"].pop("sequence"); context["window"].pop("guard_sequence")
    context["window"].update(sequence_length=len(request.context.window.sequence),
                             guard_length=len(request.context.window.guard_sequence),
                             end0=request.context.window.end0)
    return {"contract_version": CONTRACT_VERSION, "module": "haplotype", "application": "haplotype", "status": status,
        "successful_computation": available, "biological_conclusion_established": False,
        "evidence": capabilities["evidence"], "settings_sha256": request.context.settings_sha256,
        "input_sha256": identity_sha256(request), "native_binary_sha256": native["native_binary_sha256"],
        "native_request_sha256": native["native_request_sha256"],
        "sources": {"reference": request.context.window.source, "reference_sha256": request.context.window.sha256,
                    "annotation": request.context.transcript.source, "annotation_version": request.context.transcript.version},
        "context": context, "phase": asdict(request.phase), "diploid_aggregation": None,
        "sequence_policy": native["coordinate_policy"], "endpoint_alignment": ALIGNMENT_POLICY,
        "capabilities": capabilities, "scenarios": scenarios, "rna_analysis": rna, "interactions": interactions,
        "prediction_only": True}


analyze_haplotype = analyse_haplotype
