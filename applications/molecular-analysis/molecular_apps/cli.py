"""CLI calls the same services a GUI would call. No network by default."""
from __future__ import annotations

import argparse
from dataclasses import asdict, replace
import json
import sys

from .contracts import (CONTRACT_VERSION, HaplotypeRequest, MolecularError, Phase,
                        Variant, context_from_dict, endpoint_from_dict, parse_json,
                        require, sequence_sha256, validate_prediction, preflight_endpoints)
from .providers import AlphaGenomeProvider, SyntheticProvider

EXIT_CODES = {"SUCCESS": 0, "INVALID_INPUT": 2, "UNKNOWN": 3, "UNSUPPORTED": 4,
              "RESOURCE_LIMIT": 5, "EXECUTION_FAILURE": 6}


def execute(mode: str, request: dict, provider, *, core_binary=None) -> dict:
    """Library entry point shared with a future GUI; no shell invocation."""
    require(mode in {"haplotype", "rna"}, "MODE", "unsupported application")
    allowed = {"context", "endpoints", "variants", "phase"} if mode == "haplotype" else {"context", "endpoints", "sequence_scenarios"}
    require(set(request) == allowed, "SCHEMA", "unexpected or missing application fields")
    context = context_from_dict(request["context"])
    require(isinstance(request["endpoints"], list) and bool(request["endpoints"]), "SCHEMA", "endpoints must be nonempty array")
    endpoints = tuple(endpoint_from_dict(e, context) for e in request["endpoints"])
    require(len({e.id for e in endpoints}) == len(endpoints), "ENDPOINTS", "endpoint ids must be unique")
    preflight_endpoints(context, endpoints)
    if mode == "haplotype":
        require(isinstance(request["variants"], list) and len(request["variants"]) == 2, "SCHEMA", "exactly two variants required")
        variants = []
        for v in request["variants"]:
            require(isinstance(v, dict) and set(v) == set(Variant.__dataclass_fields__), "SCHEMA", "unexpected or missing variant fields")
            variants.append(Variant(**v))
        p = request["phase"]
        require(isinstance(p, dict) and set(p) == {"kind", "evidence"}, "SCHEMA", "unexpected or missing phase fields")
        from .haplotype import analyse_haplotype
        return analyse_haplotype(HaplotypeRequest(context, tuple(variants), Phase(**p), endpoints), provider, core_binary=core_binary)
    sequences = request["sequence_scenarios"]
    require(isinstance(sequences, dict) and "REF" in sequences and 1 <= len(sequences) <= 4, "SCHEMA", "RNA input requires REF and at most four named sequences")
    require(sequences["REF"] == context.window.sequence, "REFERENCE_MISMATCH", "RNA REF scenario differs from authenticated reference")
    provider.capabilities(context)
    predictions = {}
    for name, sequence in sequences.items():
        require(isinstance(name, str) and name and not any(ord(c) < 32 for c in name), "SCENARIO", "scenario name must be explicit text")
        require(isinstance(sequence, str) and len(sequence) == len(context.window.sequence) and set(sequence) <= set("ACGTN"), "MISMATCHED_WINDOW", "RNA sequences must match fixed window; use haplotype module for indel mapping")
        prediction = provider.predict_sequence(context, name, sequence)
        validate_prediction(context, prediction, expected_sequence_sha256=sequence_sha256(sequence))
        # This RNA entry point declares equal-length positional scenarios.
        # Indels use the native haplotype module and its explicit coordinate map.
        tracks = tuple(replace(track, metadata={**track.metadata, "coordinate_space": "reference",
                                               "alignment": "reference_retained",
                                               "alignment_assumption": "equal-length positional RNA scenario; no indel inference"})
                       for track in prediction.tracks)
        predictions[name] = replace(prediction, tracks=tracks)
    from .rna_processing import analyse_rna
    result = analyse_rna(context, endpoints, predictions)
    result.update({"contract_version": CONTRACT_VERSION, "application": "rna_processing",
                   "context": asdict(context), "settings_sha256": context.settings_sha256,
                   "input_sequence_sha256": {k: sequence_sha256(v) for k, v in sequences.items()},
                   "endpoint_specs": [asdict(e) for e in endpoints], "biological_conclusion_established": False})
    # Keep context identity/provenance, but do not repeat raw DNA in output.
    result["context"]["window"].pop("sequence")
    result["context"]["window"].pop("guard_sequence")
    return result


def _read_json(path: str) -> dict:
    try:
        if path == "-":
            data = sys.stdin.buffer.read(8 * 2**20 + 1)
        else:
            with open(path, "rb") as source:
                data = source.read(8 * 2**20 + 1)
        require(len(data) <= 8 * 2**20, "INPUT_SIZE", "request exceeds 8MiB", "RESOURCE_LIMIT")
        return parse_json(data.decode("utf-8"))
    except (OSError, UnicodeError) as error:
        raise MolecularError("INVALID_INPUT", "INPUT_FILE", "cannot read a UTF-8 JSON input") from error


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description="Experimental molecular applications; mock evidence is synthetic.")
    parser.add_argument("mode", choices=["haplotype", "rna", "access-check"])
    parser.add_argument("input", nargs="?")
    parser.add_argument("--provider", choices=["mock", "alphagenome"], default="mock")
    parser.add_argument("--core-binary")
    parser.add_argument("--access-authorized", action="store_true", help="operator assertion that API access and applicable terms are authorized")
    parser.add_argument("--track-names", help="JSON file mapping requested output types to exact SDK experiment names")
    args = parser.parse_args(argv)
    try:
        if args.mode == "access-check":
            blockers = AlphaGenomeProvider().blockers()
            result = {"contract_version": CONTRACT_VERSION, "status": "UNSUPPORTED" if blockers else "UNKNOWN",
                      "code": "LIVE_ACCESS_PENDING", "blockers": blockers, "live_smoke_test": "PENDING",
                      "successful_computation": False, "biological_conclusion_established": False}
        else:
            require(args.input is not None, "INPUT_FILE", "provide a JSON request path or - for stdin")
            tracks = _read_json(args.track_names) if args.track_names else None
            if tracks is not None:
                require(all(isinstance(k, str) and isinstance(v, str) for k, v in tracks.items()), "TRACK_SELECTION", "track selection must map strings to strings")
            provider = SyntheticProvider() if args.provider == "mock" else AlphaGenomeProvider(access_authorized=args.access_authorized, track_names=tracks)
            result = execute(args.mode, _read_json(args.input), provider, core_binary=args.core_binary)
        print(json.dumps(result, sort_keys=True, separators=(",", ":"), allow_nan=False))
        return EXIT_CODES.get(result.get("status"), 6)
    except MolecularError as error:
        print(json.dumps(error.to_result(), sort_keys=True))
        return EXIT_CODES[error.status]
    except Exception:
        # Preserve traceback to stderr for local debugging; never render it as a biological result.
        import traceback
        traceback.print_exc(file=sys.stderr)
        print(json.dumps(MolecularError("EXECUTION_FAILURE", "APPLICATION", "application failed; see local stderr").to_result(), sort_keys=True))
        return 6


if __name__ == "__main__":
    raise SystemExit(main())
