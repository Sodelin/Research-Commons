"""Offline matched-context molecular fixture; no service or credential access.

Reuses the published RNA contracts and deterministic provider. This is an
optional software demonstration, never an ancestry observation or assay.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import html
import json
from pathlib import Path
import sys
from types import ModuleType
import uuid

COMMONS = Path(__file__).resolve().parents[2]
INHERITED = COMMONS / "applications/molecular-analysis"
PINS = {
    "molecular_apps/contracts.py": "32d6b69ce48412de21e5160aac287415500c79a95aa306b29a6ea90ce3d71e67",
    "molecular_apps/providers.py": "a1494dd5de42dd77afed22396c6b45f41c8ebf1eaab596a819f95f7ad4befe01",
    "molecular_apps/rna_processing.py": "f0f46b37cefca4d232eb01f37be1c3aa0d5cec84da635e3b603c238711c2d68a",
    "molecular_apps/cli.py": "cddeec13db9194f5d3f59842e8e2531de3bd7fa6d295fad356d63199138f3449",
    "examples/synthetic-rna-processing.json": "96b0f8c616d6e7f8fcd993aaba30bd5898356361960f760a19f8b2a4774b9625",
}


def _captured_sources():
    captured = {}
    for relative, digest in PINS.items():
        path = INHERITED / relative
        if path.is_symlink() or path.stat().st_size > 2**20:
            raise ValueError("inherited fixture source is symlinked or exceeds size limit")
        raw = path.read_bytes()
        if hashlib.sha256(raw).hexdigest() != digest:
            raise ValueError("inherited fixture source identity changed: " + relative)
        captured[relative] = raw
    return captured


def _load(captured):
    # Execute each authenticated single buffer; do not consult cached bytecode.
    name = "_rc_offline_molecular_" + uuid.uuid4().hex
    package = ModuleType(name)
    package.__path__ = []
    sys.modules[name] = package
    for short in ("contracts", "providers", "rna_processing", "cli"):
        relative = "molecular_apps/" + short + ".py"
        module = ModuleType(name + "." + short)
        module.__package__ = name
        module.__file__ = str(INHERITED / relative)
        sys.modules[module.__name__] = module
        setattr(package, short, module)
        exec(compile(captured[relative], module.__file__, "exec", dont_inherit=True), module.__dict__)
    return package


def matched_request(captured=None):
    """Equal-length hypothetical cis substitutions using inherited context."""
    captured = _captured_sources() if captured is None else captured
    request = json.loads(captured["examples/synthetic-rna-processing.json"])
    reference = request["context"]["window"]["sequence"]
    alternate_a = request["sequence_scenarios"]["ALT"]
    if reference[8:10] != "AC" or alternate_a[8:10] != "GC":
        raise ValueError("inherited substitution anchor changed")
    alternate_b = reference[:9] + "G" + reference[10:]
    combined = alternate_a[:9] + "G" + alternate_a[10:]
    request["sequence_scenarios"] = {"REF": reference, "A": alternate_a,
                                     "B": alternate_b, "AB": combined}
    return request


def compute_offline(request=None):
    """Return fresh synthetic outputs, with separately typed RNA endpoints."""
    captured = _captured_sources()
    package = _load(captured)
    request = matched_request(captured) if request is None else request
    if set(request.get("sequence_scenarios", {})) != {"REF", "A", "B", "AB"}:
        raise ValueError("offline interaction demonstration requires REF/A/B/AB")
    result = package.cli.execute("rna", request, package.providers.SyntheticProvider())
    interactions = {}
    for identifier, endpoint in result["endpoints"].items():
        if endpoint["status"] == "SUCCESS":
            values = endpoint["values_by_scenario"]
            interactions[identifier] = {
                "value": values["AB"] - values["A"] - values["B"] + values["REF"],
                "formula": "yAB-yA-yB+yREF", "scale": endpoint["scale"],
                "family": endpoint["family"], "evidence": "MOCK_SYNTHETIC",
                "interpretation": "deterministic fixture arithmetic; not measured or model-validated biology",
            }
    result.update({
        "schema": "practical-solver-offline-molecular-v1",
        "execution_status": "FRESH_OFFLINE_FIXTURE_COMPUTATION",
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "evidence_origin": "inherited public synthetic RNA fixture plus explicitly derived equal-length scenarios",
        "live_api_calls": 0, "credentials_accessed": False,
        "provider": "deterministic_mock", "prediction_only": True,
        "whole_application_lean_verified": False, "ancestry_observation_admitted": False,
        "matched_scenarios": ["REF", "A", "B", "AB"],
        "phase": {"kind": "hypothetical_cis", "evidence": "software fixture; no specimen phase inference"},
        "derived_scenarios": {"A": "inherited ALT: chr1:108 A>G (0-based)",
                              "B": "new synthetic chr1:109 C>G (0-based)",
                              "AB": "both substitutions in the same reference window"},
        "interactions": interactions, "executed_inherited_source_sha256": PINS,
        "unsupported_endpoints": ["typed splice-junction adapter", "validated PSI method", "official multisplit PAS scoring"],
        "limitations": [
            "Expression is a declared transcript-exon coverage proxy from RNA_SEQ.",
            "Splice usage is a separate declared SPLICE_SITE_USAGE aggregate.",
            "PAS is a derived two-annotation-window RNA coverage ratio, not direct PAS output or isoform usage.",
            "The deterministic synthetic provider is not AlphaGenome inference or experimental validation.",
            "Human-labelled synthetic context does not supply plant or hemlock ancestry observations.",
        ],
    })
    return result, request


def run_offline(output_dir: Path | str):
    """Create exclusive fresh export directory and return the JSON result."""
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=False)
    result, request = compute_offline()
    (output / "REQUEST.json").write_text(json.dumps(request, indent=2, sort_keys=True) + "\n")
    (output / "RESULT.json").write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False) + "\n")
    report = "# Optional offline molecular demonstration\n\n"
    report += "Execution: **FRESH_OFFLINE_FIXTURE_COMPUTATION**. Evidence: **MOCK_SYNTHETIC**. Live calls: **0**.\n\n"
    report += "Matched REF/A/B/AB sequences use one reference window, tissue, transcript, model and endpoint definition.\n\n"
    report += "| Endpoint | Family | Scale | Synthetic interaction |\n|---|---|---|---|\n"
    for key, row in result["interactions"].items():
        report += f"| {key} | {row['family']} | {row['scale']} | {row['value']:.12g} |\n"
    report += "\nInteraction = yAB − yA − yB + yREF on each declared scale.\n\n"
    report += "\n".join("- " + item for item in result["limitations"]) + "\n\n"
    report += "Exported REQUEST.json and RESULT.json retain settings, sequence digests and per-scenario values. Current live-access setup and terms review remain separate; this command reads no credential and creates no SDK client.\n"
    (output / "REPORT.md").write_text(report)
    (output / "REPORT.html").write_text("<!doctype html><meta charset=utf-8><title>Offline molecular fixture</title><pre>" + html.escape(report) + "</pre>")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description="Optional offline molecular fixture; zero live calls")
    parser.add_argument("--output", type=Path, required=True, help="new export directory")
    args = parser.parse_args(argv)
    try:
        result = run_offline(args.output)
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "INVALID_INPUT", "reason": str(error)}))
        return 2
    print(json.dumps({"status": result["status"], "evidence": result["evidence"], "live_api_calls": 0,
                      "output": str(args.output)}))
    return 0 if result["status"] == "SUCCESS" else 3


if __name__ == "__main__":
    raise SystemExit(main())
