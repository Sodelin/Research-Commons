#!/usr/bin/env python3
"""Preserve actual isolated kernel-run evidence outside ignored build scratch."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from check_core import save, sha
from evidence_distribution import distribute_file

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--run", type=Path, help="Explicit completed run, instead of the mutable latest-run pointer.")
    parser.add_argument("--result-file", default="COEFFICIENT-RECOVERY-RESULT.json",
                        help="Packet-local result summary filename; historical evidence remains unchanged.")
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    preparation = json.loads((workspace / "PREPARATION.json").read_bytes())
    if args.run:
        run = args.run.resolve()
        final = json.loads((run / "FINAL-RECEIPT.json").read_bytes())
    else:
        final = json.loads((workspace / ".build/LATEST-RUN.json").read_bytes())
        run = Path(final["run"])
    assert run.is_relative_to(workspace)
    evidence = Path(preparation["evidence"]) / ("run-" + run.name)
    evidence.mkdir(parents=True, exist_ok=True)
    copied = []
    for path in sorted(run.rglob("*")):
        if not path.is_file() or path.suffix in {".olean", ".ilean", ".ir", ".private", ".server"}:
            continue
        if any(part == "objects" for part in path.relative_to(run).parts):
            continue
        # The complete namespace overlay is represented by its explicit JSON
        # inventory and actual import bindings, not repeated external binaries.
        if path.is_symlink():
            continue
        relative = path.relative_to(run)
        target = evidence / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            body = path.read_bytes()
            assert target.read_bytes() == body, ("Preserved evidence differs", target)
            copied.append({"path": str(relative), "bytes": len(body), "sha256": sha(path)})
        else:
            copied.append(distribute_file(path, evidence, relative,
                force_gzip=path.name.startswith("NATIVE-LOADER.") or path.name == "AUDIT-RESULT.json"))
    distributions = [row for row in copied if row.get("encoding") == "gzip"]
    save(evidence / "COMPRESSED-DISTRIBUTIONS.json", {
        "status": "PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION", "distributions": distributions,
        "original_run_unchanged": True,
        "restore_command": "python3 scripts/restore_distributed_evidence.py MANIFEST --output DESTINATION"})
    receipt = {"status": final["status"], "workspace": str(workspace), "actual_run": str(run),
        "evidence": str(evidence.relative_to(ROOT)), "final_receipt": final,
        "preserved_files": copied, "compiled_artifact_bytes_distributed": False,
        "original_attempts_overwritten": False, "preparation_sha256": sha(workspace / "PREPARATION.json")}
    receipt["compressed_distributions_manifest_sha256"] = sha(evidence / "COMPRESSED-DISTRIBUTIONS.json")
    save(evidence / "PRESERVATION-MANIFEST.json", receipt)
    result_file = ROOT / args.result_file
    assert result_file.parent == ROOT and result_file.suffix == ".json"
    save(result_file, receipt)
    print(json.dumps({"status": final["status"], "preserved_files": len(copied),
                      "evidence": receipt["evidence"]}))


if __name__ == "__main__":
    main()
