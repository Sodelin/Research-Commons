#!/usr/bin/env python3
"""Preserve actual isolated kernel-run evidence outside ignored build scratch."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    workspace = args.workspace.resolve()
    preparation = json.loads((workspace / "PREPARATION.json").read_bytes())
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
        body = path.read_bytes()
        if target.exists():
            assert target.read_bytes() == body, ("Preserved evidence differs", target)
        else:
            target.write_bytes(body)
        copied.append({"path": str(relative), "bytes": len(body), "sha256": sha(path)})
    receipt = {"status": final["status"], "workspace": str(workspace), "actual_run": str(run),
        "evidence": str(evidence.relative_to(ROOT)), "final_receipt": final,
        "preserved_files": copied, "compiled_artifact_bytes_distributed": False,
        "original_attempts_overwritten": False, "preparation_sha256": sha(workspace / "PREPARATION.json")}
    save(evidence / "PRESERVATION-MANIFEST.json", receipt)
    save(ROOT / "COEFFICIENT-RECOVERY-RESULT.json", receipt)
    print(json.dumps({"status": final["status"], "preserved_files": len(copied),
                      "evidence": receipt["evidence"]}))


if __name__ == "__main__":
    main()
