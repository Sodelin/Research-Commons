#!/usr/bin/env python3
"""Build the native executable while preserving exact source and tool identities."""
from __future__ import annotations
import datetime
import json
import os
from pathlib import Path
import subprocess
import time
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]

def main():
    compiler_bin = Path(os.environ.get("CONNECTED_LEAN_BIN", "/workspace/toolchains/lean-4.33.1-linux/bin")).resolve()
    assert sha(compiler_bin / "lean") == COMPILER
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/native-build" / stamp
    evidence.mkdir(parents=True)
    inputs = sorted((ROOT / "GParity").glob("*.lean")) + [ROOT / "lakefile.lean", ROOT / "lean-toolchain"]
    before = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    for path in inputs:
        frozen = evidence / "sources" / path.relative_to(ROOT)
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(path.read_bytes())
    env = dict(os.environ, PATH=str(compiler_bin) + os.pathsep + os.environ["PATH"])
    command = [str(compiler_bin / "lake"), "build"]
    start = time.monotonic()
    with (evidence / "stdout.txt").open("wb") as out, (evidence / "stderr.txt").open("wb") as err:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=err)
    after = {str(p.relative_to(ROOT)): sha(p) for p in inputs}
    stable = before == after and sha(compiler_bin / "lean") == COMPILER
    binary = ROOT / ".lake/build/bin/gparity"
    passed = result.returncode == 0 and stable and binary.is_file()
    receipt = {"status": "PASS_NATIVE_BUILD" if passed else "FAILED_ATTEMPT_PRESERVED",
               "command": command, "exit_code": result.returncode, "elapsed_seconds": time.monotonic() - start,
               "source_sha256": before, "source_and_compiler_identity_stable": stable,
               "compiler_sha256": COMPILER, "lake_sha256": sha(compiler_bin / "lake"),
               "stdout_sha256": sha(evidence / "stdout.txt"), "stderr_sha256": sha(evidence / "stderr.txt"),
               "all_sources_fresh_claimed": False, "classification": "Lake build with stable source identities; fresh trust-zero compilation is check_core.py."}
    if passed:
        receipt.update(binary_sha256=sha(binary), binary_path=str(binary))
    save(evidence / "RECEIPT.json", receipt)
    print(json.dumps({"status": receipt["status"], "binary_sha256": receipt.get("binary_sha256"), "evidence": str(evidence)}))
    return 0 if passed else 1

if __name__ == "__main__":
    raise SystemExit(main())
