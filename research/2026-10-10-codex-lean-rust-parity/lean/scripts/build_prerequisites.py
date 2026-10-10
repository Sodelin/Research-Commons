#!/usr/bin/env python3
"""Build the pinned Mathlib import roots for the public modular graph.

This uses an existing checkout; it neither installs tools nor selects a new
revision. Lake may reuse its own dependency artifacts. The formal runner later
pins the exact imported companion bundles and checks every owned Lean module.
"""
from __future__ import annotations
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
from check_core import COMPILER, bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--target", default="all", help="all or a named DEPENDENCY-GRAPH target")
    parser.add_argument("--list", action="store_true", help="List the required roots without building")
    args = parser.parse_args()
    graph = json.loads((ROOT / "DEPENDENCY-GRAPH.json").read_bytes())
    targets = list(graph["targets"].values()) if args.target == "all" else [graph["targets"][args.target]]
    modules = {m for target in targets for m in target["modules"]}
    roots = sorted({i for target in targets for entry in target["modules"].values()
                    for i in entry["imports"] if i not in modules and i.startswith("Mathlib.")})
    if args.list:
        print("\n".join(roots))
        return 0
    assert 1 <= args.threads <= 16
    compiler_bin = Path(os.environ["CONNECTED_LEAN_BIN"]).resolve()
    mathlib = Path(os.environ["CONNECTED_MATHLIB"]).resolve()
    assert sha(compiler_bin / "lean") == COMPILER
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip() == MATHLIB
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    evidence = ROOT / "evidence/prerequisites" / stamp
    evidence.mkdir(parents=True)
    save(evidence / "ROOTS.json", roots)
    env = dict(os.environ, PATH=str(compiler_bin) + os.pathsep + os.environ["PATH"],
               LEAN_NUM_THREADS=str(args.threads))
    command = [str(compiler_bin / "lake"), "build"] + roots
    start = time.monotonic()
    with (evidence / "stdout.txt").open("wb") as out, (evidence / "stderr.txt").open("wb") as err:
        result = subprocess.run(command, cwd=mathlib, env=env, stdout=out, stderr=err)
    final_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=mathlib, text=True).strip()
    identity_stable = final_commit == MATHLIB and sha(compiler_bin / "lean") == COMPILER
    artifacts = {}
    for module in roots:
        path = mathlib / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if path.is_file():
            artifacts[module] = bundle(path)
    passed = result.returncode == 0 and identity_stable and len(artifacts) == len(roots)
    receipt = {"status": "PASS_PINNED_EXTERNAL_ROOTS" if passed else "FAILED_ATTEMPT_PRESERVED",
               "command": command, "exit_code": result.returncode, "threads": args.threads,
               "elapsed_seconds": time.monotonic() - start, "compiler_sha256": COMPILER,
               "mathlib_commit": MATHLIB, "identity_stable": identity_stable,
               "graph_sha256": sha(ROOT / "DEPENDENCY-GRAPH.json"), "target": args.target,
               "root_artifacts": artifacts, "stdout_sha256": sha(evidence / "stdout.txt"),
               "stderr_sha256": sha(evidence / "stderr.txt"),
               "all_external_modules_fresh_claimed": False,
               "classification": "Lake source-build or exact dependency artifact reuse; owned project compilation is separate."}
    save(evidence / "RECEIPT.json", receipt)
    print(json.dumps({"status": receipt["status"], "roots": len(roots), "evidence": str(evidence)}))
    return 0 if passed else 1

if __name__ == "__main__":
    raise SystemExit(main())
