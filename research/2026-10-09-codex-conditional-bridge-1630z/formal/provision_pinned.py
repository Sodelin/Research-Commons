#!/usr/bin/env python3
"""Clean-machine scratch provisioning of the exact accepted Lean/Mathlib pins.

No global installation, lake update, cache server or remote workflow is used.
Existing repositories at a different revision are refused instead of rewritten.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ARCHIVE_URL = "https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst"
ARCHIVE_SHA = "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235"
COMPILER_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
MATHLIB_REV = "0df444a360eaa60ab8c11dca51a86af692955474"
IMPORTS = [
    "Mathlib.Data.Rat.Floor", "Mathlib.Data.Real.Basic",
    "Mathlib.Algebra.Order.BigOperators.Group.Finset",
    "Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset",
    "Mathlib.Tactic.Linarith", "Mathlib.Tactic.FieldSimp",
    "Mathlib.Tactic.NormNum", "Mathlib.Tactic.Positivity",
]


def sha(path):
    hasher = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--skip-build", action="store_true", help="Verify/reuse pins without any compiler build")
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    repo = Path(__file__).resolve().parents[3]
    assert not scratch.is_relative_to(repo), "Use scratch outside tracked Commons"
    scratch.mkdir(parents=True, exist_ok=True)
    args.evidence.mkdir(parents=True, exist_ok=False)
    records = []

    def run(argv, cwd=scratch, seconds=120, env=None):
        label = str(len(records) + 1).zfill(3)
        start = time.monotonic()
        try:
            result = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, timeout=seconds)
            code, out, err = result.returncode, result.stdout, result.stderr
        except subprocess.TimeoutExpired as exc:
            code, out, err = 124, exc.stdout or b"", exc.stderr or b""
        (args.evidence / (label + ".stdout")).write_bytes(out)
        (args.evidence / (label + ".stderr")).write_bytes(err)
        records.append({"argv": argv, "cwd": str(cwd), "cap_seconds": seconds,
                        "exit_code": code, "seconds": time.monotonic() - start,
                        "stdout_sha256": hashlib.sha256(out).hexdigest(),
                        "stderr_sha256": hashlib.sha256(err).hexdigest()})
        (args.evidence / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
        if code:
            raise RuntimeError(f"Command failed, preserved as {label}: {argv}")
        return out

    archive = scratch / "lean.tar.zst"
    if not archive.exists():
        run(["curl", "--fail", "--location", "--retry", "0", "--connect-timeout", "15",
             "--max-time", "180", ARCHIVE_URL, "--output", str(archive)], seconds=190)
    assert sha(archive) == ARCHIVE_SHA, "Compiler archive hash mismatch"
    binary_dir = scratch / "lean-4.33.1-linux/bin"
    lean = binary_dir / "lean"
    if not lean.exists():
        run(["tar", "--zstd", "-xf", str(archive), "-C", str(scratch)], seconds=120)
    assert sha(lean) == COMPILER_SHA, "Compiler executable hash mismatch"
    version = run([str(lean), "--version"]).decode().strip()

    def exact_repository(path, url, revision):
        if (path / ".git").exists():
            actual = run(["git", "-C", str(path), "rev-parse", "HEAD"]).decode().strip()
            assert actual == revision, ("Refusing existing revision drift", path, actual, revision)
            return
        assert not path.exists(), ("Refusing existing nonrepository directory", path)
        run(["git", "init", "--quiet", str(path)])
        run(["git", "-C", str(path), "remote", "add", "origin", url])
        run(["git", "-C", str(path), "fetch", "--quiet", "--no-tags", "--depth=1", "origin", revision])
        run(["git", "-C", str(path), "checkout", "--quiet", "--detach", revision])

    mathlib = scratch / "mathlib"
    exact_repository(mathlib, "https://github.com/leanprover-community/mathlib4.git", MATHLIB_REV)
    manifest = run(["git", "-C", str(mathlib), "show", "HEAD:lake-manifest.json"])
    assert (mathlib / "lake-manifest.json").read_bytes() == manifest, "Dependency manifest drift"
    dependencies = json.loads(manifest)["packages"]
    for dep in dependencies:
        exact_repository(mathlib / ".lake/packages" / dep["name"], dep["url"], dep["rev"])
    if not args.skip_build:
        env = dict(os.environ, PATH=str(binary_dir) + ":" + os.environ["PATH"],
                   LEAN_NUM_THREADS="4", MATHLIB_CACHE_DIR=str(scratch / "cache"))
        run([str(binary_dir / "lake"), "--no-cache", "build", *IMPORTS], cwd=mathlib, seconds=600, env=env)
    receipt = {"status": "PINS_VERIFIED_BUILD_SKIPPED" if args.skip_build else "PINNED_IMPORTS_BUILT",
               "compiler_archive_sha256": ARCHIVE_SHA, "compiler_sha256": COMPILER_SHA,
               "compiler_version": version, "mathlib_revision": MATHLIB_REV,
               "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
               "dependency_pins": {d["name"]: d["rev"] for d in dependencies},
               "lean_bin": str(binary_dir), "mathlib": str(mathlib), "commands": records}
    (args.evidence / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(receipt["status"], flush=True)


if __name__ == "__main__":
    main()
