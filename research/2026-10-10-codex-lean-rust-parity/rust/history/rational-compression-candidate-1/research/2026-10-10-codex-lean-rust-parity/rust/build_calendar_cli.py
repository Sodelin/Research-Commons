#!/usr/bin/env python3
"""Offline build of the additive general-calendar frontend from frozen inputs.

The accepted core, private probes and historical executable guards stay fixed.
Downloaded third-party crate archives are separately checksum-checked against
the new package's Cargo.lock. This receipt is build evidence, not a proof that
all supplied calendars satisfy the original scientific source class.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def check_files(records):
    for entry in records:
        path = Path(entry["path"])
        if not path.is_absolute():
            path = ROOT / path
        if sha(path.read_bytes()) != entry["sha256"]:
            raise ValueError("Frozen input changed: " + str(path))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--cargo-home", required=True, type=Path)
    parser.add_argument("--target-directory", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--artifact-directory", required=True, type=Path)
    parser.add_argument("--freeze", required=True, type=Path)
    args = parser.parse_args()
    freeze_raw = args.freeze.read_bytes()
    freeze = json.loads(freeze_raw)
    if freeze.get("schema") != "rust_calendar_frontend_source_freeze_v1" or freeze.get("status") != "FROZEN_BEFORE_BUILD":
        raise ValueError("Expected the separate general-calendar frontend freeze")
    for key in ("inputs", "accepted_source_guards", "inherited_provider_guards", "accepted_binary_guards", "third_party_archives"):
        check_files(freeze[key])
    package = HERE / "calendar-cli"
    actual = sorted(str(path.relative_to(ROOT)) for path in [package / "Cargo.toml", package / "Cargo.lock",
        *package.glob("src/*.rs"), *package.glob("tests/*.rs")])
    expected = sorted(entry["path"] for entry in freeze["inputs"] if entry["role"] == "compile_input")
    if actual != expected:
        raise ValueError("Frontend compile input inventory changed after freeze")
    runtime = args.runtime.resolve()
    target = args.target_directory.absolute()
    cargo_home = args.cargo_home.absolute()
    if target.parent != Path("/tmp") or cargo_home.parent != Path("/tmp"):
        raise ValueError("Use independent /tmp target and Cargo-home directories")
    args.output.mkdir(parents=True, exist_ok=False)
    args.artifact_directory.mkdir(parents=True, exist_ok=False)
    target.mkdir(parents=True, exist_ok=False)
    environment = {"PATH": str(runtime / "toolchain/bin") + os.pathsep + os.defpath,
        "CARGO_HOME": str(cargo_home), "CARGO_TARGET_DIR": str(target), "LANG": "C.UTF-8",
        "PYTHONDONTWRITEBYTECODE": "1"}
    receipt = {"schema": "rust_calendar_frontend_build_receipt_v1", "status": "FAILED", "commands": [],
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "freeze_path": str(args.freeze), "freeze_sha256": sha(freeze_raw), "frozen_inputs": freeze,
        "builder_sha256": sha(Path(__file__).read_bytes()), "network_used_by_build": False,
        "accepted_public_runtime_replaced": False, "source_admission_verified": False,
        "full_solver_verified": False, "third_party_claim": "Cargo.lock and downloaded archive checksums verified; no universal third-party proof."}
    cargo = runtime / "toolchain/bin/cargo"
    commands = [("rustc-version", [runtime / "toolchain/bin/rustc", "--version", "--verbose"]),
        ("cargo-version", [cargo, "--version", "--verbose"]),
        ("tests", [cargo, "test", "--locked", "--offline"]),
        ("release", [cargo, "build", "--release", "--locked", "--offline"])]
    started = time.monotonic()
    try:
        for name, command in commands:
            before = time.monotonic()
            child = subprocess.run(list(map(str, command)), cwd=package, env=environment,
                capture_output=True, check=False, timeout=120)
            (args.output / (name + ".stdout")).write_bytes(child.stdout)
            (args.output / (name + ".stderr")).write_bytes(child.stderr)
            receipt["commands"].append({"id": name, "command": list(map(str, command)),
                "process_started": True, "exit_code": child.returncode, "timed_out": False,
                "wall_seconds": time.monotonic() - before, "stdout_sha256": sha(child.stdout),
                "stderr_sha256": sha(child.stderr)})
            if child.returncode:
                raise ValueError("Frontend build command failed: " + name)
            if name == "rustc-version" and b"1159e78c4747b02ef996e55082b704c09b970588" not in child.stdout:
                raise ValueError("Unexpected compiler commit")
        for key in ("inputs", "accepted_source_guards", "inherited_provider_guards", "accepted_binary_guards", "third_party_archives"):
            check_files(freeze[key])
        built = target / "release/calendar-solver"
        artifact = args.artifact_directory / "calendar-solver"
        shutil.copyfile(built, artifact)
        artifact.chmod(0o700)
        receipt.update(status="PASS", binary=str(artifact), binary_sha256=sha(artifact.read_bytes()),
            target_binary=str(built), compile_input_rehash_stable=True, accepted_source_rehash_stable=True,
            accepted_runtime_rehash_stable=True)
    except Exception as error:
        receipt["error"] = str(error)
        raise
    finally:
        receipt.update(wall_seconds=time.monotonic() - started,
            ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (args.output / "BUILD-RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: receipt[key] for key in ("status", "binary", "binary_sha256")}))


if __name__ == "__main__":
    main()
