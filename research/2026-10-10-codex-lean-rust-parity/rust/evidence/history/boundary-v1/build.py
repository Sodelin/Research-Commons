#!/usr/bin/env python3
"""Rebuild with inherited checksum-provisioned Rust1.90.0, offline and locked.

Use coordinator/native_replay.py to create the supplied runtime first; this
script performs no downloads and preserves a new actual build/test receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    runtime = args.runtime.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    environment = {"PATH": str(runtime / "toolchain/bin") + os.pathsep + os.defpath,
                   "CARGO_HOME": str(runtime / "cargo-home"),
                   "CARGO_TARGET_DIR": str(runtime / "parity-target"),
                   "LANG": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1"}
    receipt = {"schema": "rust_parity_build_receipt_v1", "status": "FAILED", "commands": [],
               "network_used_by_this_build": False,
               "provisioning_network_record": str(runtime.parent / "packet/logs/PROVISIONING.json"),
               "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    started = time.monotonic()
    files = sorted([HERE / "Cargo.toml", HERE / "Cargo.lock", *HERE.glob("src/*.rs"),
                    *HERE.glob("tests/*.rs"), *HERE.glob("examples/*.rs")])
    source_manifest = [{"path": str(path.relative_to(ROOT)), "sha256": sha(path.read_bytes())} for path in files]
    inherited = json.loads((HERE / "INHERITED-SOURCES.json").read_text())
    for entry in inherited["files"]:
        if sha((ROOT / entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("Inherited source changed: " + entry["path"])
    receipt.update(owned_compile_sources=source_manifest, inherited_sources=inherited)
    cargo = runtime / "toolchain/bin/cargo"
    commands = [("rustc-version", [runtime / "toolchain/bin/rustc", "--version", "--verbose"]),
                ("cargo-version", [cargo, "--version", "--verbose"]),
                ("tests", [cargo, "test", "--locked", "--offline"]),
                ("release", [cargo, "build", "--release", "--locked", "--offline"]),
                ("source-population-probe", [cargo, "build", "--release", "--locked", "--offline",
                                             "--example", "source_population_probe"])]
    try:
        for name, command in commands:
            before = time.monotonic()
            child = subprocess.run(list(map(str, command)), cwd=HERE, env=environment,
                                   capture_output=True, check=False, timeout=120)
            (args.output / (name + ".stdout")).write_bytes(child.stdout)
            (args.output / (name + ".stderr")).write_bytes(child.stderr)
            receipt["commands"].append({"id": name, "command": list(map(str, command)),
                                        "exit_code": child.returncode, "wall_seconds": time.monotonic() - before,
                                        "stdout_sha256": sha(child.stdout), "stderr_sha256": sha(child.stderr)})
            if child.returncode:
                raise ValueError("Build command failed: " + name)
            if name == "rustc-version" and b"1159e78c4747b02ef996e55082b704c09b970588" not in child.stdout:
                raise ValueError("Unexpected Rust compiler commit")
        binary = runtime / "parity-target/release/parity-solver"
        probe = runtime / "parity-target/release/examples/source_population_probe"
        receipt.update(status="PASS", binary=str(binary), binary_sha256=sha(binary.read_bytes()),
                       source_population_probe=str(probe), source_population_probe_sha256=sha(probe.read_bytes()),
                       source_population_probe_scope="Fixed internal fixtures; no new RC1 operation or typed source admission")
    finally:
        receipt.update(wall_seconds=time.monotonic() - started,
                       ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (args.output / "BUILD-RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": receipt["status"], "binary": receipt["binary"],
                      "binary_sha256": receipt["binary_sha256"]}))


if __name__ == "__main__":
    main()
