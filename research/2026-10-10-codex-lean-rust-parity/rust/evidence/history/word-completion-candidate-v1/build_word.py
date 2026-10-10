#!/usr/bin/env python3
"""Build a separately pinned internal word candidate from frozen inputs.

Offline provisioned Rust1.90.0; no accepted runtime is replaced. A successful
build is not typed-provider acceptance or a general source-refinement proof.
Use fresh output and target directories after reporting readiness to root.
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


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_files(records: list[dict]) -> None:
    for entry in records:
        if sha((ROOT / entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("Frozen input changed: " + entry["path"])


def check_binaries(records: list[dict]) -> None:
    for entry in records:
        if sha(Path(entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("Accepted baseline changed: " + entry["path"])


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--target-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--freeze", type=Path, required=True)
    args = parser.parse_args()
    freeze_raw = args.freeze.read_bytes()
    freeze = json.loads(freeze_raw)
    if freeze.get("schema") != "rust_internal_word_source_freeze_v1" or freeze.get("status") != "FROZEN_BEFORE_BUILD":
        raise ValueError("Expected the separately recorded prebuild source freeze")
    check_files(freeze["inputs"])
    check_files(freeze["inherited_providers"])
    check_binaries(freeze["preserved_runtime_inputs"])
    actual = sorted(str(path.relative_to(ROOT)) for path in [HERE / "Cargo.toml", HERE / "Cargo.lock",
        *HERE.glob("src/*.rs"), *HERE.glob("tests/*.rs"), *HERE.glob("examples/*.rs")])
    expected = sorted(entry["path"] for entry in freeze["inputs"] if entry["role"] == "compile_input")
    if actual != expected:
        raise ValueError("Compile input inventory changed after the prebuild freeze")
    runtime = args.runtime.resolve()
    target = args.target_directory.resolve()
    if target.parent != runtime or not target.name.startswith("word-candidate-target-"):
        raise ValueError("Use a new word-candidate-target-* under the provisioned runtime")
    args.output.mkdir(parents=True, exist_ok=False)
    target.mkdir(parents=True, exist_ok=False)
    environment = {"PATH": str(runtime / "toolchain/bin") + os.pathsep + os.defpath,
        "CARGO_HOME": str(runtime / "cargo-home"), "CARGO_TARGET_DIR": str(target),
        "LANG": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1"}
    receipt = {"schema": "rust_internal_word_build_receipt_v1", "status": "FAILED", "commands": [],
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "freeze_path": str(args.freeze), "freeze_sha256": sha(freeze_raw),
        "builder_sha256": sha(Path(__file__).read_bytes()), "frozen_inputs": freeze,
        "network_used_by_this_build": False, "public_runtime_replaced": False,
        "public_word_endpoint": False, "source_admission_claim": False,
        "general_word_refinement_proof_claim": False, "original_typed_provider_acceptance_inferred": False}
    cargo = runtime / "toolchain/bin/cargo"
    commands = [("rustc-version", [runtime / "toolchain/bin/rustc", "--version", "--verbose"]),
        ("cargo-version", [cargo, "--version", "--verbose"]),
        ("tests", [cargo, "test", "--locked", "--offline"]),
        ("release", [cargo, "build", "--release", "--locked", "--offline"])]
    commands.extend((name, [cargo, "build", "--release", "--locked", "--offline", "--example", example])
        for name, example in [("source-population-probe", "source_population_probe"),
            ("source-epoch-probe", "source_epoch_probe"), ("source-boundary-probe", "source_boundary_probe"),
            ("source-word-probe", "source_word_probe")])
    started = time.monotonic()
    try:
        for name, command in commands:
            before = time.monotonic()
            child = subprocess.run(list(map(str, command)), cwd=HERE, env=environment,
                capture_output=True, check=False, timeout=120)
            (args.output / (name + ".stdout")).write_bytes(child.stdout)
            (args.output / (name + ".stderr")).write_bytes(child.stderr)
            receipt["commands"].append({"id": name, "command": list(map(str, command)),
                "process_started": True, "exit_code": child.returncode, "timed_out": False,
                "wall_seconds": time.monotonic() - before,
                "stdout_sha256": sha(child.stdout), "stderr_sha256": sha(child.stderr)})
            if child.returncode:
                raise ValueError("Candidate build command failed: " + name)
            if name == "rustc-version" and b"1159e78c4747b02ef996e55082b704c09b970588" not in child.stdout:
                raise ValueError("Unexpected Rust compiler commit")
        check_files(freeze["inputs"])
        check_files(freeze["inherited_providers"])
        check_binaries(freeze["preserved_runtime_inputs"])
        for name, path in [("binary", target / "release/parity-solver"),
            ("source_population_probe", target / "release/examples/source_population_probe"),
            ("source_epoch_probe", target / "release/examples/source_epoch_probe"),
            ("source_boundary_probe", target / "release/examples/source_boundary_probe"),
            ("source_word_probe", target / "release/examples/source_word_probe")]:
            receipt[name] = str(path)
            receipt[name + "_sha256"] = sha(path.read_bytes())
        receipt.update(status="PASS", compile_input_rehash_stable=True, preserved_runtime_rehash_stable=True,
            probe_scope=freeze.get("probe_scope", "Eight full-view word fixtures and five explicitly unsupported completion fixtures; typed baseline and independent acceptance are separate"))
    except Exception as error:
        receipt["error"] = str(error)
        raise
    finally:
        receipt.update(wall_seconds=time.monotonic() - started,
            ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (args.output / "BUILD-RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "binary", "binary_sha256",
        "source_word_probe", "source_word_probe_sha256"]}))


if __name__ == "__main__":
    main()
