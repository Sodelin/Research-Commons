#!/usr/bin/env python3
"""Build a separate internal epoch candidate after original population acceptance.

Offline checksum-provisioned Rust1.90.0; no public runtime replacement. The
recorded acceptance inputs are task dependencies, not signatures or general
source-refinement certificates. Use a new output and target directory.
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", type=Path, required=True)
    parser.add_argument("--target-directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--population-receipt", type=Path, required=True)
    parser.add_argument("--support-receipt", type=Path, required=True)
    args = parser.parse_args()
    population_raw = args.population_receipt.read_bytes()
    population = json.loads(population_raw)
    if not (population.get("pass") is True and population.get("cases_passed") == 8
            and population.get("cases_total") == 8
            and {"lean", "rust"}.issubset(population.get("languages_executed", []))
            and len(population.get("cases", [])) == 8
            and all(case.get("pass") is True and all(
                case.get("process_runs", {}).get(language, {}).get("process_started") is True
                and case["process_runs"][language].get("exit_code") == 0
                and case["process_runs"][language].get("timed_out") is False
                for language in ("lean", "rust")) for case in population["cases"])):
        raise ValueError("Original Lean/Rust eight-case population acceptance is required")
    support_raw = args.support_receipt.read_bytes()
    support = json.loads(support_raw)
    if support.get("status") != "PASS" or support.get("target") != "extraction/original-population-fixture":
        raise ValueError("Original population/support context kernel-and-owned-audit acceptance is required")
    runtime = args.runtime.resolve()
    target = args.target_directory.resolve()
    if target == runtime / "parity-target" or target in (runtime, HERE, ROOT):
        raise ValueError("Candidate target must be separate from the accepted public runtime")
    args.output.mkdir(parents=True, exist_ok=False)
    target.mkdir(parents=True, exist_ok=False)
    builder_raw = Path(__file__).read_bytes()
    sources = sorted([HERE / "Cargo.toml", HERE / "Cargo.lock", *HERE.glob("src/*.rs"),
                      *HERE.glob("tests/*.rs"), *HERE.glob("examples/*.rs")])
    source_pins = [{"path": str(path.relative_to(ROOT)), "sha256": sha(path.read_bytes())} for path in sources]
    inherited = json.loads((HERE / "INHERITED-SOURCES.json").read_bytes())
    for entry in inherited["files"]:
        if sha((ROOT / entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("Inherited source changed: " + entry["path"])
    environment = {"PATH": str(runtime / "toolchain/bin") + os.pathsep + os.defpath,
                   "CARGO_HOME": str(runtime / "cargo-home"), "CARGO_TARGET_DIR": str(target),
                   "LANG": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1"}
    receipt = {"schema": "rust_internal_epoch_build_receipt_v1", "status": "FAILED", "commands": [],
               "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "network_used_by_this_build": False, "builder_sha256": sha(builder_raw),
               "owned_compile_sources": source_pins, "inherited_sources": inherited,
               "dependency_acceptance_inputs": [
                   {"path": str(args.population_receipt), "sha256": sha(population_raw)},
                   {"path": str(args.support_receipt), "sha256": sha(support_raw)}],
               "population_execution_modes": population.get("execution_modes"),
               "public_runtime_replaced": False, "public_epoch_endpoint": False,
               "source_admission_claim": False, "general_epoch_refinement_proof_claim": False}
    started = time.monotonic()
    cargo = runtime / "toolchain/bin/cargo"
    commands = [("rustc-version", [runtime / "toolchain/bin/rustc", "--version", "--verbose"]),
                ("cargo-version", [cargo, "--version", "--verbose"]),
                ("tests", [cargo, "test", "--locked", "--offline"]),
                ("release", [cargo, "build", "--release", "--locked", "--offline"]),
                ("source-population-probe", [cargo, "build", "--release", "--locked", "--offline",
                                             "--example", "source_population_probe"]),
                ("source-epoch-probe", [cargo, "build", "--release", "--locked", "--offline",
                                        "--example", "source_epoch_probe"])]
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
        for entry in source_pins:
            if sha((ROOT / entry["path"]).read_bytes()) != entry["sha256"]:
                raise ValueError("Compile input changed during candidate build")
        for name, path in [("binary", target / "release/parity-solver"),
                           ("source_population_probe", target / "release/examples/source_population_probe"),
                           ("source_epoch_probe", target / "release/examples/source_epoch_probe")]:
            receipt[name] = str(path)
            receipt[name + "_sha256"] = sha(path.read_bytes())
        receipt.update(status="PASS", compile_input_rehash_stable=True,
                       probe_scope="Fixed internal entered-state fixtures; no public endpoint or original source admission")
    finally:
        receipt.update(wall_seconds=time.monotonic() - started,
                       ended_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        (args.output / "BUILD-RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": receipt["status"], "binary": receipt["binary"],
                      "binary_sha256": receipt["binary_sha256"],
                      "source_epoch_probe": receipt["source_epoch_probe"],
                      "source_epoch_probe_sha256": receipt["source_epoch_probe_sha256"]}))


if __name__ == "__main__":
    main()
