#!/usr/bin/env python3
"""Evaluate the audited finite Lean checker against saved Rust certificates.

Contributor: Codex / lean_integration_successor, 2026-10-10.
The private native producer is never invoked. Literal finite tables are checked
against the frozen request/result bytes before one bounded compiled Lean run.
This is a finite comparison, not native parser or elimination refinement.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT.parent


def definition(source: str, name: str) -> str:
    match = re.search(r"^def " + re.escape(name) + r"\b[\s\S]*? :=\s*([\s\S]*?)(?=\n(?:/--|def |#|end )|\Z)", source, re.M)
    assert match, ("Missing literal definition", name)
    return re.sub(r"\s+", " ", match.group(1)).strip()


def literal_table(source: str, name: str, size: int, *, index: bool = False):
    body = definition(source, name)
    if size == 0:
        assert body == "Fin.elim0", (name, body)
        return []

    def value(text: str):
        if index:
            match = re.fullmatch(r"⟨(\d+), by decide⟩", text)
            assert match, (name, text)
            return int(match.group(1))
        match = re.fullmatch(r"\(\((\d+) : ℚ\) / (\d+)\)", text)
        if match:
            return Fraction(int(match.group(1)), int(match.group(2)))
        match = re.fullmatch(r"\((\d+) : ℚ\)", text)
        assert match, (name, text)
        return Fraction(int(match.group(1)))

    branches = []
    while body.startswith("if "):
        match = re.fullmatch(r"if a\.val = (\d+) then (.*?) else (.*)", body)
        assert match, (name, body)
        branches.append((int(match.group(1)), value(match.group(2))))
        body = match.group(3)
    assert len({a for a, _ in branches}) == len(branches)
    default = value(body)
    return [next((v for a, v in branches if a == i), default) for i in range(size)]


def moments(M, z, weights):
    return [sum((a * sum((x ** k for k in range(math.comb(j, 2))), Fraction())
                 for x, a in zip(z, weights)), Fraction()) for j in range(3, M + 1)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-execution-config", type=Path, required=True)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    assert 1 <= args.timeout <= 60
    output = args.output.resolve()
    assert not output.exists()
    output.mkdir(parents=True)
    evaluator_count = 0
    receipt = {"status": "PREFLIGHT_PENDING", "native_producer_processes": 0,
               "lean_evaluator_processes": 0,
               "execution_mode": "compiled_lean_evaluator_not_standalone_elf"}
    try:
        config = json.loads(args.lean_execution_config.read_bytes())
        capture = json.loads(args.capture.read_bytes())
        pinned = {}

        def pin(path, expected=None):
            path = Path(path).resolve(strict=True)
            actual = sha(path)
            assert expected is None or actual == expected, path
            pinned[str(path)] = actual
            return path

        pin(args.lean_execution_config)
        pin(args.capture)
        assert config["status"] == "PREPARED_CHECKED_CONTEXT_EVALUATOR_EXECUTION_PENDING"
        assert config["execution_mode"] == "compiled_lean_evaluator_not_standalone_elf"
        compiler = pin(config["compiler_path"], COMPILER)
        driver = pin(config["driver_path"], config["driver_sha256"])
        assert driver.read_text() == "import G6RationalCompressionCertificateFixtureMain\n"
        assert config["command_prefix"] == [str(compiler), "-j1", "-t0", "-M4096",
                                            "-Ddebug.skipKernelTC=false", "--run", str(driver)]
        assert config["additional_native_provider_boundary"] == []
        execution_evidence = ROOT / config["evidence"]
        artifacts = json.loads((execution_evidence / "ACTUAL-IMPORTED-ARTIFACTS.json").read_bytes())
        for row in artifacts:
            p = pin(row["path"], row["sha256"])
            assert p.stat().st_size == row["bytes"]
        native = json.loads((execution_evidence / "NATIVE-RUNTIME-PINS.json").read_bytes())
        for path, row in native["libraries"].items():
            pin(path, row["sha256"])
        kernel = ROOT / config["kernel_evidence"]
        pin(kernel / "PRESERVATION-MANIFEST.json", config["kernel_preservation_manifest_sha256"])
        source_text = None
        origins = []
        for row in capture["source_pins"]:
            p = pin(PACKET / row["path"], row["sha256"])
            assert config["source_pins"][p.stem] == row["sha256"]
            origins.append(row)
            if p.stem == "G6RationalCompressionCertificateFixture":
                source_text = p.read_text()
        assert source_text is not None

        def origin(row):
            p = pin(PACKET / row["path"], row["sha256"])
            assert p.is_relative_to(PACKET)
            relative = p.relative_to(PACKET)
            destination = output / "saved-origin" / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, destination)
            assert sha(destination) == row["sha256"]
            origins.append(row)
            return p

        origin(capture["origin_receipt"])
        origin(capture["origin_identity"])
        expected = []
        references = []
        for case in capture["cases"]:
            name = case["name"]
            req = json.loads(origin(case["request"]).read_bytes())
            result = json.loads(origin(case["result"]).read_bytes())
            saved_check = json.loads(origin(case["native_checker"]).read_bytes())
            z = [Fraction(row["z"]) for row in req["atoms"]]
            alpha = [Fraction(row["alpha"]) for row in req["atoms"]]
            atom = [row["input_index"] for row in result["output_atoms"]]
            beta = [Fraction(row["beta"]) for row in result["output_atoms"]]
            M, n, r = req["M"], len(z), len(atom)
            assert (M, n, r) == (case["M"], case["n"], case["r"])
            assert z == list(map(Fraction, case["z"]))
            assert alpha == list(map(Fraction, case["alpha"]))
            assert atom == case["atom"] and beta == list(map(Fraction, case["beta"]))
            for field, values in [("z", z), ("alpha", alpha), ("atom", atom), ("beta", beta)]:
                assert literal_table(source_text, name + "_" + field, r if field in ("atom", "beta") else n,
                                     index=field == "atom") == values, (name, field)
            assert definition(source_text, name + "_check") == (
                f"checkCompression {M} {name}_z {name}_alpha {name}_atom {name}_beta")
            assert all(type(a) is int and 0 <= a < n for a in atom)
            mass = sum(beta, Fraction()) == sum(alpha, Fraction())
            other = (M >= 2 and all(0 < x < 1 for x in z) and all(a >= 0 for a in alpha)
                     and r <= M - 1 and all(b > 0 for b in beta))
            input_moments, output_moments = moments(M, z, alpha), moments(M, [z[a] for a in atom], beta)
            valid = other and mass and input_moments == output_moments
            assert valid == case["expected"] == saved_check["certificate_valid"]
            expected.append((name, valid))
            references.append({"name": name, "M": M, "n": n, "r": r, "expected": valid,
                               "mass_preserved": mass, "other_premises": other,
                               "input_tail_moments": list(map(str, input_moments)),
                               "output_tail_moments": list(map(str, output_moments))})
            if name == "sameMassWrongTail":
                assert M == 3 and other and mass and input_moments != output_moments
        assert len(expected) == 6
        expected += [("wrongTailMass", True), ("wrongTailOtherPremises", True), ("wrongTailMomentDiffers", True)]
        assert config["fixtures"] == [name for name, _ in expected]
        save(output / "REFERENCE-RESULTS.json", references)
        save(output / "SOURCE-INPUT-BINDINGS.json", {"origins": origins, "capture_sha256": sha(args.capture),
             "finite_literal_table_values_match_saved_requests_and_results": True,
             "scope": "Static check of this exact finite literal source grammar, not a general native parser refinement."})
        shutil.copyfile(args.capture, output / "FINITE-INPUT-CAPTURE.json")
        shutil.copyfile(args.lean_execution_config, output / "LEAN-EXECUTION-CONFIG.json")
        shutil.copyfile(Path(__file__), output / "EVALUATOR-REVIEWER.py")
        save(output / "PRE-EVALUATION-PINS.json", pinned)
        started = time.monotonic()
        env = dict(os.environ, LEAN_PATH=config["lean_path"])
        evaluator_count = 1
        try:
            process = subprocess.run(config["command_prefix"], cwd=config["workdir"], env=env,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=args.timeout)
            stdout, stderr, returncode = process.stdout, process.stderr, process.returncode
        except subprocess.TimeoutExpired as error:
            stdout, stderr, returncode = error.stdout or b"", error.stderr or b"", None
        (output / "lean.stdout").write_bytes(stdout)
        (output / "lean.stderr").write_bytes(stderr)
        save(output / "LEAN-PROCESS-RESULT.json", {"command": config["command_prefix"], "exit_code": returncode,
             "seconds": time.monotonic() - started, "timeout_seconds": args.timeout,
             "stdout_sha256": sha(output / "lean.stdout"), "stderr_sha256": sha(output / "lean.stderr")})
        assert returncode == 0 and stderr == b"", (returncode, stderr.decode(errors="replace"))
        actual = []
        for line in stdout.decode().splitlines():
            match = re.fullmatch(r"([A-Za-z0-9]+): (true|false) \(expected (true|false)\)", line)
            assert match, line
            name, observed, literal_expected = match.groups()
            actual.append((name, observed == "true"))
            assert observed == literal_expected
        assert actual == expected, (actual, expected)
        for path, digest in pinned.items():
            assert sha(Path(path)) == digest, ("Post-evaluation identity drift", path)
        receipt.update(status="PASS_ACTUAL_COMPILED_FINITE_CHECKS_AGAINST_SAVED_RUST_CERTIFICATES",
                       lean_evaluator_processes=evaluator_count, checks=len(expected), certificate_cases=6,
                       extra_wrong_tail_controls=3, cases=[{"name": n, "actual": v} for n, v in actual],
                       execution_config_sha256=sha(args.lean_execution_config), capture_sha256=sha(args.capture),
                       kernel_evidence=config["kernel_evidence"], all_pre_post_artifact_identities_stable=True,
                       compiler_sha256=COMPILER, private_native_binary_sha256=capture["private_native_binary_sha256"],
                       universal_native_parser_or_elimination_refinement_claimed=False,
                       source_positive_factor_or_arbitrary_real_extraction_claimed=False,
                       old_native_tests_reexecuted=False)
    except Exception as error:
        receipt.update(status="FAILED_RETAINED" if evaluator_count else "PREFLIGHT_BLOCKED_NO_EVALUATOR",
                       lean_evaluator_processes=evaluator_count, error=str(error), error_type=type(error).__name__)
    save(output / "RECEIPT.json", receipt)
    manifest = [{"path": str(p.relative_to(output)), "sha256": sha(p), "bytes": p.stat().st_size}
                for p in sorted(output.rglob("*")) if p.is_file()]
    save(output / "PRESERVATION-MANIFEST.json", {"files": manifest,
         "original_kernel_and_native_artifacts_modified": False})
    print(json.dumps({"status": receipt["status"], "checks": receipt.get("checks", 0),
                      "lean_evaluator_processes": evaluator_count, "native_producer_processes": 0,
                      "preserved_files": len(manifest), "output": str(output)}))
    if not receipt["status"].startswith("PASS_"):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
