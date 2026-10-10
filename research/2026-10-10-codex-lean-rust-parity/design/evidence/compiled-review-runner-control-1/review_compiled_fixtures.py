#!/usr/bin/env python3
"""Compare actual imported Lean fixture execution and Rust against exact oracles.

This keeps the frozen oracle versions untouched. Imported closure acceptance is
supplied by integration's separate kernel receipt. Lean --run is explicitly a
compiled evaluator execution, not a standalone extracted ELF.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

import boundary_oracle
import epoch_oracle
from population_oracle import require

DESIGN = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args):
    module = epoch_oracle if args.family == "epoch" else boundary_oracle
    all_fixtures = module.fixtures()
    names = args.fixture or list(all_fixtures)
    require(len(set(names)) == len(names) and all(name in all_fixtures for name in names),
            "unknown or duplicate fixture selection")
    output = args.output.resolve()
    require(not output.exists(), "compiled fixture review output exists")
    output.mkdir(parents=True)
    sources = [Path(__file__).resolve(), DESIGN/"epoch_oracle.py", DESIGN/"population_oracle.py"]
    if args.family == "boundary":
        sources.append(DESIGN/"boundary_oracle.py")
    for path in sources:
        (output/path.name).write_bytes(path.read_bytes())
    observed = [*sources, *[p.resolve() for p in args.lean_artifact]]
    probes, commands, modes, environments, directories = {}, {}, {}, {}, {}
    for language, path in (("rust", args.rust_probe), ("lean", args.lean_probe)):
        if path:
            probes[language] = path.resolve()
            commands[language] = [str(probes[language])]
            modes[language] = "standalone_executable"
    config = None
    if args.lean_execution_config:
        require(not args.lean_probe, "choose compiled evaluator or standalone Lean fixture")
        config_path = args.lean_execution_config.resolve()
        config = epoch_oracle.parse_json(config_path.read_bytes())
        compiler, driver = Path(config["compiler_path"]), Path(config["driver_path"])
        require(digest(compiler) == config["compiler_sha256"], "Lean compiler differs from execution configuration")
        require(digest(driver) == config["driver_sha256"], "Lean driver differs from execution configuration")
        prefix = config["command_prefix"]
        require(prefix[0] == str(compiler) and prefix[-2:] == ["--run", str(driver)],
                "unexpected bounded evaluator prefix")
        require("-Ddebug.skipKernelTC=false" in prefix and "-j1" in prefix and "-t0" in prefix,
                "evaluator prefix omits recorded kernel/process flags")
        allowed = set(config.get("fixtures", names))
        require(set(names) <= allowed, "fixture absent from original-provider execution configuration")
        staged_driver = output/"LEAN-DRIVER.lean"
        staged_driver.write_bytes(driver.read_bytes())
        (output/"LEAN-EXECUTION-CONFIG.json").write_bytes(config_path.read_bytes())
        observed.extend([config_path, driver])
        probes["lean"] = compiler.resolve()
        commands["lean"] = [*prefix[:-1], str(staged_driver)]
        modes["lean"] = "compiled_lean_evaluator_not_standalone_elf"
        environments["lean"] = dict(os.environ, LEAN_PATH=config["lean_path"])
        directories["lean"] = config["workdir"]
    before = {language: digest(path) for language, path in probes.items()}
    input_before = {str(path): digest(path) for path in observed}
    cases = []
    expected_controls = {}
    for name in names:
        fixture = all_fixtures[name]
        expected, literal, unranked = (module.expected_probe(name, fixture) if args.family == "epoch"
                                       else module.expected_probe(name, *fixture))
        expected_controls[name] = expected
        (output/(name+".expected.json")).write_text(json.dumps(expected, indent=2, sort_keys=True)+"\n")
        (output/(name+".unranked.json")).write_text(json.dumps(unranked, indent=2, sort_keys=True)+"\n")
        results, errors = {}, []
        for language in probes:
            command = [*commands[language], name]
            result = {"command": command, "execution_mode": modes[language],
                      "process_started": False, "exit_code": None, "timed_out": False}
            started = time.monotonic()
            stdout, stderr = b"", b""
            try:
                process = subprocess.run(command, capture_output=True, timeout=args.timeout,
                                         cwd=directories.get(language), env=environments.get(language))
                stdout, stderr = process.stdout, process.stderr
                result.update(process_started=True, exit_code=process.returncode)
                require(process.returncode == 0, language+" fixture process failed")
                module.check_probe(epoch_oracle.parse_json(stdout), expected, literal, unranked)
            except subprocess.TimeoutExpired as error:
                result.update(process_started=True, timed_out=True)
                stdout, stderr = error.stdout or b"", error.stderr or b""
                errors.append(language+": bounded execution timeout")
            except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
                errors.append(language+": "+str(error))
            (output/(name+"."+language+".stdout")).write_bytes(stdout)
            (output/(name+"."+language+".stderr")).write_bytes(stderr)
            result.update(elapsed_seconds=time.monotonic()-started,
                          stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                          stderr_sha256=hashlib.sha256(stderr).hexdigest())
            results[language] = result
        cases.append({"fixture": name, "literal_support": len(literal),
                      "selected_views": len(expected["rows"]), "unranked_views": len(unranked),
                      "runs": results, "errors": errors, "pass": not errors})
    controls = (boundary_oracle.asymmetric_controls(expected_controls)
                if args.family == "boundary" and set(expected_controls) == set(all_fixtures) else {})
    after = {language: digest(path) for language, path in probes.items()}
    input_after = {str(path): digest(path) for path in observed}
    receipt = {"schema": "compiled_original_fixture_oracle_review_v1", "family": args.family,
               "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "languages_executed": list(probes), "execution_modes": modes,
               "binary_pins_before": before, "binary_pins_after": after,
               "observed_input_pins_before": input_before, "observed_input_pins_after": input_after,
               "lean_import_path": config["lean_path"] if config else None,
               "lean_workdir": config["workdir"] if config else None,
               "separately_authenticated_kernel_evidence": config.get("kernel_evidence") if config else None,
               "kernel_qualification": "Imported artifact closure and executable-refinement theorem status must be authenticated by the separate integration receipt; these file observations do not establish it.",
               "source_admission_claim": False, "general_Rust_refinement_claim": False,
               "Lean_standalone_ELF_claim": bool(args.lean_probe) and probes["lean"].read_bytes()[:4] == b"\x7fELF",
               "oracle_algorithm": ("Single full mixed ordered-half-rate generator spectral projectors"
                                    if args.family == "epoch" else "Whole-Copy unused-bit exact marginalization"),
               "all_fixture_names": list(all_fixtures), "fixtures_executed": names,
               "fixtures_not_executed": [name for name in all_fixtures if name not in names],
               "controls": controls, "cases": cases, "cases_total": len(cases),
               "cases_passed": sum(case["pass"] for case in cases),
               "pass": all(case["pass"] for case in cases) and before == after and input_before == input_after,
               "claim": "ORACLE_SELF_CHECK_ONLY" if not probes else "FINITE_ORIGINAL_FIXTURE_FULL_COEFFICIENT_REVIEW"}
    (output/"RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True)+"\n")
    print(json.dumps({key: receipt[key] for key in ("family", "claim", "pass", "cases_total", "cases_passed")}))
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=("epoch", "boundary"), required=True)
    parser.add_argument("--rust-probe", type=Path)
    lean = parser.add_mutually_exclusive_group()
    lean.add_argument("--lean-probe", type=Path)
    lean.add_argument("--lean-execution-config", type=Path)
    parser.add_argument("--lean-artifact", type=Path, action="append", default=[])
    parser.add_argument("--fixture", action="append")
    parser.add_argument("--timeout", type=int, default=30, choices=range(1, 61))
    parser.add_argument("--output", type=Path, required=True)
    raise SystemExit(run(parser.parse_args()))
