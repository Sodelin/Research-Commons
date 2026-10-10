#!/usr/bin/env python3
"""Compare six typed original completion fixtures with the exact reference.

Lean executes an imported, separately kernel-checked completion provider through
the compiled evaluator. Rust executes its private word wrapper; only the six
empty-word, conditional, zero-dimensional rational completion rows are projected
to the direct source fixture format. No native recurrence is used by the oracle.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

import review_completion_controls as controls
import source_word_oracle as ref

DESIGN = Path(__file__).resolve().parent
NAMES = ("completion1", "completion2", "completion3", "completion4",
         "completionCarriedNonminimum", "completionPermutedFour")
REVIEWER_SHA = "61dac01fae9a034870d9bc3471e978da8de98c4d864bb4dc19fc6d281b94d0c8"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def direct_expected(name):
    request = ref.epoch.parse_json((controls.FREEZE / (name + ".request.json")).read_bytes())
    ref.require(request["initial"]["kind"] == "CONDITIONAL" and not request["word"] and
                request["slots"] == 0 and not request["context"]["hybrids"],
                "direct comparison requires the frozen empty-word rational input")
    word, internals = ref.expected_probe(name, request)
    ref.require(word["status"] == "TABLE" and not word["variables"], "direct completion is not rational")
    forms = controls.closed_form(name, word)
    context = {**request["context"], "register": request["initial"]["snapshot"]["register"],
               "start": request["initial"]["snapshot"]}
    rows = []
    for row in word["rows"]:
        terms = row["coefficients"]
        ref.require(len(terms) == 1 and terms[0][0] == [], "direct completion contains a survival coordinate")
        rows.append({"view": row["view"], "witness": row["witness"], "weight": terms[0][1]})
    return {"schema": "source_completion_probe_v1", "fixture": name, "context": context,
            "rows": rows}, word, internals, forms


def check_direct(actual, expected, internals):
    ref.require(type(actual) is dict and set(actual) == set(expected), "direct completion fields differ")
    for key in ("schema", "fixture", "context"):
        ref.require(ref.epoch.exact_json(actual[key]) == ref.epoch.exact_json(expected[key]),
                    "direct completion changed " + key)
    ref.require(type(actual["rows"]) is list, "direct completion row is not a list")
    wanted = {ref.epoch.exact_json(row["view"]): row["weight"] for row in expected["rows"]}
    seen, total = {}, Fraction(0)
    for row in actual["rows"]:
        ref.require(type(row) is dict and set(row) == {"view", "witness", "weight"},
                    "direct completion row has unknown or missing fields")
        value = row["weight"]
        ref.require(type(value) is str, "completion weight is not a rational string")
        weight = Fraction(value)
        ref.require(weight > 0 and ref.epoch.qwire(weight) == value, "completion weight is not positive canonical p/q")
        raw = row["witness"]
        current = {**expected["context"], "global_labels": list(range(len(expected["context"]["local_samples"]))),
                   "register": raw["register"], "start": raw}
        state = ref.epoch.validate_context(current)
        code = ref.Code(state, tuple(raw["register"]))
        ref.require(code in internals["literal"], "direct completion witness is outside exact positive literal support")
        view = code.view(expected["context"])
        key = ref.epoch.exact_json(row["view"])
        ref.require(key == ref.epoch.exact_json(view), "direct completion witness does not realize its full view")
        ref.require(len(state.roots) == 1 and state.roots[0][2] == ("A", expected["context"]["root"]),
                    "direct completion witness is not one ancestral-root genealogy")
        ref.require(key not in seen and wanted.get(key) == value, "duplicate destination or incorrect completion weight")
        seen[key], total = value, total + weight
    ref.require(seen == wanted and total == 1, "direct completion omitted destinations or changed mass")
    return {"status": "PASS", "full_view_rows": len(seen), "exact_total_weight": "1/1"}


def checker_controls():
    expected, _, internal, _ = direct_expected("completion4")
    check_direct(expected, expected, internal)
    bad = copy.deepcopy(expected)
    # Preserve total mass while changing one balanced and one pectinate weight.
    balanced = next(row for row in bad["rows"] if controls.balanced_four(row["view"]))
    pectinate = next(row for row in bad["rows"] if not controls.balanced_four(row["view"]))
    balanced["weight"] = ref.epoch.qwire(Fraction(balanced["weight"]) + Fraction(1, 288))
    pectinate["weight"] = ref.epoch.qwire(Fraction(pectinate["weight"]) - Fraction(1, 288))
    candidates = [("balanced mass-preserving wrong weights", bad)]
    for label, mutate in [
        ("noncanonical rational", lambda x: x["rows"][0].update(weight="2/144")),
        ("wrong original register", lambda x: x["rows"][0]["witness"]["register"].__setitem__(0, False)),
        ("duplicate/missing full destination", lambda x: x["rows"].__setitem__(0, copy.deepcopy(x["rows"][1]))),
        ("unknown top-level field", lambda x: x.update(source_admission_verified=True))]:
        bad = copy.deepcopy(expected)
        mutate(bad)
        candidates.append((label, bad))
    rejected = []
    for label, bad in candidates:
        try:
            check_direct(bad, expected, internal)
        except (ValueError, TypeError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise ValueError("direct checker accepted " + label)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-word-probe", type=Path)
    parser.add_argument("--lean-execution-config", type=Path)
    parser.add_argument("--lean-artifact", type=Path, action="append", default=[])
    parser.add_argument("--fixture", action="append")
    parser.add_argument("--timeout", type=int, default=30, choices=range(1, 61))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    ref.require(digest(DESIGN / "review_completion_controls.py") == REVIEWER_SHA and
                digest(DESIGN / "source_word_oracle.py") == controls.ORACLE_SHA and
                digest(controls.FREEZE / "INVENTORY.json") == controls.INVENTORY_SHA and
                digest(DESIGN / "WORD-COMPLETION-EXTENSION-20261010T1300Z.md") == controls.CONTRACT_SHA,
                "completion reference or input freeze changed")
    names = args.fixture or list(NAMES)
    ref.require(len(set(names)) == len(names) and set(names) <= set(NAMES), "unknown or repeated completion fixture")
    args.output.mkdir(parents=True, exist_ok=False)
    paths = [Path(__file__).resolve(), DESIGN / "review_completion_controls.py",
             DESIGN / "source_word_oracle.py", DESIGN / "boundary_oracle.py", DESIGN / "epoch_oracle.py",
             DESIGN / "population_oracle.py", DESIGN / "chart_check.py", DESIGN / "certificate_check.py",
             DESIGN / "WORD-COMPLETION-EXTENSION-20261010T1300Z.md", controls.FREEZE / "INVENTORY.json",
             *[controls.FREEZE / (name + ".request.json") for name in names],
             *[path.resolve() for path in args.lean_artifact]]
    commands, modes, environments, directories = {}, {}, {}, {}
    config = None
    if args.rust_word_probe:
        path = args.rust_word_probe.resolve()
        paths.append(path)
        commands["rust"] = [str(path)]
        modes["rust"] = "private_native_word_wrapper_projected_to_direct_rational_row"
    if args.lean_execution_config:
        config_path = args.lean_execution_config.resolve()
        config = ref.epoch.parse_json(config_path.read_bytes())
        compiler, driver = Path(config["compiler_path"]), Path(config["driver_path"])
        ref.require(digest(compiler) == config["compiler_sha256"] and digest(driver) == config["driver_sha256"],
                    "completion evaluator configuration pins differ")
        prefix = config["command_prefix"]
        ref.require(prefix[0] == str(compiler) and prefix[-2:] == ["--run", str(driver)] and
                    all(flag in prefix for flag in ["-j1", "-t0", "-Ddebug.skipKernelTC=false"]),
                    "unexpected bounded completion evaluator command")
        ref.require(set(names) <= set(config["fixtures"]), "completion fixture is absent from typed execution context")
        paths.extend([config_path, compiler, driver])
        staged = args.output / "LEAN-DRIVER.lean"
        staged.write_bytes(driver.read_bytes())
        (args.output / "LEAN-EXECUTION-CONFIG.json").write_bytes(config_path.read_bytes())
        commands["lean"] = [*prefix[:-1], str(staged.resolve())]
        environments["lean"] = dict(os.environ, LEAN_PATH=config["lean_path"])
        directories["lean"] = config["workdir"]
        modes["lean"] = "compiled_lean_evaluator_not_standalone_elf"
    before = {str(path): digest(path) for path in paths}
    for path in paths:
        if path.parent == DESIGN:
            (args.output / path.name).write_bytes(path.read_bytes())
    invalid_controls = checker_controls()
    cases = []
    for name in names:
        expected, word, internal, form = direct_expected(name)
        (args.output / (name + ".expected.json")).write_text(json.dumps(expected, indent=2) + "\n")
        results, errors = {}, []
        for language, prefix in commands.items():
            command = [*prefix, name]
            result = {"command": command, "execution_mode": modes[language], "process_started": False,
                      "exit_code": None, "timed_out": False}
            stdout, stderr, started = b"", b"", time.monotonic()
            try:
                process = subprocess.run(command, capture_output=True, timeout=args.timeout,
                                         cwd=directories.get(language), env=environments.get(language))
                stdout, stderr = process.stdout, process.stderr
                result.update(process_started=True, exit_code=process.returncode)
                ref.require(process.returncode == 0 and max(len(stdout), len(stderr)) <= 4 * 1024 * 1024,
                            "completion fixture process failed or exceeded frame cap")
                actual = ref.epoch.parse_json(stdout)
                if language == "rust":
                    ref.check_probe(actual, word, internal)
                    actual = {"schema": expected["schema"], "fixture": name, "context": expected["context"],
                              "rows": [{"view": row["view"], "witness": row["witness"],
                                        "weight": row["coefficients"][0][1]} for row in actual["rows"]]}
                result["coefficient_review"] = check_direct(actual, expected, internal)
            except subprocess.TimeoutExpired as error:
                stdout, stderr = error.stdout or b"", error.stderr or b""
                result.update(process_started=True, timed_out=True)
                errors.append(language + ": bounded execution timeout")
            except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
                errors.append(language + ": " + str(error))
            (args.output / (name + "." + language + ".stdout")).write_bytes(stdout)
            (args.output / (name + "." + language + ".stderr")).write_bytes(stderr)
            result.update(elapsed_seconds=time.monotonic() - started,
                          stdout_sha256=hashlib.sha256(stdout).hexdigest(),
                          stderr_sha256=hashlib.sha256(stderr).hexdigest())
            results[language] = result
        cases.append({"fixture": name, "full_view_rows": len(expected["rows"]),
                      "closed_form": form, "runs": results, "errors": errors, "pass": not errors})
        print(name, "PASS" if not errors else "FAIL", len(expected["rows"]), flush=True)
    after = {str(path): digest(path) for path in paths}
    answer = {"schema": "original_completion_compiled_fixture_review_v1",
              "pass": all(case["pass"] for case in cases) and before == after,
              "claim": "FINITE_IMPORTED_ORIGINAL_EVALUATOR_COEFFICIENT_REVIEW" if config else
                       "FINITE_NATIVE_RATIONAL_COMPLETION_REVIEW" if commands else "ORACLE_SELF_CHECK_ONLY",
              "execution_modes": modes, "languages_executed": list(commands),
              "cases_total": len(cases), "cases_passed": sum(case["pass"] for case in cases),
              "full_view_rows_total": sum(case["full_view_rows"] for case in cases),
              "cases": cases, "invalid_table_controls_rejected": invalid_controls,
              "oracle_algorithm": "Full ordered half-rate generator zero spectral projector",
              "pins_before": before, "pins_after": after,
              "separately_authenticated_kernel_evidence": config.get("kernel_evidence") if config else None,
              "kernel_qualification": "Separate integration receipts must authenticate the exact completion theorem, fixture context and imported/native runtime closure.",
              "Lean_standalone_ELF_claim": False, "general_native_refinement_claim": False,
              "source_admission_verified": False, "chosen_epoch_table_identity_claim": False}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print(json.dumps({key: answer[key] for key in ["pass", "cases_total", "cases_passed", "full_view_rows_total", "claim"]}), flush=True)
    return 0 if answer["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
