#!/usr/bin/env python3
"""Compare nine typed original-word fixtures with the independent exact reference.

The direct Lean envelope retains every selected-view coefficient and a literal
range witness. It has no native work counters. Rust's full private envelope is
checked first, then projected to the direct coefficient envelope. Separate Lean
kernel receipts must authenticate the original providers and extraction context.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

import source_word_oracle as ref

DESIGN = Path(__file__).resolve().parent
ORACLE_SHA = "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102"
CONTRACT_SHA = "dabc36aef7265cef2efeac982b6f191540eaf12f809045bce75e6e5161952458"
NAMES = ("emptyConditionalWord", "emptyNaturalWord", "emptyNaturalCommonWord",
         "conditionalCommonFalseWord", "conditionalCommonTrueWord", "repeatedIntervalSlot",
         "carriedOutsideWord", "parallelCommonFinite", "parallelIndependentFinite")
HYBRID_NAMES = {"parallelCommonFinite", "parallelIndependentFinite"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def origin(name):
    ref.require(name in NAMES, "unknown original-word fixture")
    folder = "word-hybrid-fixture-freeze-1" if name in HYBRID_NAMES else "word-fixture-freeze-1"
    return DESIGN / "evidence" / folder / (name + ".request.json")


def direct_expected(name):
    request = ref.epoch.parse_json(origin(name).read_bytes())
    ref.require(request["terminal"] == "FULL_VIEW", "direct fixture includes a completion stage")
    word, internal = ref.expected_probe(name, request)
    ref.require(word["status"] == "TABLE", "frozen direct-word reference exhausted its limits")
    answer = {"schema": "source_original_word_coefficients_v1", "fixture": name,
              "request": request, "variables": word["variables"], "rows": word["rows"]}
    return answer, word, internal


def project_native(actual):
    return {"schema": "source_original_word_coefficients_v1", "fixture": actual["fixture"],
            "request": actual["request"], "variables": actual["variables"], "rows": actual["rows"]}


def check_direct(actual, expected, internal):
    ref.require(type(actual) is dict and set(actual) == set(expected),
                "direct word has unknown or missing fields")
    for key in ("schema", "fixture", "request", "variables"):
        ref.require(ref.epoch.exact_json(actual[key]) == ref.epoch.exact_json(expected[key]),
                    "direct word changed " + key)
    ref.require(type(actual["rows"]) is list, "direct word rows are not a list")
    wanted = {ref.epoch.exact_json(row["view"]): ref.epoch.exact_json(row["coefficients"])
              for row in expected["rows"]}
    seen, rows = {}, []
    original = expected["request"]["context"]
    for row in actual["rows"]:
        ref.require(type(row) is dict and set(row) == {"view", "witness", "coefficients"},
                    "direct word row fields differ")
        raw = row["witness"]
        ref.require(type(raw) is dict and type(raw.get("register")) is list,
                    "direct word lacks a literal register witness")
        current = {**original, "global_labels": list(range(len(original["local_samples"]))),
                   "register": raw["register"], "start": raw}
        state = ref.epoch.validate_context(current)
        code = ref.Code(state, tuple(raw["register"]))
        ref.require(code in internal["literal"], "direct word witness is outside independently reached literal support")
        key = ref.epoch.exact_json(row["view"])
        ref.require(key == ref.epoch.exact_json(code.view(original)),
                    "direct word witness does not realize its complete selected view")
        value = ref.epoch.exact_json(row["coefficients"])
        ref.require(key not in seen and wanted.get(key) == value,
                    "direct word duplicate destination or wrong canonical coefficient")
        seen[key] = value
        rows.append(row)
    ref.require(seen == wanted, "direct word omitted or added a selected destination")
    # These readers retain the original full register and original populations.
    ref.require(ref.unranked(expected["request"], rows) ==
                ref.unranked(expected["request"], expected["rows"]),
                "direct word full-register unordered pushforward differs")
    return {"status": "PASS", "full_view_rows": len(rows), "literal_support_states": len(internal["literal"]),
            "terms": sum(len(row["coefficients"]) for row in rows),
            "Lean_native_work_counters_inferred": False}


def checker_controls():
    base, _, internal = direct_expected("parallelIndependentFinite")
    check_direct(base, base, internal)
    candidates = []
    for label, mutate in [
        ("unknown native work field", lambda x: x.update(work={})),
        ("original gamma bank aliased", lambda x: x["variables"][-1].__setitem__(1, 1)),
        ("stored original register changed", lambda x: x["rows"][0]["witness"]["register"].__setitem__(3, not x["rows"][0]["witness"]["register"][3])),
        ("duplicate full selected destination", lambda x: x["rows"].append(copy.deepcopy(x["rows"][0]))),
        ("full destination omitted", lambda x: x["rows"].pop()),
        ("coefficient changed", lambda x: x["rows"][0]["coefficients"][0].__setitem__(1, "7/11")),
        ("boolean exponent masquerading as integer", lambda x: x["rows"][0]["coefficients"][0][0].__setitem__(0, False)),
        ("COMMON substituted for INDEPENDENT", lambda x: x["request"]["common"].__setitem__(0, True))]:
        bad = copy.deepcopy(base)
        mutate(bad)
        candidates.append((label, bad))
    rejected = []
    for label, bad in candidates:
        try:
            check_direct(bad, base, internal)
        except (ValueError, TypeError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise ValueError("direct word checker accepted " + label)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-word-probe", type=Path)
    parser.add_argument("--lean-execution-config", type=Path)
    parser.add_argument("--lean-artifact", type=Path, action="append", default=[])
    parser.add_argument("--fixture", action="append")
    parser.add_argument("--timeout", type=int, default=30, choices=range(1, 61))
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    ref.require(digest(DESIGN / "source_word_oracle.py") == ORACLE_SHA and
                digest(DESIGN / "WORD-REFINEMENT.md") == CONTRACT_SHA,
                "frozen original-word reference or contract changed")
    names = args.fixture or list(NAMES)
    ref.require(len(names) == len(set(names)) and set(names) <= set(NAMES), "repeated or unknown word fixture")
    args.output.mkdir(parents=True, exist_ok=False)
    paths = [Path(__file__).resolve(), DESIGN / "source_word_oracle.py", DESIGN / "boundary_oracle.py",
             DESIGN / "epoch_oracle.py", DESIGN / "population_oracle.py", DESIGN / "chart_check.py",
             DESIGN / "certificate_check.py", DESIGN / "WORD-REFINEMENT.md",
             *[origin(name) for name in names], *[path.resolve() for path in args.lean_artifact]]
    commands, modes, environments, directories = {}, {}, {}, {}
    config = None
    if args.rust_word_probe:
        path = args.rust_word_probe.resolve()
        paths.append(path)
        commands["rust"] = [str(path)]
        modes["rust"] = "private_native_word_envelope_projected_to_direct_coefficient_rows"
    if args.lean_execution_config:
        config_path = args.lean_execution_config.resolve()
        config = ref.epoch.parse_json(config_path.read_bytes())
        compiler, driver = Path(config["compiler_path"]), Path(config["driver_path"])
        ref.require(digest(compiler) == config["compiler_sha256"] and digest(driver) == config["driver_sha256"],
                    "word evaluator configuration pins differ")
        prefix = config["command_prefix"]
        ref.require(prefix[0] == str(compiler) and prefix[-2:] == ["--run", str(driver)] and
                    all(flag in prefix for flag in ["-j1", "-t0", "-Ddebug.skipKernelTC=false"]),
                    "unexpected bounded word evaluator command")
        ref.require(set(names) <= set(config["fixtures"]), "word fixture missing from typed execution context")
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
        expected, word, internal = direct_expected(name)
        check_direct(expected, expected, internal)
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
                            "word fixture process failed or exceeded frame cap")
                actual = ref.epoch.parse_json(stdout)
                if language == "rust":
                    ref.check_probe(actual, word, internal)
                    actual = project_native(actual)
                result["coefficient_review"] = check_direct(actual, expected, internal)
            except subprocess.TimeoutExpired as error:
                stdout, stderr = error.stdout or b"", error.stderr or b""
                result.update(process_started=True, timed_out=True)
                errors.append(language + ": bounded execution timeout")
            except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
                errors.append(language + ": " + str(error))
            for suffix, data in [("stdout", stdout), ("stderr", stderr)]:
                (args.output / (name + "." + language + "." + suffix)).write_bytes(data)
                result[suffix + "_sha256"] = hashlib.sha256(data).hexdigest()
            result["elapsed_seconds"] = time.monotonic() - started
            results[language] = result
        cases.append({"fixture": name, "full_view_rows": len(expected["rows"]),
                      "runs": results, "errors": errors, "pass": not errors})
        print(name, "PASS" if not errors else "FAIL", len(expected["rows"]), flush=True)
    after = {str(path): digest(path) for path in paths}
    answer = {"schema": "original_word_compiled_fixture_review_v1",
              "pass": all(row["pass"] for row in cases) and before == after,
              "claim": "FINITE_IMPORTED_ORIGINAL_EVALUATOR_COEFFICIENT_REVIEW" if config else
                       "FINITE_NATIVE_WORD_COEFFICIENT_REVIEW" if commands else "ORACLE_SELF_CHECK_ONLY",
              "execution_modes": modes, "languages_executed": list(commands),
              "cases_total": len(cases), "cases_passed": sum(row["pass"] for row in cases),
              "full_view_rows_total": sum(row["full_view_rows"] for row in cases), "cases": cases,
              "invalid_table_controls_rejected": invalid_controls,
              "oracle_algorithm": "Full ordered half-rate coupled-generator spectral projectors and independent whole-Copy boundary marginalization",
              "pins_before": before, "pins_after": after,
              "separately_authenticated_kernel_evidence": config.get("kernel_evidence") if config else None,
              "kernel_qualification": "Separate scheduler receipts authenticate exact chosen-table/init/word proofs, fixtures and imported/native artifacts.",
              "Lean_native_work_counters_inferred": False, "Lean_standalone_ELF_claim": False,
              "general_native_refinement_claim": False, "source_admission_verified": False,
              "ancestral_completion_claim": False,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS" if answer["pass"] else "FAIL", len(cases), answer["full_view_rows_total"], len(invalid_controls), flush=True)
    return 0 if answer["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
