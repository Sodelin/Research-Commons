#!/usr/bin/env python3
"""Compare three completed literal source-word rows with supplied calendars.

The Lean coefficient envelope has no producer agenda or native work fields.
Typed proofs separately bind complete literal phases to the original calendar
law through the inherited phase-Perm results. This reviewer does not equate
ascending IDs with arbitrary Finset.toList choices or prove a universal native
calendar extraction theorem. Only the sole compiler/evaluator scheduler may
provide --lean-execution-config and execute the authenticated Lean context.
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

import calendar_check as production
import review_word_compiled_fixtures as direct
import source_calendar_oracle as calendar

DESIGN = Path(__file__).resolve().parent
NAMES = ("twoTipCalendar", "serialNegativeTips", "parallelCommonCalendar")
PINS = {
    "calendar_check.py": "6190bcd125c51d2e133b571ecc9fe08298fe5a731dc6536459f66446f0ae29bb",
    "review_word_compiled_fixtures.py": "f0763dadfe55ba1f6ba40e2f545637966082347226c1796eeffea8cf4e6691c8",
    "source_calendar_oracle.py": "3f01def72cbd1b999099f713764e97941753a12349bcf4e23f3e7d90b63de27c",
    "source_word_oracle.py": "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102",
    "boundary_oracle.py": "0d85747a1f58c4c78b4aa7b0a8f671cd145b7a5f4ce990f9ed33df6b4766db29",
    "epoch_oracle.py": "da66bf78d538d7acdc8d67b560b3d7fe95fd987d614cf34ffd3803c03c8235bd",
    "population_oracle.py": "216d83a844019f115de1dfa19c12827e0570348181d380f1435dc6ee646748ff",
    "chart_check.py": "3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a",
    "certificate_check.py": "ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24",
}


def origin(name):
    calendar.require(name in NAMES, "unknown completed calendar fixture")
    return DESIGN / "evidence" / "calendar-fixture-freeze-1" / (name + ".request.json")


def expected(name):
    raw = origin(name).read_bytes()
    request = production.parse_request(raw)
    requirements, agenda, child, limit = calendar.compile_calendar(request)
    calendar.require(limit is None and child["terminal"] == "ANCESTRAL_COMPLETE",
                     "frozen calendar does not have a complete child word")
    word, internal = calendar.ref.expected_probe(name, child)
    calendar.require(word["status"] == "TABLE", "completed reference exhausted its limits")
    answer = {"schema": "source_original_word_coefficients_v1", "fixture": name,
              "request": child, "variables": word["variables"], "rows": word["rows"]}
    return answer, internal, {"request": request, "requirements": requirements, "agenda": agenda}


def controls():
    answer, internal, _ = expected("parallelCommonCalendar")
    candidates = [
        ("native work fields in Lean envelope", lambda x: x.update(work={})),
        ("completion replaced by full view", lambda x: x["request"].__setitem__("terminal", "FULL_VIEW")),
        ("COMMON replaced by INDEPENDENT", lambda x: x["request"]["common"].__setitem__(0, False)),
        ("original gamma coordinate changed", lambda x: x["variables"][-1].__setitem__(1, 1)),
        ("complete destination omitted", lambda x: x["rows"].pop()),
        ("complete destination duplicated", lambda x: x["rows"].append(copy.deepcopy(x["rows"][0]))),
        ("original register witness changed", lambda x: x["rows"][0]["witness"]["register"].__setitem__(3, not x["rows"][0]["witness"]["register"][3])),
        ("balanced same-register coefficient forgery", balanced),
    ]
    rejected = []
    for label, mutate in candidates:
        bad = copy.deepcopy(answer)
        mutate(bad)
        calendar.require(bad != answer, "review control changed no semantic bytes: " + label)
        try:
            direct.check_direct(bad, answer, internal)
        except (ValueError, TypeError, KeyError, IndexError):
            rejected.append(label)
        else:
            raise ValueError("completed source-word checker accepted " + label)
    return rejected


def balanced(answer):
    from fractions import Fraction
    first = answer["rows"][0]
    second = next(row for row in answer["rows"][1:]
                  if row["view"]["register"] == first["view"]["register"])
    exponent = first["coefficients"][0][0]
    for row, delta in [(first, Fraction(1, 1000)), (second, Fraction(-1, 1000))]:
        terms = {tuple(e): Fraction(q) for e, q in row["coefficients"]}
        terms[tuple(exponent)] = terms.get(tuple(exponent), Fraction(0)) + delta
        row["coefficients"] = [[list(e), calendar.ref.epoch.qwire(q)]
                               for e, q in sorted(terms.items()) if q]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-calendar-solver", type=Path)
    parser.add_argument("--lean-execution-config", type=Path)
    parser.add_argument("--lean-artifact", type=Path, action="append", default=[])
    parser.add_argument("--fixture", action="append")
    parser.add_argument("--timeout", type=int, default=30, choices=range(1, 61))
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    names = args.fixture or list(NAMES)
    calendar.require(len(names) == len(set(names)) and set(names) <= set(NAMES),
                     "repeated or unknown completed calendar fixture")
    for name, sha in PINS.items():
        calendar.require(direct.digest(DESIGN / name) == sha, "reference pin changed: " + name)
    args.output.mkdir(parents=True, exist_ok=False)
    paths = [Path(__file__).resolve(), *[DESIGN / name for name in PINS],
             DESIGN / "CALENDAR-REFINEMENT-20261010T1340Z.md",
             *[origin(name) for name in names], *[p.resolve() for p in args.lean_artifact]]
    commands, environments, directories, modes = {}, {}, {}, {}
    config = None
    if args.native_calendar_solver:
        native = args.native_calendar_solver.resolve()
        paths.append(native)
        commands["rust"] = [str(native), "solve"]
        modes["rust"] = "general_supplied_calendar_frontend_projected_to_completed_coefficient_rows"
    if args.lean_execution_config:
        config_path = args.lean_execution_config.resolve()
        config = calendar.ref.epoch.parse_json(config_path.read_bytes())
        compiler, driver = Path(config["compiler_path"]), Path(config["driver_path"])
        calendar.require(direct.digest(compiler) == config["compiler_sha256"] and
                         direct.digest(driver) == config["driver_sha256"], "evaluator configuration pins differ")
        prefix = config["command_prefix"]
        calendar.require(prefix[0] == str(compiler) and prefix[-2:] == ["--run", str(driver)] and
                         all(flag in prefix for flag in ["-j1", "-t0", "-Ddebug.skipKernelTC=false"]),
                         "unexpected bounded compiled evaluator command")
        calendar.require(set(names) <= set(config["fixtures"]), "typed fixture missing from context")
        paths.extend([config_path, compiler, driver])
        staged = args.output / "LEAN-DRIVER.lean"
        staged.write_bytes(driver.read_bytes())
        (args.output / "LEAN-EXECUTION-CONFIG.json").write_bytes(config_path.read_bytes())
        commands["lean"] = [*prefix[:-1], str(staged.resolve())]
        environments["lean"] = dict(os.environ, LEAN_PATH=config["lean_path"])
        directories["lean"] = config["workdir"]
        modes["lean"] = "compiled_lean_evaluator_not_standalone_elf"
    before = {str(path): direct.digest(path) for path in paths}
    for path in paths:
        if path.parent == DESIGN:
            (args.output / path.name).write_bytes(path.read_bytes())
    rejected, cases = controls(), []
    for name in names:
        wanted, internal, binding = expected(name)
        direct.check_direct(wanted, wanted, internal)
        raw = origin(name).read_bytes()
        (args.output / (name + ".calendar-request.json")).write_bytes(raw)
        for suffix, value in [("expected", wanted), ("calendar-binding", binding)]:
            (args.output / (name + "." + suffix + ".json")).write_text(json.dumps(value, indent=2) + "\n")
        runs, errors = {}, []
        for language, prefix in commands.items():
            command = [*prefix, name] if language == "lean" else prefix
            record = {"command": command, "execution_mode": modes[language], "process_started": False,
                      "exit_code": None, "timed_out": False}
            stdout, stderr, started = b"", b"", time.monotonic()
            try:
                process = subprocess.run(command, input=raw if language == "rust" else None,
                                         capture_output=True, timeout=args.timeout,
                                         cwd=directories.get(language), env=environments.get(language))
                stdout, stderr = process.stdout, process.stderr
                record.update(process_started=True, exit_code=process.returncode)
                calendar.require(process.returncode == 0 and max(len(stdout), len(stderr)) <= 4 * 1024 * 1024,
                                 "completed fixture failed or exceeded frame cap")
                actual = calendar.ref.epoch.parse_json(stdout)
                if language == "rust":
                    record["production_reference_review"] = production.verify_certificate(raw, stdout, 0)
                    word = actual["word_result"]
                    actual = {"schema": wanted["schema"], "fixture": name, "request": word["request"],
                              "variables": word["variables"], "rows": word["rows"]}
                record["coefficient_review"] = direct.check_direct(actual, wanted, internal)
            except subprocess.TimeoutExpired as error:
                stdout, stderr = error.stdout or b"", error.stderr or b""
                record.update(process_started=True, timed_out=True)
                errors.append(language + ": bounded execution timeout")
            except (OSError, ValueError, TypeError, KeyError, IndexError) as error:
                errors.append(language + ": " + str(error))
            for suffix, data in [("stdout", stdout), ("stderr", stderr)]:
                (args.output / (name + "." + language + "." + suffix)).write_bytes(data)
                record[suffix + "_sha256"] = hashlib.sha256(data).hexdigest()
            record["elapsed_seconds"] = time.monotonic() - started
            runs[language] = record
        cases.append({"fixture": name, "full_view_rows": len(wanted["rows"]),
                      "runs": runs, "errors": errors, "pass": not errors})
        print(name, "PASS" if not errors else "FAIL", len(wanted["rows"]), flush=True)
    after = {str(path): direct.digest(path) for path in paths}
    answer = {"schema": "original_completed_calendar_literal_word_review_v1",
              "pass": all(case["pass"] for case in cases) and before == after,
              "claim": "FINITE_IMPORTED_ORIGINAL_COMPLETED_LITERAL_WORD_REVIEW" if config else
                       "FINITE_NATIVE_COMPLETED_CALENDAR_REVIEW" if commands else "REFERENCE_PREPARATION_ONLY",
              "execution_modes": modes, "languages_executed": list(commands),
              "cases_total": len(cases), "cases_passed": sum(case["pass"] for case in cases),
              "full_view_rows_total": sum(case["full_view_rows"] for case in cases), "cases": cases,
              "invalid_table_controls_rejected": rejected, "pins_before": before, "pins_after": after,
              "separately_authenticated_kernel_evidence": config.get("kernel_evidence") if config else None,
              "phase_permutation_qualification": "Typed proofs separately bind literal complete phases to the physical original calendar law; arbitrary Finset.toList choices are not asserted equal.",
              "Lean_native_work_counters_inferred": False, "Lean_standalone_ELF_claim": False,
              "general_native_calendar_refinement_claim": False, "source_admission_verified": False,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS" if answer["pass"] else "FAIL", len(cases), answer["full_view_rows_total"], len(rejected), flush=True)
    return 0 if answer["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
