#!/usr/bin/env python3
"""Focused independent live controls for the new calendar adapter.

Challenges request binding and hybrid coefficients while a forged native
checker accepts. Also verifies that framed inner UNKNOWN is never promoted to
an independent exhaustion proof, and distinguishes postlaunch internal failure.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

import calendar_check as checker
from review_calendar_helper import project

DESIGN = Path(__file__).resolve().parent
RUST = DESIGN.parent/"rust"
EXPECTED_ADAPTER = "9de9c1bf056a7b0d40900b33ebd3d29f12b2efacab61e90f9ab5b633a86f0db6"
EXPECTED_HELPER = "6190bcd125c51d2e133b571ecc9fe08298fe5a731dc6536459f66446f0ae29bb"


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def fake_binary(path, result, exit_code):
    raw = checker.canonical_json(result)
    check_frame = checker.canonical_json({"schema": "source_calendar_check_v1", "status": "ACCEPT"})
    script = ("#!/usr/bin/python3\nimport sys\n"
              "if sys.argv[1:2] == ['check']:\n"
              f"    sys.stdout.buffer.write({check_frame!r})\n    sys.exit(0)\n"
              "sys.stdin.buffer.read()\n"
              f"sys.stdout.buffer.write({raw!r})\nsys.exit({exit_code})\n")
    path.write_text(script)
    path.chmod(0o700)
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    result = {"schema": "calendar_independent_adapter_review_v1", "pass": False,
              "native_execution": True, "Lean_execution": False, "source_admission": False}
    try:
        adapter = RUST/"native_calendar_component.py"
        before = {str(p): digest(p.read_bytes()) for p in [adapter, DESIGN/"calendar_check.py", args.binary]}
        checker.require(before[str(adapter)] == EXPECTED_ADAPTER and before[str(DESIGN/"calendar_check.py")] == EXPECTED_HELPER,
                        "reviewed adapter/helper identity changed")
        (out/"native_calendar_component.py").write_bytes(adapter.read_bytes())
        (out/"calendar_check.py").write_bytes((DESIGN/"calendar_check.py").read_bytes())
        (out/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
        original = DESIGN/"evidence/calendar-fixture-freeze-1"
        saved = DESIGN/"evidence/calendar-rust-review-1"
        base_request = (original/"parallelCommonCalendar.request.json").read_bytes()
        base = project((saved/"parallelCommonCalendar.rust.stdout").read_bytes())
        controls = []

        def run(name, raw_request, binary, expected_status, expected_exit, solver, checker_started, reference, pin=None):
            request = out/(name+".request.json");request.write_bytes(raw_request)
            destination = out/name
            command = [sys.executable, "-B", str(adapter), "--request", str(request.resolve()),
                       "--output", str(destination.resolve()), "--binary", str(binary.resolve())]
            if pin:
                command += ["--expected-binary-sha256", pin]
            started = time.monotonic()
            executed = subprocess.run(command, capture_output=True, timeout=60)
            (out/(name+".stdout")).write_bytes(executed.stdout)
            (out/(name+".stderr")).write_bytes(executed.stderr)
            record = json.loads((destination/"RESULT.json").read_bytes())
            checker.require(record["schema"] == "rust_calendar_component_result_v1" and
                            record["status"] == expected_status and record["exit_code"] == expected_exit and
                            executed.returncode == expected_exit, "adapter status/exit differs: " + name)
            for field, value in [("solver_called", solver), ("checker_called", checker_started),
                                 ("reference_checker_called", reference), ("certificate_valid", False),
                                 ("source_admission_verified", False), ("provider_work_checked", False),
                                 ("provider_exhaustion_verified", False), ("full_solver_verified", False)]:
                checker.require(record.get(field) is value, "adapter promoted/misstated " + field + ": " + name)
            checker.require(record["request_sha256"] == digest(raw_request), "adapter changed exact raw request binding")
            checker.require((destination/"REQUEST.json").read_bytes() == raw_request, "staged raw request differs")
            passed = {"name": name, "status": record["status"], "exit_code": executed.returncode,
                      "wall_seconds": round(time.monotonic()-started, 6),
                      "result_sha256": digest((destination/"RESULT.json").read_bytes()),
                      "stdout_sha256": digest(executed.stdout), "stderr_sha256": digest(executed.stderr)}
            controls.append(passed)
            result["controls"] = controls
            return record

        # Raw identity differs from the normalized request echo by design.
        raw = b" \n"+checker.canonical_json(checker.parse_request(base_request)).replace(b'"root":0', b'"root":-0')+b" \n"
        good = run("rawSemanticBinding", raw, args.binary, "SUPPLIED_CALENDAR_TABLE", 0,
                   True, True, True, before[str(args.binary)])
        checker.require(good["reference_check"]["full_view_rows"] == 24 and
                        good["binary_pin_verification"] == "EXPECTED_PIN_MATCHED", "wrong asymmetric raw-bound table")

        borrowed = copy.deepcopy(base)
        borrowed["request"]["original_gamma"][0] = "2/3"
        borrowed["agenda"]["physical_coordinates"][-1]["argument"] = "2/3"
        fake = fake_binary(out/"borrowed-bank-producer.py", borrowed, 0)
        rejected = run("foreignSemanticRequest", base_request, fake, "RESOURCE_OR_EXECUTION_FAILURE", 1,
                       True, True, True)
        checker.require(not rejected["formal_table_checked"], "foreign bank promoted to checked table")

        balanced = copy.deepcopy(base)
        rows = balanced["word_result"]["rows"]
        register = rows[0]["view"]["register"]
        same_register = [row for row in rows if row["view"]["register"] == register]
        checker.require(len(same_register) >= 2, "hybrid forge lacks two same-register genealogies")
        dimension = len(balanced["word_result"]["variables"])
        monomial = (0,)*dimension
        def polynomial(row):
            return {tuple(p): Fraction(q) for p, q in row["coefficients"]}
        original_mass = {}
        for row in rows:
            for power, coefficient in polynomial(row).items():
                original_mass[power] = original_mass.get(power, 0)+coefficient
        for row, shift in [(same_register[0], Fraction(1, 1000)), (same_register[1], Fraction(-1, 1000))]:
            p = polynomial(row);p[monomial] = p.get(monomial, 0)+shift
            row["coefficients"] = [[list(power), checker.calendar.ref.epoch.qwire(q)] for power, q in sorted(p.items()) if q]
        forged_mass = {}
        for row in rows:
            for power, coefficient in polynomial(row).items():
                forged_mass[power] = forged_mass.get(power, 0)+coefficient
        checker.require(original_mass == forged_mass, "balanced hybrid control changed total polynomial mass")
        fake = fake_binary(out/"balanced-hybrid-producer.py", balanced, 0)
        rejected = run("balancedHybridCoefficients", base_request, fake, "RESOURCE_OR_EXECUTION_FAILURE", 1,
                       True, True, True)
        checker.require(rejected["checker_execution"]["exit_code"] == 0 and
                        rejected["reference_checker_execution"]["exit_code"] == 1,
                        "balanced hybrid forge was not rejected by independent coefficients")

        unknown_request = (original/"epochCallLimit.request.json").read_bytes()
        unknown = project((saved/"epochCallLimit.rust.stdout").read_bytes())
        unknown["word_result"]["limit"]["required"] = 17
        fake = fake_binary(out/"operational-unknown-producer.py", unknown, 2)
        scoped = run("operationalUnknownQualification", unknown_request, fake, "UNKNOWN", 2, True, True, True)
        checker.require(not scoped["formal_table_checked"] and not scoped["reference_check"]["unknown_exhaustion_verified"]
                        and scoped["reference_check"]["limit_check"] == "PROVIDER_LIMIT_FRAME_ONLY",
                        "framed provider counter falsely verified or promoted")
        checker.require(scoped["unknown_metadata"]["consumer_population"] == ["E", 0], "original UNKNOWN population lost")

        unknown_wrong_request = copy.deepcopy(unknown)
        unknown_wrong_request["request"]["inverse_rates"][0] = "2/1"
        fake = fake_binary(out/"foreign-unknown-producer.py", unknown_wrong_request, 2)
        run("foreignUnknownRequest", unknown_request, fake, "RESOURCE_OR_EXECUTION_FAILURE", 1, True, True, True)

        internal_error = {"schema": checker.SCHEMA, "status": "ERROR", "error": "INTERNAL"}
        fake = fake_binary(out/"internal-failure-producer.py", internal_error, 1)
        failed = run("postlaunchInternalFailure", base_request, fake, "RESOURCE_OR_EXECUTION_FAILURE", 1,
                     True, False, False)
        checker.require(failed["failure_reason"] == "PRODUCER_EXECUTION_FAILED", "postlaunch failure called input refusal")

        after = {str(p): digest(p.read_bytes()) for p in [adapter, DESIGN/"calendar_check.py", args.binary]}
        checker.require(after == before, "accepted inputs changed during adapter review")
        result.update({"pass": True, "cases_passed": len(controls), "identities_before": before, "identities_after": after,
                       "reviewer_sha256": digest(Path(__file__).read_bytes()),
                       "qualification": "Six actual adapter controls; mathematical/reference acceptance distinguished from native replay and operational UNKNOWN. Existing broader adapter controls not rerun; no Lean/RC1/source-admission promotion."})
    except Exception as error:
        result["error"] = str(error)
        raise
    finally:
        (out/"RECEIPT.json").write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"pass": result["pass"], "cases": result["cases_passed"]}))


if __name__ == "__main__":
    main()
