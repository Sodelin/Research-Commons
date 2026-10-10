#!/usr/bin/env python3
"""Two additive serial-hybrid calendar controls, with an independent reference.

The original 32-input contract, helper and receipts remain frozen. These inputs
exercise two distinct original registers and four distinct parallel parent
occurrences. No Lean calendar extraction or general source admission is claimed.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import time

import source_calendar_oracle as oracle

DESIGN = Path(__file__).resolve().parent
ORACLE_SHA = "3f01def72cbd1b999099f713764e97941753a12349bcf4e23f3e7d90b63de27c"
CONTRACT_SHA = "7e2202aeac884c2024e3f168031b8e90ae73f3c9c924252e7e3705aeb8cba478"
FREEZE = DESIGN / "evidence/calendar-serial-hybrid-fixture-freeze-1"
NAMES = ("serialTwoCommonCalendar", "serialTwoIndependentCalendar")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def requests():
    source = {"vertices": 7, "root": 0,
              "edges": [[0, 1], [0, 2], [2, 3], [2, 3], [3, 4],
                        [4, 5], [4, 5], [5, 6]],
              "leaves": [1, 6], "hybrids": [[3, 2, 3], [5, 5, 6]],
              "local_samples": [0, 1, 1], "global_labels": [0, 1, 2]}
    base = {"context": source, "ages": ["5/1", "0/1", "4/1", "3/1", "2/1", "1/1", "0/1"],
            "inverse_rates": ["1/1", "2/1", "3/2", "5/2", "7/3", "11/5", "13/7", "17/11", "2/3"],
            "original_gamma": ["1/3", "2/5"], "common": [True, True],
            "terminal": "ANCESTRAL_COMPLETE", "compiler_limits": dict(oracle.COMPILER_MAX),
            "word_limits": dict(oracle.ref.DEFAULT_LIMITS),
            "provider_limits": copy.deepcopy(oracle.PROVIDER_DEFAULTS)}
    result = {name: copy.deepcopy(base) for name in NAMES}
    result[NAMES[1]]["common"] = [False, False]
    return result


def register_controls(expected):
    """Check the complete polynomial register marginal, not just total mass."""
    details = []
    for name in NAMES:
        answer, internal = expected[name]
        child = answer["word_result"]
        request = child["request"]
        initial, assignments, contributions = oracle.ref.initial_rows(request)
        oracle.ref.require(assignments == 4 and contributions == 9 and len(initial) == 4,
                           "two original hybrids did not retain four once-drawn registers/raw nine terms")
        oracle.ref.require(child["work"]["initial_assignments"] == 4 and
                           child["work"]["initial_term_contributions"] == 9,
                           "native-compatible initialization counters differ")
        dimension = len(child["variables"])
        oracle.ref.require(answer["requirements"] == {"word_length": 20, "slots": 5, "variables": 47} and
                           answer["agenda"]["physical_coordinates"][-2:] == [
                               {"variable": ["ORIGINAL_GAMMA", 0], "kind": "RATIONAL", "argument": "1/3"},
                               {"variable": ["ORIGINAL_GAMMA", 1], "kind": "RATIONAL", "argument": "2/5"}],
                           "shared original-hybrid bank or calendar accounting changed")
        wanted = {}
        for code, poly in initial.items():
            bits = (code.register[3], code.register[5])
            wanted[bits] = poly
        observed = {}
        for row in child["rows"]:
            register = row["view"]["register"]
            oracle.ref.require(len(register) == 7 and not any(register[v] for v in [0, 1, 2, 4, 6]),
                               "natural source register changed a nonhybrid bit")
            bits = (register[3], register[5])
            poly = {tuple(p): Fraction(q) for p, q in row["coefficients"]}
            oracle.ref.add(observed.setdefault(bits, {}), poly)
        oracle.ref.require(observed == wanted and len(observed) == 4,
                           "full polynomial original-register marginal differs")
        gamma = [Fraction(1, 3), Fraction(2, 5)]
        masses = {}
        for bits, poly in observed.items():
            total = Fraction(0)
            for powers, coefficient in poly.items():
                oracle.ref.require(not any(powers[:dimension - 2]),
                                   "register marginal retains a population exposure variable")
                total += coefficient * gamma[0] ** powers[-2] * gamma[1] ** powers[-1]
            masses[str(list(bits))] = oracle.ref.epoch.qwire(total)
        oracle.ref.require(set(masses.values()) == {"2/5", "4/15", "1/5", "2/15"},
                           "asymmetric original-coin probabilities differ")
        details.append({"fixture": name, "initial_register_assignments": 4,
                        "initial_raw_monomial_contributions": 9, "exact_register_masses": masses,
                        "full_view_rows": len(child["rows"])})
    a, _ = expected[NAMES[0]]
    b, _ = expected[NAMES[1]]
    def rows(frame):
        return {oracle.ref.epoch.exact_json(row["view"]): row["coefficients"]
                for row in frame["word_result"]["rows"]}
    oracle.ref.require(rows(a) != rows(b), "COMMON and current-owner INDEPENDENT interaction became identical")
    rejected = []
    base, internal = expected[NAMES[0]]
    for name, mutate in [
        ("second original gamma aliased", lambda x: x["agenda"]["physical_coordinates"][-1].update(argument="1/3")),
        ("second parallel occurrence omitted", lambda x: x["agenda"]["word"].remove(["EXIT", 6])),
        ("second stored register erased", lambda x: x["word_result"]["rows"][0]["witness"]["register"].__setitem__(5, not x["word_result"]["rows"][0]["witness"]["register"][5])),
        ("natural raw nine contributions collapsed", lambda x: x["word_result"]["work"].update(initial_term_contributions=6))]:
        bad = copy.deepcopy(base)
        mutate(bad)
        try:
            oracle.check_probe(bad, base, internal)
        except (ValueError, TypeError, KeyError, IndexError):
            rejected.append(name)
        else:
            raise ValueError("serial hybrid checker accepted " + name)
    return details, rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-inputs", type=Path)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=30, choices=range(1, 61))
    args = parser.parse_args()
    ref = oracle.ref
    ref.require(digest(DESIGN / "source_calendar_oracle.py") == ORACLE_SHA and
                digest(oracle.CONTRACT) == CONTRACT_SHA, "original calendar contract/reference changed")
    args.output.mkdir(parents=True, exist_ok=False)
    origins = args.freeze_inputs or FREEZE
    if args.freeze_inputs:
        ref.require(not args.rust_probe, "input-only freeze must precede new native execution")
        origins.mkdir(parents=True, exist_ok=False)
        for name, request in requests().items():
            (origins / (name + ".request.json")).write_text(json.dumps(request, indent=2) + "\n")
    paths = [Path(__file__).resolve(), DESIGN / "source_calendar_oracle.py", oracle.CONTRACT,
             *[DESIGN / name for name in ["source_word_oracle.py", "boundary_oracle.py", "epoch_oracle.py",
                                         "population_oracle.py", "chart_check.py", "certificate_check.py"]],
             *[origins / (name + ".request.json") for name in NAMES]]
    if args.rust_probe:
        paths += [args.rust_probe.resolve(), origins / "INVENTORY.json"]
    before = {str(path): digest(path) for path in paths}
    for path in paths:
        if path.parent == DESIGN:
            (args.output / path.name).write_bytes(path.read_bytes())
    expected, records = {}, []
    for name, request in requests().items():
        ref.require(ref.epoch.exact_json(ref.epoch.parse_json((origins / (name + ".request.json")).read_bytes())) ==
                    ref.epoch.exact_json(request), "separate serial input differs from frozen reference")
        answer, internal = oracle.expected_probe(name, request)
        ref.require(answer["status"] == "TABLE", "two-hybrid reference exhausted the unchanged caps")
        oracle.check_probe(answer, answer, internal)
        expected[name] = answer, internal
        (args.output / (name + ".expected.json")).write_text(json.dumps(answer, indent=2) + "\n")
        record = {"fixture": name, "request_sha256": digest(origins / (name + ".request.json")),
                  "full_view_rows": len(answer["word_result"]["rows"]), "pass": True}
        if args.rust_probe:
            run = {"process_started": False, "exit_code": None, "timed_out": False}
            stdout, stderr = b"", b""
            try:
                process = subprocess.run([str(args.rust_probe.resolve()), name], capture_output=True, timeout=args.timeout)
                stdout, stderr = process.stdout, process.stderr
                run.update(process_started=True, exit_code=process.returncode)
                ref.require(process.returncode == 0 and max(len(stdout), len(stderr)) <= 4 * 1024 * 1024,
                            "two-hybrid calendar process failed or exceeded frame cap")
                run["review"] = oracle.check_probe(ref.epoch.parse_json(stdout), answer, internal)
            except (OSError, ValueError, TypeError, KeyError, IndexError, subprocess.TimeoutExpired) as error:
                record["pass"] = False
                run["error"] = str(error)
                if isinstance(error, subprocess.TimeoutExpired):
                    stdout, stderr = error.stdout or b"", error.stderr or b""
                    run.update(process_started=True, timed_out=True)
            for suffix, data in [("stdout", stdout), ("stderr", stderr)]:
                (args.output / (name + ".rust." + suffix)).write_bytes(data)
                run[suffix + "_sha256"] = hashlib.sha256(data).hexdigest()
            record["run"] = run
        records.append(record)
        print(name, "PASS" if record["pass"] else "FAIL", record["full_view_rows"], flush=True)
    marginals, rejected = register_controls(expected)
    if args.freeze_inputs:
        inventory = {"schema": "serial_two_hybrid_calendar_input_only_v1", "new_native_execution": False,
                     "parent_calendar_contract_sha256": CONTRACT_SHA, "parent_calendar_oracle_sha256": ORACLE_SHA,
                     "independent_control_driver_sha256": digest(Path(__file__).resolve()),
                     "inputs": [{"fixture": name, "path": name + ".request.json",
                                 "sha256": digest(origins / (name + ".request.json"))} for name in NAMES],
                     "register_marginal_controls": marginals, "same_compiler_and_provider_limits": True}
        (origins / "INVENTORY.json").write_text(json.dumps(inventory, indent=2) + "\n")
    after = {str(path): digest(path) for path in paths}
    ref.require(before == after, "serial fixture/reference/producer changed during review")
    receipt = {"schema": "serial_two_hybrid_calendar_review_v1", "pass": all(r["pass"] for r in records),
               "claim": "FINITE_NATIVE_CALENDAR_REVIEW" if args.rust_probe else "INPUT_AND_ORACLE_PREPARATION_ONLY",
               "native_execution": bool(args.rust_probe), "Lean_execution": False,
               "cases_total": 2, "cases_passed": sum(r["pass"] for r in records),
               "full_view_rows_total": sum(r["full_view_rows"] for r in records), "cases": records,
               "register_marginal_controls": marginals, "adversarial_controls_rejected": rejected,
               "pins_before": before, "pins_after": after, "source_admission_verified": False,
               "general_calendar_refinement_proved": False,
               "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print("PASS" if receipt["pass"] else "FAIL", 2, receipt["full_view_rows_total"], len(rejected), flush=True)
    return 0 if receipt["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
