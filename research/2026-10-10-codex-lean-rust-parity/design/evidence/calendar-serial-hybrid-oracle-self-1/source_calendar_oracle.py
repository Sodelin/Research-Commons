#!/usr/bin/env python3
"""Independent supplied-calendar agenda/exposure and complete-word reference.

Event records are sorted by rational date, phase and original ID. Tables reuse
the frozen coupled-generator spectral reference, not the native calendar, path
history, boundary current-owner enumeration or population lift recurrence.
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

import source_word_oracle as ref

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

DESIGN = Path(__file__).resolve().parent
CONTRACT = DESIGN / "CALENDAR-REFINEMENT-20261010T1340Z.md"
WORD_ORACLE_SHA = "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102"
COMPILER_MAX = {"word_length": 32, "slots": 16, "variables": 256}
PROVIDER_DEFAULTS = {
    "epoch": {"calls": 4096, "destinations": 4096, "lifted_terms": 65536,
              "branches": 4096, "term_products": 65536},
    "boundary": {"assignments": 16, "destinations": 16, "term_contributions": 128},
    "completion": {"calls": 4096, "destinations": 4096, "lifted_terms": 65536}}
REQUEST_KEYS = {"context", "ages", "inverse_rates", "original_gamma", "common", "terminal",
                "compiler_limits", "word_limits", "provider_limits"}


class InvalidInput(ValueError):
    def __init__(self, code):
        self.code = code
        super().__init__(code)


def require(condition, code="SOURCE_CALENDAR_INPUT"):
    if not condition:
        raise InvalidInput(code)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rational(token):
    require(type(token) is str)
    try:
        q = Fraction(token)
    except (ValueError, ZeroDivisionError):
        raise InvalidInput("SOURCE_CALENDAR_INPUT") from None
    require(ref.epoch.qwire(q) == token)
    return q


def check_request(request):
    require(type(request) is dict and set(request) == REQUEST_KEYS)
    word_limits = request["word_limits"]
    require(type(word_limits) is dict and set(word_limits) == set(ref.DEFAULT_LIMITS) and
            all(type(cap) is int and 0 <= cap < 2**64 for cap in word_limits.values()), "SOURCE_CALENDAR_LIMITS")
    original = request["context"]
    dummy = {"context": original, "initial": {"kind": "NATURAL"}, "common": request["common"],
             "slots": 0, "word": [], "terminal": request["terminal"], "limits": request["word_limits"]}
    try:
        ref.check_request(dummy)
    except (ValueError, TypeError, KeyError, IndexError):
        raise InvalidInput("SOURCE_CALENDAR_INPUT") from None
    require(all(type(request[key]) is list for key in ["ages", "inverse_rates", "original_gamma"]),
            "SOURCE_CALENDAR_DIMENSIONS")
    require(len(request["ages"]) == original["vertices"] and
            len(request["inverse_rates"]) == len(original["edges"]) + 1 and
            len(request["original_gamma"]) == len(original["hybrids"]), "SOURCE_CALENDAR_DIMENSIONS")
    ages, inverses, gamma = [list(map(rational, request[key]))
                             for key in ["ages", "inverse_rates", "original_gamma"]]
    require(all(ages[younger] < ages[older] for older, younger in original["edges"]),
            "SOURCE_CALENDAR_STRICT_EDGE")
    require(all(q > 0 for q in inverses), "SOURCE_CALENDAR_INVERSE_RATE")
    require(all(0 < q < 1 for q in gamma), "SOURCE_CALENDAR_GAMMA")
    limits = request["compiler_limits"]
    require(type(limits) is dict and set(limits) == set(COMPILER_MAX) and
            all(type(limits[key]) is int and 0 <= limits[key] <= cap for key, cap in COMPILER_MAX.items()),
            "SOURCE_CALENDAR_LIMITS")
    providers = request["provider_limits"]
    require(type(providers) is dict and set(providers) == set(PROVIDER_DEFAULTS), "SOURCE_CALENDAR_LIMITS")
    for kind, fields in PROVIDER_DEFAULTS.items():
        values = providers[kind]
        require(type(values) is dict and set(values) == set(fields) and
                all(type(cap) is int and 0 <= cap < 2**64 for cap in values.values()), "SOURCE_CALENDAR_LIMITS")
    # Validation priority is independent of initialization or generated budgets.
    require(request["terminal"] != "ANCESTRAL_COMPLETE" or original["local_samples"],
            "SOURCE_WORD_COMPLETION_EMPTY_COPY")
    return ages, inverses, gamma


def compile_calendar(request):
    ages, inverses, gamma = check_request(request)
    original = request["context"]
    dates = sorted(set(ages))
    requirements = {"word_length": len(original["edges"]) + original["vertices"] + len(dates) - 1,
                    "slots": len(dates) - 1,
                    "variables": (len(dates) - 1) * (len(original["edges"]) + 1) + len(gamma)}
    for kind in COMPILER_MAX:
        cap = request["compiler_limits"][kind]
        if requirements[kind] > cap:
            return requirements, None, None, {"stage": "COMPILER", "kind": kind,
                                               "required": requirements[kind], "cap": cap}
    # Independent flat event sorting makes equal-date phase ordering explicit.
    records = [(ages[edge[0]], 0, "EXIT", e) for e, edge in enumerate(original["edges"])]
    records += [(age, 1, "ENTER", v) for v, age in enumerate(ages)]
    records.sort()
    date_index = {age: i for i, age in enumerate(dates)}
    word, origins, slots, cohorts = [], [], [], []
    for age in dates:
        index = date_index[age]
        if index:
            slot = index - 1
            slots.append({"slot": slot, "word_position": len(word),
                          "younger_date": ref.epoch.qwire(dates[slot]), "older_date": ref.epoch.qwire(age),
                          "duration": ref.epoch.qwire(age - dates[slot])})
            word.append(["INTERVAL", slot])
            origins.append({"date_index": index, "phase": "INTERVAL", "index": slot})
        exits, vertices = [], []
        for date, phase, tag, ident in records:
            if date == age:
                (exits if phase == 0 else vertices).append(ident)
                word.append([tag, ident])
                origins.append({"date_index": index, "phase": tag, "index": ident})
        cohorts.append({"date_index": index, "representative": min(vertices),
                        "vertices": vertices, "exits": exits})
    child = {"context": original, "initial": {"kind": "NATURAL"}, "common": request["common"],
             "slots": len(slots), "word": word, "terminal": request["terminal"], "limits": request["word_limits"]}
    coordinates = []
    for variable in ref.variables(child):
        if variable[0] == "X":
            p = variable[3] if variable[2] == "E" else len(original["edges"])
            exposure = Fraction(slots[variable[1]]["duration"]) / inverses[p]
            coordinates.append({"variable": variable, "kind": "EXP_NEG", "argument": ref.epoch.qwire(exposure)})
        else:
            coordinates.append({"variable": variable, "kind": "RATIONAL",
                                "argument": ref.epoch.qwire(gamma[variable[1]])})
    agenda = {"dates": list(map(ref.epoch.qwire, dates)), "cohorts": cohorts,
              "word": word, "origins": origins, "slots": slots, "physical_coordinates": coordinates,
              "leaf_age_zero": all(ages[v] == 0 for v in original["leaves"])}
    ref.require(len(word) == requirements["word_length"] and len(coordinates) == requirements["variables"],
                "independent agenda accounting differs")
    ref.check_request(child)
    return requirements, agenda, child, None


def provider_zero_control(request, child):
    """Finite first-call controls, without replaying any native recurrence.

The all-coefficient reference supports the default provider caps and these
explicit zero-budget first-call controls. It does not claim arbitrary native
lift-work counting equivalence from the spectral generator.
"""
    differences = [(kind, key, cap) for kind, values in request["provider_limits"].items()
                   for key, cap in values.items() if cap != PROVIDER_DEFAULTS[kind][key]]
    if not differences:
        return None, None
    ref.require(len(differences) == 1 and differences[0][2] == 0,
                "reference has no arbitrary nondefault native provider-work equivalence")
    kind, key, _ = differences[0]
    if (kind, key) == ("boundary", "assignments"):
        stage = next(i for i, letter in enumerate(child["word"]) if letter[0] != "INTERVAL")
        return {"stage": stage, "kind": "BOUNDARY:Assignments", "required": 1, "cap": 0}, None
    if (kind, key) == ("epoch", "calls"):
        stage = next(i for i, letter in enumerate(child["word"]) if letter[0] == "INTERVAL")
        return {"stage": stage, "kind": "EPOCH:Calls", "required": 1, "cap": 0}, ["E", 0]
    ref.require((kind, key) == ("completion", "calls") and child["terminal"] == "ANCESTRAL_COMPLETE",
                "unsupported first-call provider control")
    return {"stage": "COMPLETION", "kind": "COMPLETION:Calls", "required": 1, "cap": 0}, ["A", child["context"]["root"]]


def expected_probe(name, request):
    requirements, agenda, child, limit = compile_calendar(request)
    answer = {"schema": "source_calendar_probe_v1", "fixture": name, "request": request,
              "source_admission_verified": False, "requirements": requirements,
              "status": "UNKNOWN" if limit else "TABLE"}
    if limit:
        answer.update(unknown_scope="COMPILER", limit=limit)
        return answer, None
    word, internal = ref.expected_probe(name, child)
    provider_limit, population = provider_zero_control(request, child)
    if provider_limit:
        # The bounded combined-priority fixture has queries=0 at its first letter.
        if word["status"] == "UNKNOWN":
            ref.require(word["limit"]["stage"] == 0 and word["limit"]["kind"] == "queries",
                        "unsupported competing reference/provider caps")
            population = None
        else:
            word = {key: word[key] for key in ["schema", "fixture", "request", "variables", "source_admission_verified"]}
            word.update(status="UNKNOWN", limit=provider_limit)
            internal = None
    answer.update(agenda=agenda, word_result=word)
    if word["status"] == "UNKNOWN":
        answer.update(status="UNKNOWN", unknown_scope="WORD", consumer_population=population)
    return answer, internal


def check_probe(actual, expected, internal):
    ref.require(type(actual) is dict and set(actual) == set(expected), "calendar output fields differ")
    for key in set(expected) - {"word_result"}:
        ref.require(ref.epoch.exact_json(actual[key]) == ref.epoch.exact_json(expected[key]),
                    "calendar output changed " + key)
    if "word_result" not in expected:
        return {"status": "PASS", "compiler_unknown": expected["limit"]}
    if expected["word_result"]["status"] == "UNKNOWN":
        ref.require(ref.epoch.exact_json(actual["word_result"]) == ref.epoch.exact_json(expected["word_result"]),
                    "calendar changed original consumer refusal metadata")
        return {"status": "PASS", "word_unknown": expected["word_result"]["limit"]}
    return ref.check_probe(actual["word_result"], expected["word_result"], internal)


def fixtures():
    ordinary = {"vertices": 3, "root": 0, "edges": [[0, 1], [0, 2]], "leaves": [1, 2], "hybrids": []}
    triple = {"vertices": 5, "root": 0, "edges": [[0, 1], [0, 2], [2, 3], [2, 4]],
              "leaves": [1, 3, 4], "hybrids": []}
    parallel = {"vertices": 5, "root": 0, "edges": [[0, 1], [0, 2], [2, 3], [2, 3], [3, 4]],
                "leaves": [1, 4], "hybrids": [[3, 2, 3]]}
    balanced = {"vertices": 7, "root": 0, "edges": [[0, 1], [0, 2], [1, 3], [1, 4], [2, 5], [2, 6]],
                "leaves": [3, 4, 5, 6], "hybrids": []}

    def request(source, samples, ages, inverses=None, gamma=(), common=(), terminal="ANCESTRAL_COMPLETE", labels=None):
        return {"context": {**copy.deepcopy(source), "local_samples": list(samples),
                            "global_labels": list(range(len(samples))) if labels is None else list(labels)},
                "ages": [ref.epoch.qwire(Fraction(q)) for q in ages],
                "inverse_rates": [ref.epoch.qwire(Fraction(q)) for q in (inverses or [1] * (len(source["edges"]) + 1))],
                "original_gamma": [ref.epoch.qwire(Fraction(q)) for q in gamma], "common": list(common),
                "terminal": terminal, "compiler_limits": dict(COMPILER_MAX), "word_limits": dict(ref.DEFAULT_LIMITS),
                "provider_limits": copy.deepcopy(PROVIDER_DEFAULTS)}

    cases = {
        "twoTipCalendar": request(ordinary, [0, 1], [2, 0, 0], [1, 2, Fraction(3, 2)]),
        "singletonCalendar": request(ordinary, [1], [1, 0, 0]),
        "emptyNaturalCalendar": request(parallel, [], [3, 0, 2, 1, 0], gamma=[Fraction(1, 3)], common=[True], terminal="FULL_VIEW"),
        "ordinaryThreeCalendar": request(triple, [0, 1, 2], [3, 0, 1, 0, 0], [1, 2, Fraction(3, 2), Fraction(5, 2), 3]),
        "ordinaryThreeRetimed": request(triple, [0, 1, 2], [7, 0, 2, 0, 0], [1, 2, Fraction(3, 2), Fraction(5, 2), 3]),
        "serialNegativeTips": request(ordinary, [0, 0, 1], [Fraction(3, 2), Fraction(-3, 2), Fraction(1, 4)], [Fraction(7, 3), Fraction(11, 5), Fraction(2, 3)]),
        "tiedInternalCohort": request(balanced, [0, 1, 2], [3, 1, 1, 0, 0, 0, 0]),
        "incomparableOrderLeft": request(balanced, [0, 1, 2], [4, 1, 2, 0, 0, 0, 0]),
        "incomparableOrderRight": request(balanced, [0, 1, 2], [4, 2, 1, 0, 0, 0, 0]),
        "parallelCommonCalendar": request(parallel, [0, 1, 1], [3, 0, 2, 1, 0], [1, 2, Fraction(3, 2), Fraction(5, 2), Fraction(7, 3), Fraction(2, 3)], [Fraction(1, 3)], [True]),
        "parallelIndependentCalendar": request(parallel, [0, 1, 1], [3, 0, 2, 1, 0], [1, 2, Fraction(3, 2), Fraction(5, 2), Fraction(7, 3), Fraction(2, 3)], [Fraction(1, 3)], [False]),
        "permutedLabelsCalendar": request(triple, [0, 1, 2], [3, 0, 1, 0, 0], labels=[3, 0, 2]),
        "largeExactExposure": request(ordinary, [0, 1], [Fraction(2**300 + 1, 11), 0, 0], [Fraction(13, 17), Fraction(19, 23), Fraction(29, 31)]),
    }
    cases["reversedParallelParents"] = copy.deepcopy(cases["parallelCommonCalendar"])
    cases["reversedParallelParents"]["context"]["hybrids"][0] = [3, 3, 2]
    large = {"vertices": 15, "root": 0, "edges": [[(v - 1) // 2, v] for v in range(1, 15)],
             "leaves": list(range(7, 15)), "hybrids": []}
    cases["validFortyThreeLetters"] = request(large, [0], list(range(20, 5, -1)))
    for kind, cap in [("word_length", 5), ("slots", 0), ("variables", 2)]:
        cases["compilerLimit_" + kind] = copy.deepcopy(cases["twoTipCalendar"])
        cases["compilerLimit_" + kind]["compiler_limits"][kind] = cap
    cases["compilerPriority"] = copy.deepcopy(cases["twoTipCalendar"])
    cases["compilerPriority"]["compiler_limits"] = dict.fromkeys(COMPILER_MAX, 0)
    cases["wordQueryLimit"] = copy.deepcopy(cases["twoTipCalendar"])
    cases["wordQueryLimit"]["word_limits"]["queries"] = 0
    for name, provider, key in [("boundaryAssignmentLimit", "boundary", "assignments"),
                                ("epochCallLimit", "epoch", "calls"),
                                ("completionCallLimit", "completion", "calls")]:
        cases[name] = copy.deepcopy(cases["singletonCalendar"])
        cases[name]["provider_limits"][provider][key] = 0
    cases["wordQueryBeforeProviderLimit"] = copy.deepcopy(cases["boundaryAssignmentLimit"])
    cases["wordQueryBeforeProviderLimit"]["word_limits"]["queries"] = 0
    invalid = [("emptyCompletionRejected", "singletonCalendar"), ("zeroInverseRejected", "twoTipCalendar"),
               ("negativeInverseRejected", "twoTipCalendar"), ("equalEdgeAgeRejected", "twoTipCalendar"),
               ("reversedEdgeAgeRejected", "twoTipCalendar"), ("gammaZeroRejected", "parallelCommonCalendar"),
               ("gammaOneRejected", "parallelCommonCalendar"), ("aboveHardcapRejected", "twoTipCalendar")]
    for name, origin in invalid:
        cases[name] = copy.deepcopy(cases[origin])
    cases["emptyCompletionRejected"]["context"].update(local_samples=[], global_labels=[])
    cases["emptyCompletionRejected"]["compiler_limits"] = dict.fromkeys(COMPILER_MAX, 0)
    cases["zeroInverseRejected"]["inverse_rates"][0] = "0/1"
    cases["zeroInverseRejected"]["compiler_limits"] = dict.fromkeys(COMPILER_MAX, 0)
    cases["negativeInverseRejected"]["inverse_rates"][0] = "-1/1"
    cases["equalEdgeAgeRejected"]["ages"][0] = "0/1"
    cases["reversedEdgeAgeRejected"]["ages"][0] = "-1/1"
    cases["gammaZeroRejected"]["original_gamma"][0] = "0/1"
    cases["gammaOneRejected"]["original_gamma"][0] = "1/1"
    cases["aboveHardcapRejected"]["compiler_limits"]["word_length"] = 33
    return cases


def self_controls(expected):
    controls = []
    base, internal = expected["parallelCommonCalendar"]
    for name, mutate in [
        ("parallel occurrence collapsed", lambda x: x["agenda"]["cohorts"][2]["exits"].pop()),
        ("wrong shared inverse exposure", lambda x: x["agenda"]["physical_coordinates"][0].update(argument="1/7")),
        ("exit/entry phase swapped", lambda x: x["agenda"]["word"].reverse()),
        ("original gamma complemented", lambda x: x["agenda"]["physical_coordinates"][-1].update(argument="2/3")),
        ("scientific gate promoted", lambda x: x.update(source_admission_verified=True))]:
        bad = copy.deepcopy(base)
        mutate(bad)
        try:
            check_probe(bad, base, internal)
        except ValueError:
            controls.append(name)
        else:
            raise ValueError("calendar checker accepted " + name)
    a = expected["ordinaryThreeCalendar"][0]
    b = expected["ordinaryThreeRetimed"][0]
    def rows(frame):
        return {ref.epoch.exact_json(row["view"]): row["coefficients"] for row in frame["word_result"]["rows"]}
    ref.require(a["agenda"]["word"] == b["agenda"]["word"] and rows(a) == rows(b) and
                a["agenda"]["physical_coordinates"] != b["agenda"]["physical_coordinates"],
                "same weak-order retiming did not preserve formal law/change physical exposures")
    ref.require(expected["incomparableOrderLeft"][0]["agenda"]["word"] !=
                expected["incomparableOrderRight"][0]["agenda"]["word"], "changed weak-order cell lost original event order")
    controls += ["same weak-order formal table / distinct physical exposures", "different incomparable order / distinct word"]
    return controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-inputs", type=Path)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=30, choices=range(1, 61))
    args = parser.parse_args()
    ref.require(digest(DESIGN / "source_word_oracle.py") == WORD_ORACLE_SHA, "frozen word reference changed")
    args.output.mkdir(parents=True, exist_ok=False)
    paths = [Path(__file__).resolve(), CONTRACT, DESIGN / "source_word_oracle.py", DESIGN / "boundary_oracle.py",
             DESIGN / "epoch_oracle.py", DESIGN / "population_oracle.py", DESIGN / "chart_check.py", DESIGN / "certificate_check.py"]
    if args.rust_probe:
        paths.append(args.rust_probe.resolve())
    before = {str(path): digest(path) for path in paths}
    for path in paths:
        if path.parent == DESIGN:
            (args.output / path.name).write_bytes(path.read_bytes())
    all_cases, results, expected = fixtures(), [], {}
    if args.freeze_inputs:
        args.freeze_inputs.mkdir(parents=True, exist_ok=False)
    for name, request in all_cases.items():
        if args.freeze_inputs:
            (args.freeze_inputs / (name + ".request.json")).write_text(json.dumps(request, indent=2) + "\n")
        record = {"fixture": name}
        try:
            want, internal = expected_probe(name, request)
            expected[name] = (want, internal)
            check_probe(want, want, internal)
            record.update(expected_status=want["status"], requirements=want["requirements"],
                          unknown_scope=want.get("unknown_scope"), full_view_rows=len(want.get("word_result", {}).get("rows", [])))
            (args.output / (name + ".expected.json")).write_text(json.dumps(want, indent=2) + "\n")
            invalid_code = None
        except InvalidInput as error:
            want, internal, invalid_code = None, None, error.code
            record.update(expected_status="INVALID_INPUT", invalid_code=invalid_code)
        if args.rust_probe:
            run = {"process_started": False, "exit_code": None, "timed_out": False}
            stdout, stderr = b"", b""
            try:
                process = subprocess.run([str(args.rust_probe.resolve()), name], capture_output=True, timeout=args.timeout)
                stdout, stderr = process.stdout, process.stderr
                run.update(process_started=True, exit_code=process.returncode)
                ref.require(max(len(stdout), len(stderr)) <= 4 * 1024 * 1024, "private calendar frame exceeds cap")
                if invalid_code:
                    ref.require(process.returncode == 1 and not stdout and invalid_code in stderr.decode("utf-8"),
                                "calendar input refusal/status/validation priority differs")
                else:
                    ref.require(process.returncode == 0, "calendar native process failed")
                    run["review"] = check_probe(ref.epoch.parse_json(stdout), want, internal)
                record["pass"] = True
            except (ValueError, subprocess.TimeoutExpired) as error:
                run["error"] = str(error)
                if isinstance(error, subprocess.TimeoutExpired):
                    stdout, stderr = error.stdout or b"", error.stderr or b""
                    run.update(process_started=True, timed_out=True)
                record["pass"] = False
            for suffix, data in [("stdout", stdout), ("stderr", stderr)]:
                (args.output / (name + ".rust." + suffix)).write_bytes(data)
                run[suffix + "_sha256"] = hashlib.sha256(data).hexdigest()
            record["run"] = run
        else:
            record["pass"] = True
        results.append(record)
    controls = self_controls(expected)
    if args.freeze_inputs:
        inventory = {"schema": "calendar_input_only_freeze_v1", "contract_sha256": before[str(CONTRACT)],
                     "oracle_sha256": before[str(Path(__file__).resolve())], "new_native_execution": False,
                     "validation": "All inputs validated independently before native source mutation; intentional invalid controls retained with expected codes.",
                     "inputs": [{"fixture": name, "path": name + ".request.json",
                                 "sha256": digest(args.freeze_inputs / (name + ".request.json")),
                                 "expected_status": row["expected_status"], "invalid_code": row.get("invalid_code")}
                                for name, row in zip(all_cases, results)]}
        (args.freeze_inputs / "INVENTORY.json").write_text(json.dumps(inventory, indent=2) + "\n")
    after = {path: digest(Path(path)) for path in before}
    ref.require(before == after, "calendar input/reference/producer changed during review")
    answer = {"schema": "calendar_complete_reference_review_v1", "pass": all(row["pass"] for row in results),
              "claim": "FINITE_NATIVE_CALENDAR_COEFFICIENT_REVIEW" if args.rust_probe else "INDEPENDENT_INPUT_AND_ORACLE_PREPARATION_ONLY",
              "native_processes_executed": bool(args.rust_probe), "Lean_execution": False,
              "cases_total": len(results), "cases_passed": sum(row["pass"] for row in results),
              "full_view_rows_total": sum(row.get("full_view_rows", 0) for row in results),
              "controls": controls, "cases": results, "pins_before": before, "pins_after": after,
              "source_admission_verified": False, "universal_calendar_refinement_proved": False,
              "arbitrary_nondefault_provider_work_equivalence_claimed": False,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS" if answer["pass"] else "FAIL", len(results), answer["full_view_rows_total"], len(controls), flush=True)
    if not answer["pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
