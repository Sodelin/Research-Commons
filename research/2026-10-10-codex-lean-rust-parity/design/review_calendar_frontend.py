#!/usr/bin/env python3
"""Actual general-input calendar frontend versus frozen coefficients/reference.

Stages the measured new executable, runs stdin/file input, captures complete
bytes and real status, and independently validates every table coefficient.
Existing private producers, Lean compilation and RC1 baselines are not rerun.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time

import calendar_check as checker
from review_calendar_helper import MODULES, project

DESIGN = Path(__file__).resolve().parent


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def process_limits():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, 4*1024**3))
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_FSIZE, (checker.MAX_CERTIFICATE_BYTES, checker.MAX_CERTIFICATE_BYTES))
    resource.setrlimit(resource.RLIMIT_NOFILE, (64, 64))


def launch(command, output, name, raw=None):
    started = time.monotonic()
    stdout, stderr = output/(name+".stdout"), output/(name+".stderr")
    timed_out = False
    with stdout.open("wb") as out, stderr.open("wb") as err:
        child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=out, stderr=err,
                                 preexec_fn=process_limits)
        try:
            child.communicate(raw, timeout=20)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGKILL)
            child.communicate()
    captured = stdout.read_bytes()
    diagnostic = stderr.read_bytes()
    run = {"command": list(map(str, command)), "process_started": True,
           "exit_code": child.returncode, "timed_out": timed_out,
           "wall_seconds": round(time.monotonic()-started, 6),
           "stdout_sha256": digest(captured), "stderr_sha256": digest(diagnostic),
           "stdout_bytes": len(captured), "stderr_bytes": len(diagnostic)}
    (output/(name+".process.json")).write_text(json.dumps(run, indent=2, sort_keys=True)+"\n")
    checker.require(not timed_out, "native process timed out: " + name)
    checker.require(len(captured) <= checker.MAX_CERTIFICATE_BYTES, "native output exceeds byte cap")
    return captured, run


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--build-receipt", type=Path)
    args = parser.parse_args()
    output = args.output
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "calendar_general_frontend_review_v1", "pass": False,
              "native_execution": True, "Lean_execution": False,
              "scientific_source_admission": False}
    try:
        binary_before = digest(args.binary.read_bytes())
        binary = output/"calendar-solver"
        binary.write_bytes(args.binary.read_bytes())
        binary.chmod(0o500)
        checker.require(digest(binary.read_bytes()) == binary_before, "staged executable identity mismatch")
        source_before = {name: digest((DESIGN/name).read_bytes()) for name in MODULES}
        for name in MODULES + [Path(__file__).name, "review_calendar_helper.py"]:
            (output/name).write_bytes((DESIGN/name).read_bytes())
        if args.build_receipt:
            receipt = args.build_receipt.read_bytes()
            (output/"BUILD-RECEIPT.json").write_bytes(receipt)
            report["build_receipt_sha256"] = digest(receipt)
        cases = []
        inputs = {}
        frames = {}
        for requests, old_output in [("calendar-fixture-freeze-1", "calendar-rust-review-1"),
                                     ("calendar-serial-hybrid-fixture-freeze-1", "calendar-serial-hybrid-rust-review-1")]:
            for path in sorted((DESIGN/"evidence"/requests).glob("*.request.json")):
                name = path.name.removesuffix(".request.json")
                raw = path.read_bytes()
                stored = output/(name+".request.json")
                stored.write_bytes(raw)
                expected = project((DESIGN/"evidence"/old_output/(name+".rust.stdout")).read_bytes())
                expected_raw = checker.canonical_json(expected)
                (output/(name+".expected.json")).write_bytes(expected_raw)
                mode = "stdin" if len(cases) % 2 == 0 else "file"
                command = [str(binary.resolve()), "solve"]
                if mode == "file":
                    command += ["--request", str(stored.resolve())]
                actual, run = launch(command, output, name, raw if mode == "stdin" else None)
                checked = checker.verify_certificate(raw, actual, run["exit_code"])
                checker.require(actual == expected_raw, "native canonical result differs from frozen producer: " + name)
                record = {"name": name, "mode": mode, "status": checked["status"], "pass": True,
                          "full_view_rows": checked.get("full_view_rows", 0), "process": run}
                cases.append(record)
                report["cases"] = cases
                (output/(name+".check.json")).write_bytes(checker.canonical_json(checked))
                inputs[name], frames[name] = raw, expected
        parser_cases = []
        base_name = "parallelCommonCalendar"
        base = checker.parse_request(inputs[base_name])
        compact = checker.canonical_json(base)
        refusal = checker.canonical_json({"schema": checker.SCHEMA, "status": "ERROR", "error": "INVALID_REQUEST"})
        bad_inputs = {
            "duplicateTopKey": compact[:-2]+b',"ages":[]}\n',
            "duplicateNestedKey": compact.replace(b'"root":0', b'"root":0,"root":0'),
            "floatCount": compact.replace(b'"vertices":5', b'"vertices":5.0'),
            "exponentCount": compact.replace(b'"vertices":5', b'"vertices":5e0'),
            "boolCount": compact.replace(b'"vertices":5', b'"vertices":true'),
            "negativeCount": compact.replace(b'"vertices":5', b'"vertices":-5'),
            "overflowCount": compact.replace(b'"vertices":5', b'"vertices":18446744073709551616'),
            "uint64maxVertices": compact.replace(b'"vertices":5', b'"vertices":18446744073709551615'),
            "nonfinite": b'{"ages":NaN}', "invalidUtf8": b'{"ages":\xff}',
            "requestByteCap": b" "*(checker.MAX_REQUEST_BYTES+1),
            "deepInput": b'{"x":'+b'['*130+b'0'+b']'*130+b'}',
            "trailingJson": compact+b'{}\n'}
        for name, mutate in [
            ("unknownField", lambda r: r.update(extra=0)),
            ("unknownNestedField", lambda r: r["context"].update(extra=0)),
            ("unknownProviderField", lambda r: r["provider_limits"]["epoch"].update(extra=0)),
            ("wrongEdgeArity", lambda r: r["context"]["edges"][0].append(0)),
            ("wrongModeArity", lambda r: r["common"].append(False)),
            ("unreducedRational", lambda r: r["inverse_rates"].__setitem__(0, "2/2")),
            ("rationalLeadingZero", lambda r: r["inverse_rates"].__setitem__(0, "1/01")),
            ("zeroInverseWithZeroCompilerCaps", lambda r: (r["inverse_rates"].__setitem__(0, "0/1"),r["compiler_limits"].update(word_length=0,slots=0,variables=0)))]:
            bad = copy.deepcopy(base);mutate(bad)
            bad_inputs[name] = checker.canonical_json(bad)
        for name, raw in bad_inputs.items():
            (output/(name+".request.json")).write_bytes(raw)
            actual, run = launch([str(binary.resolve()), "solve"], output, name, raw)
            checked = checker.verify_certificate(raw, actual, run["exit_code"])
            checker.require(actual == refusal and checked["status"] == "REFUSED", "parser failed refusal: " + name)
            parser_cases.append({"name": name, "pass": True, "process": run})
            report["parser_controls"] = parser_cases
        semantic = []
        variants = {"semanticMinusZero": compact.replace(b'"root":0', b'"root":-0'),
                    "whitespaceAndKeyOrder": json.dumps(base, indent=3).encode()+b"\n"}
        nondefault = copy.deepcopy(base)
        for fields in nondefault["provider_limits"].values():
            for key in fields:
                fields[key] += 1
        variants["nondefaultSuccessfulProviderCaps"] = checker.canonical_json(nondefault)
        high_labels = copy.deepcopy(base);high_labels["context"]["global_labels"] = [0, 2**63, 2**64-1]
        variants["uint64GlobalEmbedding"] = checker.canonical_json(high_labels)
        for name, raw in variants.items():
            request = checker.parse_request(raw)
            # Reuse the known table, changing only fields whose semantics are
            # noncomputational metadata or successful inner work limits.
            expected = copy.deepcopy(frames[base_name])
            expected["request"] = request
            expected["word_result"]["request"]["context"] = request["context"]
            actual, run = launch([str(binary.resolve())], output, name, raw)
            checked = checker.verify_certificate(raw, actual, run["exit_code"])
            checker.require(actual == checker.canonical_json(expected) and checked["formal_table_checked"],
                            "semantic input variant changed full table: " + name)
            (output/(name+".request.json")).write_bytes(raw)
            (output/(name+".check.json")).write_bytes(checker.canonical_json(checked))
            semantic.append({"name": name, "pass": True, "process": run})
        # The native checker has a declared replay role. Independent semantic
        # checks above remain mandatory even when native replay accepts.
        native_controls = []
        request_path = output/(base_name+".request.json")
        good_path = output/(base_name+".stdout")
        forged = copy.deepcopy(frames[base_name]);forged["agenda"]["physical_coordinates"][0]["argument"] = "1/7"
        forged_path = output/"forged-native-check.result.json";forged_path.write_bytes(checker.canonical_json(forged))
        whitespace_path = output/"noncanonical-native-check.result.json"
        whitespace_path.write_text(json.dumps(frames[base_name], indent=2)+"\n")
        for name, certificate, accept in [("nativeGoodReplay", good_path, True),
                                           ("nativeForgedReplay", forged_path, False),
                                           ("nativeNoncanonicalReplay", whitespace_path, False)]:
            actual, run = launch([str(binary.resolve()), "check", "--request", str(request_path.resolve()),
                                  "--certificate", str(certificate.resolve())], output, name)
            expected = {"schema": "source_calendar_check_v1", "status": "ACCEPT" if accept else "REJECT"}
            checker.require(actual == checker.canonical_json(expected) and run["exit_code"] == (0 if accept else 1),
                            "native replay framing/status differs: " + name)
            native_controls.append({"name": name, "pass": True, "independent_algorithm": False, "process": run})
        source_after = {name: digest((DESIGN/name).read_bytes()) for name in MODULES}
        checker.require(source_after == source_before and digest(args.binary.read_bytes()) == binary_before
                        and digest(binary.read_bytes()) == binary_before, "measured input identity changed")
        report.update(cases_passed=len(cases), full_view_rows=sum(c["full_view_rows"] for c in cases),
                      semantic_controls=semantic, native_replay_controls=native_controls,
                      source_before=source_before, source_after=source_after,
                      binary_before=binary_before, binary_after=digest(args.binary.read_bytes()),
                      staged_binary_sha256=digest(binary.read_bytes()),
                      reviewer_sha256=digest(Path(__file__).read_bytes()),
                      qualification="Actual general-input frontend and independent coefficient checks. Native checker is replay. No Lean/compiler rerun, RC1 executable promotion, source admission or complete solver claim.")
        report["pass"] = True
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        (output/"RECEIPT.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"pass": report["pass"], "cases": report["cases_passed"],
                      "views": report["full_view_rows"], "parser_controls": len(report["parser_controls"])}))


if __name__ == "__main__":
    main()
