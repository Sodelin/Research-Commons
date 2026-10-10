#!/usr/bin/env python3
"""Saved-output acceptance and adversarial controls for calendar_check.py.

No native producer or compiler is rerun. Frozen private outputs are projected
to the public envelope and checked using the independently pinned references.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

import calendar_check as checker

DESIGN = Path(__file__).resolve().parent
MODULES = ["certificate_check.py", "chart_check.py", "population_oracle.py", "epoch_oracle.py",
           "boundary_oracle.py", "source_word_oracle.py", "source_calendar_oracle.py", "calendar_check.py"]
OLD_HASHES = [
    "ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24",
    "3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a",
    "216d83a844019f115de1dfa19c12827e0570348181d380f1435dc6ee646748ff",
    "da66bf78d538d7acdc8d67b560b3d7fe95fd987d614cf34ffd3803c03c8235bd",
    "0d85747a1f58c4c78b4aa7b0a8f671cd145b7a5f4ce990f9ed33df6b4766db29",
    "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102",
    "3f01def72cbd1b999099f713764e97941753a12349bcf4e23f3e7d90b63de27c"]


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def project(raw):
    if not raw:
        return {"schema": checker.SCHEMA, "status": "ERROR", "error": "INVALID_REQUEST"}
    value = json.loads(raw)
    value.pop("fixture")
    value["schema"] = checker.SCHEMA
    if "word_result" in value:
        value["word_result"] = checker.public_word(value["word_result"])
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output
    output.mkdir(parents=True, exist_ok=False)
    result = {"schema": "calendar_public_helper_saved_review_v1", "pass": False,
              "native_execution": False, "Lean_execution": False,
              "scope": "SAVED_PRIVATE_ENVELOPE_PROJECTION_AND_INDEPENDENT_PUBLIC_CHECKER"}
    try:
        before = {name: digest((DESIGN/name).read_bytes()) for name in MODULES}
        for name, expected in zip(MODULES, OLD_HASHES):
            checker.require(before[name] == expected, "frozen reference source changed: " + name)
        for name in MODULES:
            (output/name).write_bytes((DESIGN/name).read_bytes())
        (output/Path(__file__).name).write_bytes(Path(__file__).read_bytes())
        cases = []
        saved = {}
        old_receipts = {}
        for inputs, evidence in [("calendar-fixture-freeze-1", "calendar-rust-review-1"),
                                 ("calendar-serial-hybrid-fixture-freeze-1", "calendar-serial-hybrid-rust-review-1")]:
            upstream = DESIGN/"evidence"/evidence/"RECEIPT.json"
            old_receipts[evidence] = digest(upstream.read_bytes())
            (output/(evidence+"-RECEIPT.json")).write_bytes(upstream.read_bytes())
            for path in sorted((DESIGN/"evidence"/inputs).glob("*.request.json")):
                name = path.name.removesuffix(".request.json")
                raw_request = path.read_bytes()
                source = DESIGN/"evidence"/evidence/(name+".rust.stdout")
                source_raw = source.read_bytes()
                frame = project(source_raw)
                raw_result = checker.canonical_json(frame)
                code = 0 if frame["status"] == "TABLE" else 2 if frame["status"] == "UNKNOWN" else 1
                checked = checker.verify_certificate(raw_request, raw_result, code)
                (output/(name+".request.json")).write_bytes(raw_request)
                (output/(name+".result.json")).write_bytes(raw_result)
                (output/(name+".check.json")).write_bytes(checker.canonical_json(checked))
                cases.append({"name": name, "status": checked["status"],
                    "full_view_rows": checked.get("full_view_rows", 0), "source_stdout": str(source),
                    "source_stdout_sha256": digest(source_raw), "request_sha256": digest(raw_request),
                    "projected_result_sha256": digest(raw_result), "exit_code": code})
                saved[name] = (raw_request, frame)
        controls = []
        base_raw, base = saved["parallelCommonCalendar"]

        def rejected(name, raw, frame, exit_code, *, serialized=None):
            encoded = checker.canonical_json(frame) if serialized is None else serialized
            try:
                checker.verify_certificate(raw, encoded, exit_code)
            except (ValueError, UnicodeError, OverflowError, TypeError, KeyError, IndexError):
                controls.append(name)
            else:
                raise ValueError("checker accepted forged " + name)

        mutations = [
            ("scientific gate promoted", lambda x: x.update(source_admission_verified=True)),
            ("parallel occurrence omitted", lambda x: x["agenda"]["cohorts"][2]["exits"].pop()),
            ("shared exposure wrong", lambda x: x["agenda"]["physical_coordinates"][0].update(argument="1/7")),
            ("original gamma complemented", lambda x: x["agenda"]["physical_coordinates"][-1].update(argument="2/3")),
            ("word work understated", lambda x: x["word_result"]["work"].update(queries=0)),
            ("register erased", lambda x: x["word_result"]["rows"][0]["view"].update(register=[])),
            ("literal witness register forged", lambda x: x["word_result"]["rows"][0]["witness"]["register"].reverse()),
            ("full destination omitted", lambda x: x["word_result"]["rows"].pop()),
            ("full destination duplicated", lambda x: x["word_result"]["rows"].append(copy.deepcopy(x["word_result"]["rows"][0]))),
            ("bool used as exponent", lambda x: x["word_result"]["rows"][0]["coefficients"][0][0].__setitem__(0, False)),
            ("unreduced coefficient", lambda x: x["word_result"]["rows"][0]["coefficients"][0].__setitem__(1, "2/2")),
            ("private fixture field leaked", lambda x: x.update(fixture="private"))]
        for name, mutate in mutations:
            forged = copy.deepcopy(base)
            mutate(forged)
            rejected(name, base_raw, forged, 0)
        # Keep formal mass one while altering a topology's polynomial weight.
        forged = copy.deepcopy(base)
        a, b = forged["word_result"]["rows"][:2]
        term = a["coefficients"][0][0]
        def shift(row, delta):
            polynomial = {tuple(p): checker.calendar.rational(q) for p, q in row["coefficients"]}
            polynomial[tuple(term)] = polynomial.get(tuple(term), 0) + delta
            row["coefficients"] = [[list(p), checker.calendar.ref.epoch.qwire(q)] for p, q in sorted(polynomial.items()) if q]
        shift(a, 1); shift(b, -1)
        rejected("balanced full coefficient forgery", base_raw, forged, 0)
        rejected("TABLE with UNKNOWN exit", base_raw, base, 2)
        rejected("noncanonical output whitespace", base_raw, base, 0,
                 serialized=json.dumps(base, sort_keys=True).encode()+b"\n")
        unknown_raw, unknown = saved["epochCallLimit"]
        for name, mutate in [
            ("UNKNOWN changed provider cap", lambda x: x["word_result"]["limit"].update(cap=1)),
            ("UNKNOWN zero excess", lambda x: x["word_result"]["limit"].update(required=0)),
            ("UNKNOWN wrong population", lambda x: x.update(consumer_population=["E", 999])),
            ("UNKNOWN wrong stage", lambda x: x["word_result"]["limit"].update(stage=0)),
            ("UNKNOWN partial rows", lambda x: x["word_result"].update(rows=[]))]:
            forged = copy.deepcopy(unknown);mutate(forged)
            rejected(name, unknown_raw, forged, 2)
        rejected("UNKNOWN with successful exit", unknown_raw, unknown, 0)
        valid_request = checker.parse_request(base_raw)
        refusal = {"schema": checker.SCHEMA, "status": "ERROR", "error": "INVALID_REQUEST"}
        invalid_inputs = {
            "duplicate root key": checker.canonical_json(valid_request)[:-2]+b',"ages":[]}\n',
            "invalid UTF8": b"{\xff}", "nonfinite JSON": b'{"x":NaN}',
            "float count": checker.canonical_json(valid_request).replace(b'"vertices":5', b'"vertices":5.0'),
            "exponent count": checker.canonical_json(valid_request).replace(b'"vertices":5', b'"vertices":5e0'),
            "bool count": checker.canonical_json(valid_request).replace(b'"vertices":5', b'"vertices":true'),
            "raw request cap": b" "*(checker.MAX_REQUEST_BYTES+1),
            "JSON depth cap": b'{"x":'+b'['*65+b'0'+b']'*65+b'}'}
        for name, raw in invalid_inputs.items():
            checked = checker.verify_certificate(raw, checker.canonical_json(refusal), 1)
            checker.require(checked["status"] == "REFUSED", "invalid JSON not refused: " + name)
            controls.append(name)
        for name, mutate in [("unknown input field", lambda x: x.update(extra=0)),
                             ("unknown nested field", lambda x: x["context"].update(extra=0)),
                             ("unreduced input rational", lambda x: x["inverse_rates"].__setitem__(0, "2/2"))]:
            bad = copy.deepcopy(valid_request);mutate(bad)
            checked = checker.verify_certificate(checker.canonical_json(bad), checker.canonical_json(refusal), 1)
            checker.require(checked["status"] == "REFUSED", name + " was admitted")
            controls.append(name)
        # Counts use semantic integers; successful provider caps are not falsely
        # rejected merely because the old fixture-only checker lacked counters.
        semantic_controls = []
        altered = copy.deepcopy(base)
        for kind, fields in altered["request"]["provider_limits"].items():
            for field in fields:
                fields[field] += 1
        checked = checker.verify_certificate(checker.canonical_json(altered["request"]), checker.canonical_json(altered), 0)
        checker.require(checked["formal_table_checked"] and not checked["provider_work_checked"],
                        "nondefault TABLE changed provider work qualification")
        semantic_controls.append("nondefault provider caps / no provider counting claim")
        zero_raw = checker.canonical_json(valid_request).replace(b'"root":0', b'"root":-0')
        checked = checker.verify_certificate(zero_raw, checker.canonical_json(base), 0)
        checker.require(checked["formal_table_checked"], "semantic -0 was not accepted")
        semantic_controls.append("semantic integer -0 normalizes to zero")
        framed = copy.deepcopy(unknown);framed["word_result"]["limit"]["required"] = 17
        checked = checker.verify_certificate(unknown_raw, checker.canonical_json(framed), 2)
        checker.require(not checked["provider_exhaustion_verified"] and not checked["formal_table_checked"],
                        "provider UNKNOWN was promoted")
        semantic_controls.append("provider UNKNOWN remains framing-only")
        after = {name: digest((DESIGN/name).read_bytes()) for name in MODULES}
        checker.require(after == before, "checker source closure changed during review")
        result.update({"pass": True, "cases": cases, "cases_passed": len(cases),
            "full_view_rows": sum(c["full_view_rows"] for c in cases), "adversarial_controls": controls,
            "semantic_scope_controls": semantic_controls, "closure_before": before, "closure_after": after,
            "upstream_receipts": old_receipts, "reviewer_sha256": digest(Path(__file__).read_bytes()),
            "qualification": "Successful TABLE coefficients/agenda/witnesses/logical word work checked independently. Provider exhaustion framing only. Generic native parser/adapter execution pending."})
    except Exception as error:
        result["error"] = str(error)
        raise
    finally:
        (output/"RECEIPT.json").write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
    print(json.dumps({"pass": result["pass"], "cases": result["cases_passed"],
                      "full_view_rows": result["full_view_rows"], "controls": len(result["adversarial_controls"])}))


if __name__ == "__main__":
    main()
