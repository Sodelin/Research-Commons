#!/usr/bin/env python3
"""Prepare an independently pinned saved-Rust comparator; executes no producer."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
import types

PACKET = Path(__file__).resolve().parents[2]
DESIGN = PACKET / "design"
SAVED = PACKET / "rust/evidence/calendar-completed-application-1"
SAVED_SHA = "a8b95013a5a8b2dd9f07c97ef8ea3b5db1a58272380e1f733f9383296c4cd578"
PINS = {
    "certificate_check.py": "ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24",
    "chart_check.py": "3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a",
    "population_oracle.py": "216d83a844019f115de1dfa19c12827e0570348181d380f1435dc6ee646748ff",
    "epoch_oracle.py": "da66bf78d538d7acdc8d67b560b3d7fe95fd987d614cf34ffd3803c03c8235bd",
    "boundary_oracle.py": "0d85747a1f58c4c78b4aa7b0a8f671cd145b7a5f4ce990f9ed33df6b4766db29",
    "source_word_oracle.py": "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102",
    "source_calendar_oracle.py": "3f01def72cbd1b999099f713764e97941753a12349bcf4e23f3e7d90b63de27c",
    "calendar_check.py": "6190bcd125c51d2e133b571ecc9fe08298fe5a731dc6536459f66446f0ae29bb",
    "review_word_compiled_fixtures.py": "f0763dadfe55ba1f6ba40e2f545637966082347226c1796eeffea8cf4e6691c8",
    "review_calendar_compiled_fixtures.py": "939d8b06433b2b328dad6c55a64624aefd91873b0e3a1a67eb14827758128a8b",
}
NAMES = ("twoTipCalendar", "serialNegativeTips", "parallelCommonCalendar")


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    observed = {}

    def capture(origin, relative, pin=None):
        raw = origin.read_bytes()
        actual = sha(raw)
        require(pin is None or pin == actual, "input pin changed: " + str(origin))
        observed[str(origin)] = actual
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        return raw

    capture(Path(__file__).resolve(), "REVIEW.py")
    modules = {}
    for name, pin in PINS.items():
        raw = capture(DESIGN / name, "reference/" + name, pin)
        module = types.ModuleType(Path(name).stem)
        module.__file__ = str(out / "reference" / name)
        sys.modules[module.__name__] = module
        exec(compile(raw, module.__file__, "exec"), module.__dict__)
        modules[name] = module
    direct = modules["review_word_compiled_fixtures.py"]
    reviewer = modules["review_calendar_compiled_fixtures.py"]
    production = modules["calendar_check.py"]
    epoch = modules["epoch_oracle.py"]
    receipt_raw = capture(SAVED / "RECEIPT.json", "saved-application/RECEIPT.json", SAVED_SHA)
    saved = epoch.parse_json(receipt_raw)
    require(saved["status"] == "PASS" and saved["cases_passed"] == 3
            and saved["full_view_rows"] == 38 and saved["Lean_execution"] is False,
            "saved Rust application receipt is not the accepted three-case result")
    cases = []
    for case in saved["cases"]:
        name = case["fixture"]
        require(name in NAMES and case["status"] == "PASS", "saved fixture/status differs")
        origin = DESIGN / "evidence/calendar-fixture-freeze-1" / (name + ".request.json")
        raw = capture(origin, "reference/evidence/calendar-fixture-freeze-1/" + origin.name,
                      case["request_sha256"])
        require((SAVED / "inputs" / origin.name).read_bytes() == raw,
                "saved application request differs from the original frozen input")
        observed[str(SAVED / "inputs" / origin.name)] = sha(raw)
        component = SAVED / "cases" / name / "component"
        table = capture(component / "TABLE.json", "saved-application/" + name + "/TABLE.json",
                        case["table_sha256"])
        require((component / "REQUEST.json").read_bytes() == raw, "staged request differs")
        observed[str(component / "REQUEST.json")] = sha(raw)
        for label in ("solver", "checker", "reference-checker"):
            for suffix in ("stdout", "stderr", "execution.json"):
                p = component / "component" / (label + "." + suffix)
                capture(p, "saved-application/" + name + "/" + p.name)
            record = epoch.parse_json((component / "component" / (label + ".execution.json")).read_bytes())
            require(record["process_started"] is True and record["exit_code"] == 0
                    and record["timed_out"] is False, "saved process did not complete: " + label)
            for stream in ("stdout", "stderr"):
                require(sha((component / "component" / (label + "." + stream)).read_bytes()) ==
                        record[stream + "_sha256"], "saved process stream identity changed")
        require((component / "component/solver.stdout").read_bytes() == table,
                "saved producer output differs from retained table")
        helper = production.verify_certificate(raw, table, 0)
        require(helper["formal_table_checked"] is True and helper["independent_all_coefficients_checked"] is True,
                "production full coefficient checker did not accept table")
        wanted, internal, binding = reviewer.expected(name)
        word = epoch.parse_json(table)["word_result"]
        actual = {"schema": wanted["schema"], "fixture": name, "request": word["request"],
                  "variables": word["variables"], "rows": word["rows"]}
        result = direct.check_direct(actual, wanted, internal)
        require(result["full_view_rows"] == case["full_view_rows"]
                and result["terms"] == case["terms"], "saved view/term cardinality changed")
        dump(out / (name + ".rust.projected.json"), actual)
        dump(out / (name + ".reference.expected.json"), wanted)
        dump(out / (name + ".calendar-binding.json"), binding)
        dump(out / (name + ".helper-review.json"), helper)
        cases.append({"fixture": name, "request_sha256": sha(raw), "table_sha256": sha(table),
                      "coefficient_review": result, "saved_native_execution_reused": True,
                      "new_native_process_started": False})
    require(tuple(case["fixture"] for case in cases) == NAMES, "saved fixture order/list changed")
    rejected = reviewer.controls()
    require(len(rejected) == 8, "comparator's eight adversarial controls not all rejected")
    after = {path: sha(Path(path).read_bytes()) for path in observed}
    require(after == observed, "original source or saved evidence changed during review")
    result = {
        "schema": "original_completed_calendar_saved_output_preparation_v1",
        "status": "READY_PENDING_ACTUAL_LEAN_OUTPUTS", "saved_rust_review_pass": True,
        "original_Lean_comparison_completed": False,
        "observed_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "cases": cases, "full_view_rows": sum(c["coefficient_review"]["full_view_rows"] for c in cases),
        "terms": sum(c["coefficient_review"]["terms"] for c in cases),
        "forgeries_rejected": rejected, "sources_and_evidence_before": observed,
        "sources_and_evidence_after": after, "native_solver_rerun": False,
        "Lean_compiler_or_evaluator_called": False, "public117_or_broader_suites_rerun": False,
        "general_native_calendar_refinement_claim": False, "source_admission_verified": False,
        "scope": "Three exact original request identities; complete selected-view coefficients, reached literal witnesses and population/register-preserving readout. Actual original Lean evaluator output and its authenticated kernel context remain pending.",
    }
    dump(out / "RECEIPT.json", result)
    print(json.dumps({k: result[k] for k in ("status", "full_view_rows", "terms")}, sort_keys=True))


if __name__ == "__main__":
    main()
