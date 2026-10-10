#!/usr/bin/env python3
"""Independently compare saved actual Lean outputs with saved Rust tables.

This reviewer has no subprocess calls and invokes no compiler or producer.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
import types

PACKET = Path(__file__).resolve().parents[2]
PREP = PACKET / "rust/evidence/calendar-original-saved-output-preparation-1"
PREP_SHA = "321f3f4950b7bde7df0937c397ba4fd03a7e534cd2031b39f47480118833475f"
LEAN_RECEIPT_SHA = "5bfc97701f7c0313bdcbf8bf6eb619ea1ccebd4d742323ff9f140d7ec487dc04"
QUALIFICATION_SHA = "137266eb7ac98ec0e790c53efd06e87bca4577506a1eda155f8123fc8b4a5ee5"
CONFIG_SHA = "4de40921194dad34ba5ad77e165af0b9daf2ed8396224189af181a3eb00baf9e"
KERNEL_SHA = "7dfecc253e3d382497b9d67cb5b50c7721744406bdfc5ca49358e1a239dee4d2"
NAMES = ("twoTipCalendar", "serialNegativeTips", "parallelCommonCalendar")
MODULES = ("certificate_check", "chart_check", "population_oracle", "epoch_oracle",
           "boundary_oracle", "source_word_oracle", "source_calendar_oracle", "calendar_check",
           "review_word_compiled_fixtures", "review_calendar_compiled_fixtures")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True, allow_nan=False) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-evidence", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    observed = {}

    def observe(path, expected=None, copied=None):
        raw = path.read_bytes()
        digest = sha(raw)
        require(expected is None or expected == digest, "pin drift: " + str(path))
        observed[str(path.resolve())] = digest
        if copied is not None:
            dest = out / copied
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(raw)
        return raw

    observe(Path(__file__).resolve(), copied="REVIEW.py")
    prep = json.loads(observe(PREP / "RECEIPT.json", PREP_SHA, "PREPARATION-RECEIPT.json"))
    require(prep["status"] == "READY_PENDING_ACTUAL_LEAN_OUTPUTS"
            and prep["saved_rust_review_pass"] is True and prep["full_view_rows"] == 38
            and prep["terms"] == 66 and len(prep["forgeries_rejected"]) == 8,
            "saved Rust preparation was not accepted")
    inventory = json.loads(observe(PREP / "ARTIFACTS.json", copied="PREPARATION-ARTIFACTS.json"))
    for entry in inventory["files"]:
        observe(PREP / entry["path"], entry["sha256"])
    modules = {}
    for name in MODULES:
        path = PREP / "reference" / (name + ".py")
        raw = observe(path, copied="reference/" + path.name)
        module = types.ModuleType(name)
        # Complete immutable preparation origins, not mutable design paths.
        module.__file__ = str(path)
        sys.modules[name] = module
        exec(compile(raw, str(path), "exec"), module.__dict__)
        modules[name] = module
    epoch = modules["epoch_oracle"]
    direct = modules["review_word_compiled_fixtures"]
    reviewer = modules["review_calendar_compiled_fixtures"]
    base = args.lean_evidence.resolve()
    lr = epoch.parse_json(observe(base / "RECEIPT.json", LEAN_RECEIPT_SHA, "lean/RECEIPT.json"))
    qual = epoch.parse_json(observe(base / "EXECUTION-QUALIFICATION.json", QUALIFICATION_SHA,
                                   "lean/EXECUTION-QUALIFICATION.json"))
    cfg = epoch.parse_json(observe(base / "LEAN-EXECUTION-CONFIG.json", CONFIG_SHA,
                                  "lean/LEAN-EXECUTION-CONFIG.json"))
    require(lr["pass"] is True and lr["cases_total"] == lr["cases_passed"] == 3
            and lr["languages_executed"] == ["lean"] and lr["full_view_rows_total"] == 38
            and lr["pins_before"] == lr["pins_after"], "actual Lean execution receipt changed")
    require(qual["driver_receipt_sha256"] == LEAN_RECEIPT_SHA
            and qual["compiled_lean_evaluator_processes"] == 3
            and qual["new_native_calendar_processes"] == 0
            and qual["specific_literal_phase_or_physical_PMF_instances_accepted"] is False,
            "actual execution/physical qualification differs")
    require(cfg["execution_mode"] == "compiled_lean_evaluator_not_standalone_elf"
            and tuple(cfg["fixtures"]) == NAMES and cfg["closure_modules"] == 200
            and cfg["owned_axioms"] == [] and cfg["nonstandard_axiom_rows"] == [],
            "execution configuration is not the accepted exact fixture context")
    for path, digest in lr["pins_before"].items():
        observe(Path(path), digest)
    cert_path = Path(qual["compiler_kernel_fixture_certificate"])
    kernel = epoch.parse_json(observe(cert_path, KERNEL_SHA, "lean/KERNEL-CERTIFICATE.json"))
    require(qual["compiler_kernel_fixture_certificate_sha256"] == KERNEL_SHA
            and kernel["kernel_checking"] is True and kernel["trust_level"] == 0
            and kernel["compiler_and_native_final_stable"] is True
            and kernel["source_pins"] == cfg["source_pins"], "kernel/source/runtime binding changed")
    kernel_base = PACKET / "lean" / kernel["evidence"]
    audit_summaries = []
    for target, report in kernel["targets"].items():
        require(report["status"] == "PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT"
                and report["source_and_import_bindings_stable"] is True
                and report["missing_modules"] == report["owned_axioms"] == report["nonstandard_axiom_rows"] == [],
                "kernel target is not a complete accepted audit")
        raw = gzip.decompress(observe(kernel_base / report["audit_distribution"],
                                      copied="lean/" + Path(report["audit_distribution"]).parent.parent.name + "-AUDIT.json.gz"))
        require(sha(raw) == report["audit_raw_sha256"], "complete owned audit raw identity changed")
        audit = epoch.parse_json(raw)
        require(audit["declaration_count"] == report["owned_declarations"]
                and audit["theorem_declaration_count"] == report["owned_theorems"]
                and audit["missing_modules"] == audit["owned_axioms"] == audit["nonstandard_axiom_rows"] == [],
                "complete owned audit summary differs")
        audit_summaries.append({"target": target, "modules": report["closure_modules"],
                                "declarations": audit["declaration_count"],
                                "theorems": audit["theorem_declaration_count"],
                                "raw_sha256": sha(raw)})
    imported_path = PACKET / "lean" / cfg["evidence"] / "ACTUAL-IMPORTED-ARTIFACTS.json"
    imported_raw = observe(imported_path)
    (out / "lean/ACTUAL-IMPORTED-ARTIFACTS.json.gz").write_bytes(gzip.compress(imported_raw, mtime=0))
    imported = epoch.parse_json(imported_raw)
    owned = [row for row in imported if row["module"] in cfg["source_pins"]]
    require(len(imported) == cfg["actual_imported_artifact_count"] == 27159
            and {row["module"] for row in owned} == set(cfg["source_pins"]),
            "actual imported source context coverage differs")
    for row in owned:
        raw = observe(Path(row["path"]), row["sha256"])
        require(len(raw) == row["bytes"], "owned imported artifact size changed")
    source_store = Path(cfg["workdir"]) / "source-store"
    for name, digest in cfg["source_pins"].items():
        observe(source_store / (digest + ".lean"), digest)
    for name in ("G7OriginalCompletedCalendarFixture", "G7OriginalCompletedCalendarFixtureMain"):
        digest = cfg["source_pins"][name]
        observe(source_store / (digest + ".lean"), digest, "lean/" + name + ".lean")
    driver = observe(base / "LEAN-DRIVER.lean", cfg["driver_sha256"], "lean/LEAN-DRIVER.lean")
    require(sha(driver) == kernel["targets"][next(t for t in kernel["targets"] if t.endswith("FixtureMain"))]["aggregate_source_sha256"],
            "evaluator driver differs from the checked aggregate")
    cases = []
    for prepared, actual_case in zip(prep["cases"], lr["cases"]):
        name = prepared["fixture"]
        require(actual_case["fixture"] == name and actual_case["pass"] is True
                and actual_case["errors"] == [], "paired fixture list/status differs")
        run = actual_case["runs"]["lean"]
        require(run["process_started"] is True and run["exit_code"] == 0
                and run["timed_out"] is False and run["execution_mode"] == cfg["execution_mode"],
                "Lean evaluator did not actually complete")
        expected_cmd = [*cfg["command_prefix"][:-1], str(base / "LEAN-DRIVER.lean"), name]
        require(run["command"] == expected_cmd, "evaluator command differs from exact config")
        lraw = observe(base / (name + ".lean.stdout"), run["stdout_sha256"], "lean/" + name + ".stdout")
        err = observe(base / (name + ".lean.stderr"), run["stderr_sha256"], "lean/" + name + ".stderr")
        require(err == b"" and len(lraw) <= 4 * 1024 * 1024, "evaluator stderr/frame differs")
        request = observe(base / (name + ".calendar-request.json"), prepared["request_sha256"],
                          "inputs/" + name + ".request.json")
        require(request == reviewer.origin(name).read_bytes(), "exact original request differs")
        rust_raw = observe(PREP / (name + ".rust.projected.json"), copied="rust/" + name + ".projected.json")
        rust = epoch.parse_json(rust_raw)
        lean = epoch.parse_json(lraw)
        wanted, internal, _ = reviewer.expected(name)
        checked = direct.check_direct(lean, wanted, internal)
        require(checked == prepared["coefficient_review"], "complete original view/term counts differ")
        key = lambda rows: {epoch.exact_json(row["view"]): epoch.exact_json(row["coefficients"]) for row in rows}
        require(key(lean["rows"]) == key(rust["rows"]), "actual complete Lean/Rust coefficients differ")
        require(all(epoch.exact_json(lean[k]) == epoch.exact_json(rust[k])
                    for k in ("schema", "fixture", "request", "variables")), "original bank/request envelope differs")
        cases.append({"fixture": name, "status": "PASS", "request_sha256": prepared["request_sha256"],
                      "rust_original_table_sha256": prepared["table_sha256"], "Lean_stdout_sha256": sha(lraw),
                      "review": checked, "actual_complete_coefficient_maps_equal": True,
                      "saved_Rust_native_execution_reused": True, "Lean_execution_by_this_reviewer": False})
    after = {path: sha(Path(path).read_bytes()) for path in observed}
    require(observed == after, "source/artifact/evidence changed during paired review")
    result = {"schema": "original_completed_calendar_saved_Lean_Rust_review_v1", "status": "PASS",
              "observed_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
              "cases": cases, "cases_passed": len(cases), "full_view_rows": 38, "terms": 66,
              "kernel_audits": audit_summaries, "exact_context_source_count": len(cfg["source_pins"]),
              "owned_imported_artifacts_rehashed": len(owned), "import_manifest_records": len(imported),
              "forgery_controls_reused_from_exact_pinned_preparation": prep["forgeries_rejected"],
              "identities_before": observed, "identities_after": after,
              "actual_Lean_evaluator_execution_receipt_sha256": LEAN_RECEIPT_SHA,
              "saved_Rust_application_receipt_sha256": "a8b95013a5a8b2dd9f07c97ef8ea3b5db1a58272380e1f733f9383296c4cd578",
              "native_or_Lean_processes_started_by_this_reviewer": 0, "old117_or_broader_suites_rerun": False,
              "full_external_native_import_reaudit": False, "Lean_standalone_ELF_claim": False,
              "specific_physical_calendar_phase_instances_checked": False,
              "general_native_calendar_refinement_claim": False, "source_admission_verified": False,
              "scope": "Exact three original completed literal natural-word tables; all38 ordered destinations/66coefficients and reachable canonical witnesses. Specific finite physical calendar phase instances remain pending; source-parser/admission and all-source closure are not promoted."}
    dump(out / "RECEIPT.json", result)
    print(json.dumps({k: result[k] for k in ("status", "cases_passed", "full_view_rows", "terms")}, sort_keys=True))


if __name__ == "__main__":
    main()
