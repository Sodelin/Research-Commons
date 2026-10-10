#!/usr/bin/env python3
"""Review preserved calendar application evidence; do not rerun native tests."""
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
EVIDENCE = PACKET / "quality/evidence/application-calendar-integration-20261010T1505Z"
FALSE_GATES = (
    "source_admission_verified", "physical_survival_image_verified",
    "observation_law_admission_verified", "full_joint_calendar_law_verified",
    "statistical_confidence_verified", "complete_source_registry_verified",
    "full_solver_verified", "certificate_valid",
)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def identity(path):
    return {"path": str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
            "bytes": path.stat().st_size, "sha256": digest(path)}


def load(path):
    return json.loads(path.read_text())


def verify_pin(row):
    path = Path(row["path"])
    if not path.is_absolute():
        path = ROOT / path
    assert digest(path) == row["sha256"], row["path"]
    if "bytes" in row:
        assert path.stat().st_size == row["bytes"], row["path"]
    return identity(path)


def main():
    pins_path = PACKET / "rust/CALENDAR-COMPONENT-PINS.json"
    pins = load(pins_path)
    bindings = [verify_pin(pins["native_artifact"]), verify_pin(pins["contract"])]
    for section in ("compile_inputs", "component_metadata", "reference_closure", "evidence"):
        bindings.extend(verify_pin(row) for row in pins[section])
    assert len(pins["compile_inputs"]) == 7
    assert len(pins["reference_closure"]) == 8
    assert pins["accepted_baseline_guards"] == {
        "sources": 87, "providers": 79, "binaries": 29, "unchanged": True}
    assert pins["source_admission_verified"] is False
    assert pins["certificate_valid"] is False
    assert pins["full_solver_verified"] is False

    build = load(PACKET / "rust/evidence/calendar-frontend-build-1/BUILD-RECEIPT.json")
    assert build["status"] == "PASS" and len(build["commands"]) == 4
    assert build["binary_sha256"] == pins["native_artifact"]["sha256"]
    assert build["accepted_public_runtime_replaced"] is False
    assert build["network_used_by_build"] is False
    for flag in ("accepted_runtime_rehash_stable", "accepted_source_rehash_stable", "compile_input_rehash_stable"):
        assert build[flag] is True
    for run in build["commands"]:
        assert run["process_started"] and run["exit_code"] == 0 and not run["timed_out"]
        for stream in ("stdout", "stderr"):
            path = PACKET / "rust/evidence/calendar-frontend-build-1" / (run["id"] + "." + stream)
            assert digest(path) == run[stream + "_sha256"]
    test_log = (PACKET / "rust/evidence/calendar-frontend-build-1/tests.stdout").read_text()
    assert "11 passed; 0 failed" in test_log

    reviews = {}
    for name, rel in (
        ("frontend", "design/evidence/calendar-general-frontend-review-1/RECEIPT.json"),
        ("helper", "design/evidence/calendar-helper-review-4/RECEIPT.json"),
        ("independent_adapter", "design/evidence/calendar-independent-adapter-review-1/RECEIPT.json"),
        ("adapter", "rust/evidence/calendar-component-controls-1/RECEIPT.json"),
    ):
        path = PACKET / rel
        data = load(path)
        assert data.get("pass", data.get("status") == "PASS") is True
        bindings.append(identity(path))
        reviews[name] = data
    assert reviews["frontend"]["cases_passed"] == 34
    assert reviews["frontend"]["full_view_rows"] == 259
    for section, count in (("parser_controls", 21), ("semantic_controls", 4), ("native_replay_controls", 3)):
        assert len(reviews["frontend"][section]) == count
        assert all(row["pass"] for row in reviews["frontend"][section])
    assert reviews["frontend"]["binary_before"] == reviews["frontend"]["binary_after"] == pins["native_artifact"]["sha256"]
    assert reviews["helper"]["cases_passed"] == 34 and reviews["helper"]["full_view_rows"] == 259
    assert len(reviews["helper"]["adversarial_controls"]) == 33
    assert len(reviews["helper"]["semantic_scope_controls"]) == 3
    assert reviews["independent_adapter"]["cases_passed"] == 6
    assert reviews["adapter"]["total"] == 18
    assert all(row["status"] == "PASS" for row in reviews["adapter"]["cases"])

    launcher = ROOT / "applications/practical-solver/run.py"
    tested_launcher = EVIDENCE / "launcher-before-descendant-cleanup.py"
    adapter = PACKET / "rust/native_calendar_component.py"
    cases = load(EVIDENCE / "CALENDAR-CASES.json")
    assert len(cases) == 12
    counts = {"SUPPLIED_CALENDAR_TABLE": 0, "UNKNOWN": 0, "REFUSAL": 0}
    case_reviews = []
    for row in cases:
        assert row["launcher_sha256"] == digest(tested_launcher)
        assert row["adapter_sha256"] == digest(adapter)
        out = ROOT / row["output"]
        result_path = out / "RESULT.json"
        assert digest(result_path) == row["result_sha256"]
        result = load(result_path)
        assert result["status"] == row["status"]
        assert digest(out / "REQUEST.json") == row["request_sha256"]
        for flag in FALSE_GATES:
            assert result.get(flag, False) is False, (row["case"], flag)
        status = row["status"]
        if status in ("SUPPLIED_CALENDAR_TABLE", "UNKNOWN"):
            counts[status] += 1
            assert row["exit_code"] == (0 if status == "SUPPLIED_CALENDAR_TABLE" else 2)
            for flag in ("native_solver_called", "native_checker_called", "reference_checker_called"):
                assert result[flag] is True
            child = result["component_result"]
            assert child["binary_observed_sha256"] == pins["native_artifact"]["sha256"]
            for flag in FALSE_GATES:
                assert child[flag] is False
            assert child["provider_work_checked"] is False
            assert child["provider_exhaustion_verified"] is False
            if status == "SUPPLIED_CALENDAR_TABLE":
                for flag in ("formal_table_checked", "independent_all_coefficients_checked",
                             "calendar_agenda_checked", "physical_substitutions_checked"):
                    assert result[flag] is True
            for process in ("solver", "checker", "reference_checker"):
                run = child[process + "_execution"]
                assert run["process_started"] and not run["timed_out"]
                for stream in ("stdout", "stderr"):
                    path = out / "component/component" / (process.replace("_", "-") + "." + stream)
                    assert digest(path) == run[stream + "_sha256"]
        else:
            counts["REFUSAL"] += 1
            assert row["exit_code"] == 1
            assert not row["solver_called"] and not row["checker_called"] and not row["reference_checker_called"]
        case_reviews.append({"case": row["case"], "status": status, "exit_code": row["exit_code"],
                             "result": identity(result_path), "pass": True})
    assert counts == {"SUPPLIED_CALENDAR_TABLE": 5, "UNKNOWN": 3, "REFUSAL": 4}

    # Two outer-launcher controls lacked machine-readable execution receipts.
    # Recheck only these controls, retaining the original stderr/stdout files.
    existing = ROOT / cases[0]["output"]
    def inventory(folder):
        return {str(p.relative_to(folder)): digest(p) for p in sorted(folder.rglob("*")) if p.is_file()}
    before = inventory(existing)
    final_controls_path = EVIDENCE / "launcher-final-controls-2/RECEIPT.json"
    final_controls = load(final_controls_path)
    assert final_controls["pass"] is True
    assert final_controls["launcher_sha256"] == digest(launcher)
    assert final_controls["native_binary_sha256"] == pins["native_artifact"]["sha256"]
    assert final_controls["focused_controls_passed"] == 4
    assert final_controls["functional_cases_passed"] == 12
    assert all(row["pass"] for row in final_controls["focused_controls"] + final_controls["functional_cases"])
    for row in final_controls["functional_cases"]:
        path = final_controls_path.parent / ("calendar-" + row["name"]) / "RESULT.json"
        assert digest(path) == row["result_sha256"]
        assert load(path)["launcher_sha256"] == digest(launcher)
    bindings.append(identity(final_controls_path))
    control_dir = EVIDENCE / "outer-controls-final-2"
    control_dir.mkdir(exist_ok=False)
    commands = [
        ("no-overwrite", ["python3", str(launcher), "calendar-law", "--request", str(existing / "REQUEST.json"),
                          "--native-binary", pins["native_artifact"]["path"], "--output", str(existing)]),
        ("missing-input", ["python3", str(launcher), "calendar-law", "--request", str(control_dir / "absent.json"),
                           "--native-binary", pins["native_artifact"]["path"], "--output", str(control_dir / "must-not-exist")]),
    ]
    controls = []
    for name, command in commands:
        run = subprocess.run(command, cwd=ROOT, capture_output=True, timeout=15)
        assert run.returncode == 1, (name, run.returncode)
        for stream in ("stdout", "stderr"):
            (control_dir / (name + "." + stream)).write_bytes(getattr(run, stream))
        controls.append({"case": name, "command": command, "exit_code": run.returncode,
                         "stdout_sha256": hashlib.sha256(run.stdout).hexdigest(),
                         "stderr_sha256": hashlib.sha256(run.stderr).hexdigest(), "pass": True})
    assert inventory(existing) == before
    assert not (control_dir / "must-not-exist").exists()
    controls[0]["existing_files_unchanged"] = len(before)
    controls[1]["output_directory_created"] = False

    verification = subprocess.run(["python3", str(PACKET / "verify_derivative.py")], cwd=ROOT,
                                  capture_output=True, timeout=15)
    assert verification.returncode == 0
    derivative = json.loads(verification.stdout)
    assert derivative["current_files"] == 63 and derivative["inherited_unchanged_files"] == 534
    assert derivative["known_inherited_baseline_updates"] == 1 and not derivative["failures"]
    (EVIDENCE / "derivative-verification.stdout").write_bytes(verification.stdout)
    (EVIDENCE / "derivative-verification.stderr").write_bytes(verification.stderr)
    bindings.extend([identity(launcher), identity(ROOT / "applications/practical-solver/README.md"),
                     identity(ROOT / "applications/practical-solver/examples/calendar-law.json"),
                     identity(PACKET / "APPLICATION-DERIVATIVE-PINS.json"), identity(EVIDENCE / "BEFORE.json"),
                     identity(EVIDENCE / "CALENDAR-CASES.json"), identity(Path(__file__))])
    old_regressions = []
    for name, status in (("affine", "MATRIX_WITNESS"), ("natural", "MATRIX_WITNESS"),
                         ("genealogy", "FORMAL_GENEALOGY_TABLE")):
        path = EVIDENCE / (name + "-regression") / "RESULT.json"
        assert load(path)["status"] == status
        old_regressions.append({"name": name, "status": status, "result": identity(path),
                                "qualification": "Earlier same-session execution before the last calendar-only launcher provenance edits; not relabeled as a run of the current launcher."})
    # Inventory raw evidence bytes, including native copies that remain ignored
    # by Git. Hashing a saved binary does not promote it to a proof certificate.
    saved = [identity(p) for p in sorted(EVIDENCE.rglob("*"))
             if p.is_file() and p != EVIDENCE / "RECEIPT.json"]
    receipt = {
        "schema": "calendar_application_saved_integration_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": True,
        "component_pin_bindings": bindings, "calendar_cases": case_reviews,
        "outer_controls": controls, "calendar_application_checks": 14,
        "status_counts": counts, "derivative_verification": derivative,
        "earlier_regressions": old_regressions, "saved_files": saved,
        "native_frontend_tests": 11, "independent_frontend_cases": 34,
        "independent_frontend_ordered_views": 259, "adapter_controls": 18,
        "independent_adapter_controls": 6, "native_tests_rerun_by_this_review": False,
        "application_cases_launcher": identity(tested_launcher),
        "application_current_launcher": identity(launcher),
        "application_cases_qualification": "Twelve preserved functional cases bind the pre-cleanup launcher exactly. The later changes add outer process-tree cleanup and explicit request-snapshot binding. Twelve fresh cases plus two outer controls and four focused lifecycle/request controls separately verify the current launcher.",
        "current_launcher_functional_cases": final_controls["functional_cases"],
        "current_launcher_focused_controls": final_controls["focused_controls"],
        "current_launcher_checks": 18,
        "Lean_execution": False, "source_admission_verified": False,
        "certificate_valid": False, "full_solver_verified": False,
        "scope": "Integrated supplied-calendar forward table with independent complete coefficient/agenda/substitution checks. Native replay is not an independent algorithm; provider-work/exhaustion, universal native refinement, observation fitting, complete source census and master inference remain separate. The prior exact117-case RC1 receipt is reused only for unchanged RC1 bytes.",
    }
    target = EVIDENCE / "RECEIPT.json"
    target.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    (PACKET / "quality/CALENDAR-APPLICATION-REVIEW.json").write_text(json.dumps({
        "schema": "calendar_application_review_pointer_v1", "pass": True,
        "receipt": identity(target), "calendar_application_checks": 14,
        "application_source_pins": 63, "certificate_valid": False, "full_solver_verified": False,
    }, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": True, "application_checks": 14, "component_bindings": len(bindings),
                      "saved_files": len(saved), "receipt_sha256": digest(target)}))


if __name__ == "__main__":
    main()
