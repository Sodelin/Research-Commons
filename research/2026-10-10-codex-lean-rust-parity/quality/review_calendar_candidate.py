#!/usr/bin/env python3
"""Authenticate both calendar candidates and independently recheck saved outputs."""
from datetime import datetime, timezone
import json
from pathlib import Path
import sys

from review_word_candidate import PACKET, ROOT, digest, read

sys.path.insert(0, str(PACKET / "design"))
import source_calendar_oracle as oracle
import review_calendar_serial_hybrids as serial


def main():
    errors, pins = [], {}

    def bind(path, expected):
        actual = digest(path)
        pins[str(path)] = actual
        if actual != expected:
            errors.append("Identity: " + str(path))

    saved = read(PACKET / "design/evidence/calendar-saved-review-2/RECEIPT.json")
    if (saved["status"] != "PASS" or saved["pins_before"] != saved["pins_after"]
            or saved["frozen_input_cases_rechecked"] != 32
            or saved["full_view_rows_rechecked"] != 163
            or saved["saved_public_byte_pairs_rechecked"] != 117):
        errors.append("Saved original32 review scope")
    for path, wanted in saved["pins_before"].items():
        # The design reviewer advances independently; authenticate the exact
        # preserved reviewer used for this historical receipt.
        source = Path(path)
        if source == PACKET / "design/review_saved_calendar.py":
            source = PACKET / "design/evidence/calendar-saved-review-2/review_saved_calendar.py"
        bind(source, wanted)

    builds = []
    for version, file_count, input_count, guard_count in ((1, 39, 75, 23), (2, 46, 87, 29)):
        freeze_path = PACKET / f"rust/notes/CALENDAR-SOURCE-FREEZE-{version}.json"
        freeze = read(freeze_path)
        directory = PACKET / f"rust/evidence/calendar-build-{version}"
        build = read(directory / "BUILD-RECEIPT.json")
        history = PACKET / f"rust/evidence/history/calendar-candidate-v{version}"
        snapshot = read(history / "SNAPSHOT.json")
        bind(freeze_path, build["freeze_sha256"])
        bind(directory / "BUILD-RECEIPT.json", snapshot["build_receipt_sha256"])
        if (build["status"] != "PASS" or build["frozen_inputs"] != freeze
                or not build["compile_input_rehash_stable"]
                or not build["preserved_runtime_rehash_stable"]
                or len(freeze["inputs"]) != input_count
                or len(freeze["preserved_runtime_inputs"]) != guard_count
                or len(snapshot["files"]) != file_count
                or len(snapshot["binaries"]) != 6
                or len(freeze["inherited_providers"]) != 79
                or build["general_calendar_refinement_proof_claim"]
                or build["source_admission_claim"] or build["public_runtime_replaced"]):
            errors.append(f"Candidate{version} scope/count/binding")
        for row in snapshot["files"]:
            bind(history / row["path"], row["sha256"])
        for row in snapshot["binaries"]:
            bind(Path(row["preserved_path"]), row["sha256"])
        compile_inputs = 0
        for row in freeze["inputs"]:
            if row["role"] == "compile_input":
                compile_inputs += 1
                path = history / row["path"].split("/rust/", 1)[1]
            else:
                path = ROOT / row["path"]
            bind(path, row["sha256"])
        if compile_inputs != 31:
            errors.append("Compile source count")
        for row in freeze["inherited_providers"]:
            bind(ROOT / row["path"], row["sha256"])
        for row in freeze["preserved_runtime_inputs"]:
            bind(Path(row["path"]), row["sha256"])
        for command in build["commands"]:
            if (command["exit_code"] != 0 or command["timed_out"]
                    or not command["process_started"]):
                errors.append("Build command: " + command["id"])
            for stream in ("stdout", "stderr"):
                bind(directory / (command["id"] + "." + stream), command[stream + "_sha256"])
        builds.append(build)

    # Strengthen the saved original32 refusal and117 exit-code checks.
    original = read(PACKET / "design/evidence/calendar-rust-review-1/RECEIPT.json")
    for case in original["cases"]:
        if case["expected_status"] == "INVALID_INPUT":
            stem = PACKET / "design/evidence/calendar-rust-review-1" / case["fixture"]
            if (Path(str(stem) + ".rust.stdout").read_bytes()
                    or Path(str(stem) + ".rust.stderr").read_text()
                    != 'InvalidInput("' + case["invalid_code"] + '")\n'):
                errors.append("Exact private refusal: " + case["fixture"])
    parity = read(PACKET / "design/evidence/calendar-candidate-regression-1/PARITY-RECEIPT.json")
    exits = {"SAT": 0, "UNSAT": 0, "TABLE": 0, "UNKNOWN": 2,
             "CONDITIONAL_ARITHMETIC": 2, "REFUSED": 1}
    if (builds[0]["binary_sha256"] != builds[1]["binary_sha256"]
            or parity["identities"]["executables"]["rust"]["sha256"] != builds[1]["binary_sha256"]):
        errors.append("Main117 byte identity reuse")
    for case in parity["cases"]:
        if (any(status != case["expected"] for status in case["status"].values())
                or any(run["exit_code"] != exits[case["expected"]] for run in case["runs"].values())):
            errors.append("Exact public status/exit: " + case["name"])

    directory = PACKET / "design/evidence/calendar-serial-hybrid-rust-review-1"
    comparison = read(directory / "RECEIPT.json")
    inventory = read(PACKET / "design/evidence/calendar-serial-hybrid-fixture-freeze-1/INVENTORY.json")
    if (not comparison["pass"] or comparison["cases_passed"] != 2
            or comparison["full_view_rows_total"] != 96
            or comparison["pins_before"] != comparison["pins_after"]
            or comparison["Lean_execution"] or comparison["source_admission_verified"]
            or comparison["general_calendar_refinement_proved"]
            or not comparison["native_execution"]):
        errors.append("Serial followup scope")
    for path, wanted in comparison["pins_before"].items():
        bind(Path(path), wanted)
    expected_all = {}
    inputs = {row["fixture"]: row for row in inventory["inputs"]}
    for case in comparison["cases"]:
        name = case["fixture"]
        path = PACKET / "design/evidence/calendar-serial-hybrid-fixture-freeze-1" / inputs[name]["path"]
        bind(path, inputs[name]["sha256"])
        request = read(path)
        if request != serial.requests()[name] or case["request_sha256"] != inputs[name]["sha256"]:
            errors.append("Serial request origin: " + name)
        expected, internal = oracle.expected_probe(name, request)
        expected_all[name] = expected, internal
        run = case["run"]
        for stream in ("stdout", "stderr"):
            bind(directory / (name + ".rust." + stream), run[stream + "_sha256"])
        if (not case["pass"] or run["exit_code"] or run["timed_out"]
                or not run["process_started"]
                or (directory / (name + ".rust.stderr")).read_bytes()
                or read(directory / (name + ".expected.json")) != expected
                or oracle.check_probe(read(directory / (name + ".rust.stdout")), expected, internal) != run["review"]):
            errors.append("Complete serial output: " + name)
    marginals, controls = serial.register_controls(expected_all)
    if (marginals != comparison["register_marginal_controls"]
            or controls != comparison["adversarial_controls_rejected"]):
        errors.append("Serial register/adversarial controls")
    result = {"schema": "calendar_saved_candidate_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "pass": not errors, "errors": errors, "cases": 34, "full_ordered_rows": 259,
        "public_protocol_cases": 117, "public_main_reused_by_exact_byte_identity": True,
        "authenticated_artifacts": len(pins), "pins": pins,
        "reviewer_sha256": digest(Path(__file__)),
        "scope": "Saved original32/163 plus serial2/96 exact finite calendar comparisons, both frozen builds/sources/native guards and saved117 public byte pairs. Complete register/coefficient/work/witness outputs checked. No new native execution, Lean calendar extraction, universal native refinement, source admission or G6/G7 closure inferred."}
    (PACKET / "quality/CALENDAR-CANDIDATE-REVIEW.json").write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("pass", "errors", "cases", "full_ordered_rows", "authenticated_artifacts")}))
    return not result["pass"]


if __name__ == "__main__":
    raise SystemExit(main())
