#!/usr/bin/env python3
"""Authenticate saved calendar input, native output, build and parity bindings.

No producer, compiler or Lean evaluator is launched. The frozen independent
calendar reference regenerates all 32 exact requests and accepted coefficient
tables; preserved original source bytes and the 117 saved public byte pairs are
checked separately. The serial-H2 followup keeps its separate execution receipt
and adds final-v2 source/input origin and executable-identity authentication.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import time

import source_calendar_oracle as oracle
import review_calendar_serial_hybrids as serial

DESIGN = Path(__file__).resolve().parent
RUST = DESIGN.parent / "rust"
SOURCE = DESIGN / "evidence/calendar-rust-review-1"
FREEZE = DESIGN / "evidence/calendar-fixture-freeze-1"
PARITY = DESIGN / "evidence/calendar-candidate-regression-1"
PINS = {
    "oracle": "3f01def72cbd1b999099f713764e97941753a12349bcf4e23f3e7d90b63de27c",
    "contract": "7e2202aeac884c2024e3f168031b8e90ae73f3c9c924252e7e3705aeb8cba478",
    "inventory": "b9bd9a83d4cf864118d2d182d800de59e6026242e9be9f6d592a40ccf82de77c",
    "reference_receipt": "9b644ec1d38833741803cf13333230f328fb0362313e72f1b7830b4b7e0f9bbf",
    "build": "fae3304514f82ad2177285ea6fe5899593ded634e4afa0545018d596d813bf32",
    "source_freeze": "9eb7d4974eb7db8bd7df52e59e9af245f045890c249be08d8179ce49cebab3f0",
    "snapshot": "00fdb080fd88460427477a8f949bc2920b3b17fa6f20677f617a6459276659aa",
    "parity": "b0b653d006568d0aba7235b7bb22dfc1c784774979764faadf4e64d371e0e959",
    "serial_inventory": "119759df99a993532659280b1578f45e625d6e6b571ca85792a199c212481edb",
    "serial_receipt": "8b09466c742ddc5078ffc5c91a6c0feeb38c6357d47cf8b7dfffc5a57c7f3876",
    "final_freeze": "f56ee31ea5fe1a732441996be3629eff070b7997e72d0c8964e02ef7c5f544fd",
    "final_snapshot": "c3905f69f66c1be5f9dfc9857a79d6600c5c1233c3e349931ead3aef4953f16a",
    "final_build": "628960b1db3c47f349625550f3d6d298203892f004f609c2d8eb10d749e90110",
    "serial_origins": "95b72892057812935c48d77707e2d6be77bca9518e30e2256df030de0d494935",
    "identity_reuse": "f6d78cfdf3b8db0973fa78b1b8d3ebb0f4fedecc244626ee475581975882763a"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    observed = {}
    require, parse = oracle.ref.require, oracle.ref.epoch.parse_json

    def bind(path, wanted=None):
        path = path.resolve()
        actual = digest(path)
        require(wanted is None or actual == wanted, "saved calendar artifact differs: " + str(path))
        observed[str(path)] = actual
        return path.read_bytes()

    bind(DESIGN / "source_calendar_oracle.py", PINS["oracle"])
    bind(oracle.CONTRACT, PINS["contract"])
    inventory = parse(bind(FREEZE / "INVENTORY.json", PINS["inventory"]))
    receipt = parse(bind(SOURCE / "RECEIPT.json", PINS["reference_receipt"]))
    freeze = parse(bind(RUST / "notes/CALENDAR-SOURCE-FREEZE-1.json", PINS["source_freeze"]))
    build_dir = RUST / "evidence/calendar-build-1"
    build = parse(bind(build_dir / "BUILD-RECEIPT.json", PINS["build"]))
    history = RUST / "evidence/history/calendar-candidate-v1"
    snapshot = parse(bind(history / "SNAPSHOT.json", PINS["snapshot"]))
    require(build["status"] == "PASS" and build["compile_input_rehash_stable"] and
            build["preserved_runtime_rehash_stable"] and build["frozen_inputs"] == freeze and
            build["freeze_sha256"] == PINS["source_freeze"] and not build["public_runtime_replaced"] and
            not build["source_admission_claim"] and not build["general_calendar_refinement_proof_claim"],
            "calendar build scope/binding differs")
    require(snapshot["build_receipt_sha256"] == PINS["build"] and
            snapshot["source_freeze_sha256"] == PINS["source_freeze"], "historical snapshot binding differs")
    for record in snapshot["files"]:
        bind(history / record["path"], record["sha256"])
    snapshot_files = {record["path"]: record["sha256"] for record in snapshot["files"]}
    compile_inputs = [entry for entry in freeze["inputs"] if entry["role"] == "compile_input"]
    require(len(compile_inputs) == freeze["compile_input_count"] == 31, "calendar compile source count differs")
    for record in compile_inputs:
        relative = record["path"].split("/rust/", 1)[1]
        require(snapshot_files.get(relative) == record["sha256"], "compile input missing from historical source snapshot")
    for record in snapshot["binaries"]:
        bind(Path(record["preserved_path"]), record["sha256"])
    require(len(build["commands"]) == 9, "calendar build command coverage differs")
    for record in build["commands"]:
        require(record["process_started"] and record["exit_code"] == 0 and not record["timed_out"],
                "saved build command did not pass")
        for suffix in ("stdout", "stderr"):
            bind(build_dir / (record["id"] + "." + suffix), record[suffix + "_sha256"])
    require(receipt["pass"] and receipt["cases_total"] == receipt["cases_passed"] == 32 and
            receipt["full_view_rows_total"] == 163 and receipt["native_processes_executed"] and
            not receipt["Lean_execution"] and not receipt["source_admission_verified"] and
            not receipt["universal_calendar_refinement_proved"] and receipt["pins_before"] == receipt["pins_after"],
            "saved calendar execution claim differs")
    for path, wanted in receipt["pins_before"].items():
        bind(Path(path), wanted)
    reference = oracle.fixtures()
    inputs = {entry["fixture"]: entry for entry in inventory["inputs"]}
    results = {entry["fixture"]: entry for entry in receipt["cases"]}
    require(set(reference) == set(inputs) == set(results) and len(inputs) == 32,
            "frozen/calendar execution fixture coverage differs")
    expected_all, cases = {}, []
    for name, request in reference.items():
        frozen = parse(bind(FREEZE / inputs[name]["path"], inputs[name]["sha256"]))
        require(oracle.ref.epoch.exact_json(frozen) == oracle.ref.epoch.exact_json(request),
                "regenerated calendar request differs from prebuild input bytes")
        record, invalid = results[name], None
        try:
            expected, internal = oracle.expected_probe(name, frozen)
            expected_all[name] = expected, internal
            saved = parse(bind(SOURCE / (name + ".expected.json")))
            require(oracle.ref.epoch.exact_json(saved) == oracle.ref.epoch.exact_json(expected),
                    "saved complete expectation differs from independent reference")
            require(saved["request"] == frozen, "saved expected request lacks frozen input binding")
        except oracle.InvalidInput as error:
            invalid = error.code
            require(inputs[name]["expected_status"] == record["expected_status"] == "INVALID_INPUT" and
                    inputs[name]["invalid_code"] == record["invalid_code"] == invalid,
                    "invalid input/control priority differs")
        run = record["run"]
        require(record["pass"] and run["process_started"] and not run["timed_out"],
                "saved producer did not complete its fixture")
        stdout = bind(SOURCE / (name + ".rust.stdout"), run["stdout_sha256"])
        stderr = bind(SOURCE / (name + ".rust.stderr"), run["stderr_sha256"])
        if invalid:
            require(run["exit_code"] == 1 and not stdout and invalid in stderr.decode(),
                    "saved producer invalid input frame/exit differs")
            count = 0
        else:
            require(run["exit_code"] == 0, "saved valid producer exit differs")
            review = oracle.check_probe(parse(stdout), expected, internal)
            require(review == run["review"], "saved coefficient review differs")
            count = len(expected.get("word_result", {}).get("rows", []))
        cases.append({"fixture": name, "full_view_rows": count, "frozen_request_binding": "PASS",
                      "saved_native_output_review": "PASS"})
    controls = oracle.self_controls(expected_all)
    require(controls == receipt["controls"], "saved calendar adversarial controls differ")
    parity = parse(bind(PARITY / "PARITY-RECEIPT.json", PINS["parity"]))
    require(parity["pass"] and parity["cases_total"] == parity["cases_passed"] == 117 and
            parity["identities"]["identities_stable"] and
            parity["identities"]["binary_sha256_before"] == parity["identities"]["binary_sha256_after"],
            "saved public parity scope/identities differ")
    for record in parity["identities"]["executables"].values():
        bind(Path(record["path"]), record["sha256"])
    for index, case in enumerate(parity["cases"]):
        require(case["pass"] and not case["errors"], "saved public case failed")
        request_path = PARITY / "cases" / (f"{index:04d}-" + case["name"] + ".req")
        bind(request_path, case["request_sha256"])
        prefix = request_path.with_suffix("")
        pair = []
        for language in ("lean", "rust"):
            run = case["runs"][language]
            require(run["process_started"] and run["exit_code"] in (0, 1, 2),
                    "saved public process status differs")
            pair.append(bind(Path(str(prefix) + "." + language + ".stdout"), run["stdout_sha256"]))
            bind(Path(str(prefix) + "." + language + ".stderr"), run["stderr_sha256"])
        require(pair[0] == pair[1], "saved canonical public bytes differ")
    # Preserve the first 32-case binding review; authenticate v2 separately.
    final_history = RUST / "evidence/history/calendar-candidate-v2"
    final_snapshot = parse(bind(final_history / "SNAPSHOT.json", PINS["final_snapshot"]))
    final_freeze = parse(bind(RUST / "notes/CALENDAR-SOURCE-FREEZE-2.json", PINS["final_freeze"]))
    final_build_dir = RUST / "evidence/calendar-build-2"
    final_build = parse(bind(final_build_dir / "BUILD-RECEIPT.json", PINS["final_build"]))
    require(final_build["status"] == "PASS" and final_build["frozen_inputs"] == final_freeze and
            final_build["compile_input_rehash_stable"] and final_build["preserved_runtime_rehash_stable"] and
            final_snapshot["build_receipt_sha256"] == PINS["final_build"] and
            final_snapshot["source_freeze_sha256"] == PINS["final_freeze"] and
            final_snapshot["serial_reference_receipt_sha256"] == PINS["serial_receipt"] and
            final_freeze["input_fixture_count"] == 34, "final-v2 build/source/acceptance binding differs")
    for record in final_snapshot["files"]:
        bind(final_history / record["path"], record["sha256"])
    for record in final_snapshot["binaries"]:
        bind(Path(record["preserved_path"]), record["sha256"])
    final_root = DESIGN.parents[2]
    for record in final_freeze["inputs"]:
        path = final_root / record["path"]
        if digest(path) != record["sha256"] and "/rust/" in record["path"]:
            path = final_history / record["path"].split("/rust/", 1)[1]
        bind(path, record["sha256"])
    for record in final_build["commands"]:
        require(record["process_started"] and record["exit_code"] == 0 and not record["timed_out"],
                "final-v2 build command did not pass")
        for suffix in ("stdout", "stderr"):
            bind(final_build_dir / (record["id"] + "." + suffix), record[suffix + "_sha256"])
    origins = parse(bind(RUST / "notes/CALENDAR-SERIAL-FIXTURE-ORIGINS-1.json", PINS["serial_origins"]))
    serial_inventory = parse(bind(serial.FREEZE / "INVENTORY.json", PINS["serial_inventory"]))
    serial_source = DESIGN / "evidence/calendar-serial-hybrid-rust-review-1"
    serial_receipt = parse(bind(serial_source / "RECEIPT.json", PINS["serial_receipt"]))
    require(serial_receipt["pass"] and serial_receipt["cases_total"] == serial_receipt["cases_passed"] == 2 and
            serial_receipt["full_view_rows_total"] == 96 and serial_receipt["native_execution"] and
            not serial_receipt["Lean_execution"] and serial_receipt["pins_before"] == serial_receipt["pins_after"],
            "serial two-hybrid execution claim differs")
    for path, wanted in serial_receipt["pins_before"].items():
        bind(Path(path), wanted)
    serial_expected = {}
    for entry in serial_inventory["inputs"]:
        name = entry["fixture"]
        request = parse(bind(serial.FREEZE / entry["path"], entry["sha256"]))
        origin_record = next(item for item in origins["fixtures"] if item["fixture"] == name)
        require(origin_record["request_sha256"] == entry["sha256"] and
                parse(bind(final_root / origin_record["request_path"], entry["sha256"])) == request and
                request == serial.requests()[name], "final-v2 serial request origin differs")
        expected, internal = oracle.expected_probe(name, request)
        serial_expected[name] = expected, internal
        require(parse(bind(serial_source / (name + ".expected.json"))) == expected,
                "serial saved exact expectation differs")
        run = next(item for item in serial_receipt["cases"] if item["fixture"] == name)["run"]
        require(run["process_started"] and run["exit_code"] == 0 and not run["timed_out"],
                "serial saved native process did not pass")
        actual = parse(bind(serial_source / (name + ".rust.stdout"), run["stdout_sha256"]))
        bind(serial_source / (name + ".rust.stderr"), run["stderr_sha256"])
        require(oracle.check_probe(actual, expected, internal) == run["review"],
                "serial saved complete table/coefficient review differs")
    marginals, serial_controls = serial.register_controls(serial_expected)
    require(marginals == serial_receipt["register_marginal_controls"] and
            serial_controls == serial_receipt["adversarial_controls_rejected"], "serial register controls differ")
    identity_reuse = parse(bind(RUST / "notes/CALENDAR-CANDIDATE-IDENTITY-REUSE-1.json", PINS["identity_reuse"]))
    require(identity_reuse["main_byte_identical"] and identity_reuse["public117_reused_by_actual_main_identity"] and
            not identity_reuse["public117_reexecuted_for_candidate2"] and
            identity_reuse["public117_receipt_sha256"] == PINS["parity"], "final-v2 public parity reuse differs")
    for record in identity_reuse["artifact_comparisons"]:
        a = bind(Path(record["candidate1_path"]), record["candidate1_sha256"])
        b = bind(Path(record["candidate2_path"]), record["candidate2_sha256"])
        require((a == b) == record["byte_identical"], "claimed executable identity reuse differs")
    for name in ["review_saved_calendar.py", "source_calendar_oracle.py", "source_word_oracle.py",
                 "review_calendar_serial_hybrids.py"]:
        bind(DESIGN / name)
        (args.output / name).write_bytes((DESIGN / name).read_bytes())
    after = {path: digest(Path(path)) for path in observed}
    require(observed == after, "calendar evidence changed during saved review")
    answer = {"schema": "saved_calendar_input_and_execution_binding_review_v1", "status": "PASS",
              "new_compiler_or_producer_execution": False, "frozen_input_cases_rechecked": 34,
              "separate_case_scopes": {"original": {"cases": 32, "views": 163}, "serial_H2": {"cases": 2, "views": 96}},
              "full_view_rows_rechecked": sum(case["full_view_rows"] for case in cases) + 96,
              "saved_public_byte_pairs_rechecked": 117, "historical_compile_source_inputs": 31,
              "historical_snapshot_files": len(snapshot["files"]), "preserved_binary_identities": len(snapshot["binaries"]),
              "final_v2_source_and_fixture_inputs_authenticated": len(final_freeze["inputs"]),
              "final_v2_snapshot_files_authenticated": len(final_snapshot["files"]),
              "build_commands_authenticated": 18, "adversarial_controls": controls,
              "serial_adversarial_controls": serial_controls, "serial_full_register_marginals": marginals,
              "final_v2_main_identity_reuses_original117_receipt": True, "cases": cases,
              "pins_before": observed, "pins_after": after, "source_admission_verified": False,
              "generic_calendar_refinement_proved": False, "Lean_calendar_execution_claimed": False,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS", 34, answer["full_view_rows_rechecked"], 117, len(controls) + len(serial_controls), flush=True)


if __name__ == "__main__":
    main()
