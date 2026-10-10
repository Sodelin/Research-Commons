#!/usr/bin/env python3
"""Authenticate saved calendar input, native output, build and parity bindings.

No producer, compiler or Lean evaluator is launched. The frozen independent
calendar reference regenerates all 32 exact requests and accepted coefficient
tables; preserved original source bytes and the 117 saved public byte pairs are
checked separately. The serial-H2 followup keeps its separate receipt.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import time

import source_calendar_oracle as oracle

DESIGN = Path(__file__).resolve().parent
RUST = DESIGN.parent / "rust"
ROOT = DESIGN.parents[2]
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
    "parity": "b0b653d006568d0aba7235b7bb22dfc1c784774979764faadf4e64d371e0e959"}


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
    for case in parity["cases"]:
        require(case["pass"] and not case["errors"], "saved public case failed")
        matches = list((PARITY / "cases").glob("*_" + case["name"] + ".req"))
        require(len(matches) == 1, "saved public request naming ambiguous")
        request_path = matches[0]
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
    for name in ["review_saved_calendar.py", "source_calendar_oracle.py", "source_word_oracle.py"]:
        bind(DESIGN / name)
        (args.output / name).write_bytes((DESIGN / name).read_bytes())
    after = {path: digest(Path(path)) for path in observed}
    require(observed == after, "calendar evidence changed during saved review")
    answer = {"schema": "saved_calendar_input_and_execution_binding_review_v1", "status": "PASS",
              "new_compiler_or_producer_execution": False, "frozen_input_cases_rechecked": 32,
              "full_view_rows_rechecked": sum(case["full_view_rows"] for case in cases),
              "saved_public_byte_pairs_rechecked": 117, "historical_compile_source_inputs": 31,
              "historical_snapshot_files": len(snapshot["files"]), "preserved_binary_identities": len(snapshot["binaries"]),
              "build_commands_authenticated": 9, "adversarial_controls": controls, "cases": cases,
              "pins_before": observed, "pins_after": after, "source_admission_verified": False,
              "generic_calendar_refinement_proved": False, "Lean_calendar_execution_claimed": False,
              "observed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(answer, indent=2) + "\n")
    print("PASS", 32, answer["full_view_rows_rechecked"], 117, len(controls), flush=True)


if __name__ == "__main__":
    main()
