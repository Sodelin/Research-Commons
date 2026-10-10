#!/usr/bin/env python3
"""Fresh bounded calendar adapter controls, without a second coefficient solver."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))
import native_calendar_component as adapter


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n").encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    origins = HERE.parent / "design/evidence/calendar-fixture-freeze-1"
    request_bytes = (origins / "twoTipCalendar.request.json").read_bytes()
    supplied = json.loads(request_bytes)
    binary = args.binary.resolve()
    binary_digest = sha(binary.read_bytes())
    source_digest = sha((HERE / "native_calendar_component.py").read_bytes())
    records = []

    def run(name, raw, executable=binary, pin=None, expected="SUPPLIED_CALENDAR_TABLE", starts=(True, True, True)):
        request = args.output / (name + ".request.json")
        request.write_bytes(raw)
        path = args.output / name
        result = adapter.execute(request, path, executable, pin)
        assert result["status"] == expected, (name, result)
        assert tuple(result[key] for key in ("solver_called", "checker_called", "reference_checker_called")) == starts, name
        assert all(result[key] is False for key in adapter.FALSE_CLAIMS), name
        assert result["exit_code"] == {"SUPPLIED_CALENDAR_TABLE": 0, "UNKNOWN": 2,
            "REFUSED_REQUEST": 1, "RESOURCE_OR_EXECUTION_FAILURE": 1}[expected]
        if expected == "SUPPLIED_CALENDAR_TABLE":
            assert all(result[key] is True for key in adapter.TABLE_FLAGS), name
        records.append({"name": name, "status": "PASS", "observed": expected,
            "result_sha256": sha((path / "RESULT.json").read_bytes()), "start_flags": list(starts)})
        return result

    positive = run("tablePinned", request_bytes, pin=binary_digest)
    assert positive["binary_pin_verification"] == "EXPECTED_PIN_MATCHED"
    unpinned = run("tableObservedOnly", request_bytes)
    assert unpinned["binary_pin_verification"] == "NOT_REQUESTED_OBSERVED_HASH_ONLY"
    value = copy.deepcopy(supplied); value["compiler_limits"]["word_length"] = 0
    unknown = run("compilerUnknown", canonical(value), expected="UNKNOWN")
    assert unknown["unknown_metadata"]["unknown_exhaustion_verified"] is True
    value = copy.deepcopy(supplied); value["provider_limits"]["completion"]["calls"] = 0
    unknown = run("providerUnknown", canonical(value), expected="UNKNOWN")
    assert unknown["unknown_metadata"]["limit_check"] == "PROVIDER_LIMIT_FRAME_ONLY"
    assert unknown["unknown_metadata"]["unknown_exhaustion_verified"] is False
    value = copy.deepcopy(supplied); value["word_limits"]["queries"] = 0
    run("wordUnknown", canonical(value), expected="UNKNOWN")
    value = copy.deepcopy(supplied); value["inverse_rates"][0] = "0/1"
    run("invalidBeforeLaunch", canonical(value), expected="REFUSED_REQUEST", starts=(False, False, False))
    raw = request_bytes.decode().replace('"root": 0', '"root": -0')
    if raw == request_bytes.decode():
        raw = canonical(supplied).decode().replace('"root":0', '"root":-0')
    run("negativeZero", raw.encode())
    run("wrongPin", request_bytes, pin="0" * 64, expected="REFUSED_REQUEST", starts=(False, False, False))
    changed = list(adapter.PINS); changed[-1] = (changed[-1][0], "0" * 64)
    original_pins = adapter.PINS
    try:
        adapter.PINS = changed
        run("wrongReferencePin", request_bytes, expected="REFUSED_REQUEST", starts=(False, False, False))
    finally:
        adapter.PINS = original_pins

    valid_table = (args.output / "tablePinned/TABLE.json").read_bytes()
    checked_frame = b'{"schema":"source_calendar_check_v1","status":"ACCEPT"}\n'

    def forged_binary(name, table, code=0, checker_code=0):
        script = args.output / (name + ".py")
        payload = (f"b' ' * {len(table)}" if len(table) > 4 * 1024 * 1024 else repr(table))
        script.write_text("#!/usr/bin/python3\nimport sys\n"
            f"if len(sys.argv)>1 and sys.argv[1]=='check':\n sys.stdout.buffer.write({checked_frame!r});sys.exit({checker_code})\n"
            f"sys.stdin.buffer.read();sys.stdout.buffer.write({payload});sys.exit({code})\n")
        script.chmod(0o700)
        return script

    run("validTableWrongExit", request_bytes, forged_binary("wrongexit", valid_table, code=2),
        expected="RESOURCE_OR_EXECUTION_FAILURE", starts=(True, False, False))
    run("malformedOutput", request_bytes, forged_binary("malformed", b"{}\n"),
        expected="RESOURCE_OR_EXECUTION_FAILURE", starts=(True, False, False))
    run("oversizedOutput", request_bytes, forged_binary("oversized", b" " * (4 * 1024 * 1024 + 1)),
        expected="RESOURCE_OR_EXECUTION_FAILURE", starts=(True, False, False))
    altered = json.loads(valid_table); altered["agenda"]["physical_coordinates"][0]["argument"] = "1/1"
    run("forgedPhysical", request_bytes, forged_binary("physical", canonical(altered)),
        expected="RESOURCE_OR_EXECUTION_FAILURE")
    altered = json.loads(valid_table); altered["word_result"]["work"]["queries"] += 1
    run("forgedWork", request_bytes, forged_binary("work", canonical(altered)),
        expected="RESOURCE_OR_EXECUTION_FAILURE")
    altered = json.loads(valid_table); altered["word_result"]["rows"][0]["witness"]["register"][0] = True
    run("forgedWitness", request_bytes, forged_binary("witness", canonical(altered)),
        expected="RESOURCE_OR_EXECUTION_FAILURE")
    altered = json.loads(valid_table)
    assert len(altered["word_result"]["rows"]) == 2
    altered["word_result"]["rows"][0]["coefficients"][0][1] = "1/3"
    altered["word_result"]["rows"][1]["coefficients"][0][1] = "2/3"
    run("forgedBalancedCoefficients", request_bytes, forged_binary("coefficients", canonical(altered)),
        expected="RESOURCE_OR_EXECUTION_FAILURE")
    run("nativeReplayRejects", request_bytes, forged_binary("reject", valid_table, checker_code=1),
        expected="RESOURCE_OR_EXECUTION_FAILURE")

    target = args.output / "tablePinned"
    before = {str(path.relative_to(target)): sha(path.read_bytes()) for path in target.rglob("*") if path.is_file()}
    try:
        adapter.execute(args.output / "tablePinned.request.json", target, binary)
        raise AssertionError("Existing output accepted")
    except FileExistsError:
        pass
    after = {str(path.relative_to(target)): sha(path.read_bytes()) for path in target.rglob("*") if path.is_file()}
    assert before == after
    records.append({"name": "noOverwrite", "status": "PASS", "all_existing_artifacts_unchanged": True})
    assert sha(binary.read_bytes()) == binary_digest
    assert sha((HERE / "native_calendar_component.py").read_bytes()) == source_digest
    receipt = {"schema": "calendar_component_controls_v1", "status": "PASS", "cases": records,
        "total": len(records), "binary": str(binary), "binary_sha256": binary_digest,
        "adapter_sha256": source_digest, "harness_sha256": sha(Path(__file__).read_bytes()),
        "source_admission_verified": False, "full_solver_verified": False,
        "ended_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": "PASS", "total": len(records), "receipt": str(args.output / "RECEIPT.json")}))


if __name__ == "__main__":
    main()
