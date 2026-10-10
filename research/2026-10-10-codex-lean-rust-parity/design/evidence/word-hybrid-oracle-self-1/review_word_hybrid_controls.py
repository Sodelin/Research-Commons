#!/usr/bin/env python3
"""Two additive finite hybrid-calendar controls against the frozen word oracle.

These change only the private fixture terminal from ANCESTRAL_COMPLETE to
FULL_VIEW. No completion, chosen-table extraction or source admission is claimed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

import source_word_oracle as oracle

DESIGN = Path(__file__).resolve().parent
ORACLE_SHA = "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102"
PAIRS = {"parallelCommonFinite": "parallelCommonCalendar",
         "parallelIndependentFinite": "parallelIndependentCalendar"}


def pin(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def request(name):
    parent = DESIGN / "evidence/word-fixture-freeze-1" / (PAIRS[name] + ".request.json")
    result = oracle.epoch.parse_json(parent.read_bytes())
    oracle.require(result["terminal"] == "ANCESTRAL_COMPLETE", "control parent terminal changed")
    result["terminal"] = "FULL_VIEW"
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    oracle.require(1 <= args.timeout <= 60, "invalid bounded timeout")
    args.output.mkdir(parents=True, exist_ok=False)
    oracle.require(pin(DESIGN / "source_word_oracle.py") == ORACLE_SHA, "frozen oracle changed")
    inputs = [Path(__file__).resolve(), DESIGN / "source_word_oracle.py",
              DESIGN / "boundary_oracle.py", DESIGN / "epoch_oracle.py",
              DESIGN / "population_oracle.py", DESIGN / "chart_check.py",
              DESIGN / "certificate_check.py", DESIGN / "WORD-REFINEMENT.md"]
    for parent in PAIRS.values():
        inputs.append(DESIGN / "evidence/word-fixture-freeze-1" / (parent + ".request.json"))
    if args.rust_probe:
        inputs.append(args.rust_probe.resolve())
    before = {str(p): pin(p) for p in inputs}
    for path in inputs:
        if path.parent == DESIGN:
            (args.output / path.name).write_bytes(path.read_bytes())
    records = []
    for name, parent in PAIRS.items():
        started = time.monotonic()
        req = request(name)
        frozen = DESIGN / "evidence/word-hybrid-fixture-freeze-1" / (name + ".request.json")
        oracle.require(oracle.epoch.exact_json(oracle.epoch.parse_json(frozen.read_bytes())) ==
                       oracle.epoch.exact_json(req), "frozen additive request changed")
        expected, internals = oracle.expected_probe(name, req)
        oracle.require(expected["status"] == "TABLE", "reference did not produce full row")
        (args.output / (name + ".expected.json")).write_text(json.dumps(expected, indent=2) + "\n")
        readers = {k: oracle.epoch.terms(poly) for k, poly in
                   oracle.unranked(req, expected["rows"]).items()}
        (args.output / (name + ".readouts.json")).write_text(json.dumps(readers, indent=2) + "\n")
        if args.rust_probe:
            command = [str(args.rust_probe.resolve()), name]
            completed = subprocess.run(command, capture_output=True, timeout=args.timeout, check=False)
            (args.output / (name + ".rust.stdout")).write_bytes(completed.stdout)
            (args.output / (name + ".rust.stderr")).write_bytes(completed.stderr)
            oracle.require(completed.returncode == 0 and len(completed.stdout) <= 4 * 1024 * 1024,
                           "private probe failed or exceeded frame cap")
            actual = oracle.epoch.parse_json(completed.stdout)
            review = oracle.check_probe(actual, expected, internals)
            review.update(command=command, exit_code=completed.returncode)
        else:
            review = {"status": "ORACLE_ONLY", "full_view_rows": len(expected["rows"]),
                      "terms": sum(len(row["coefficients"]) for row in expected["rows"])}
        records.append({"fixture": name, "parent_fixture": parent,
                        "request_sha256": pin(frozen), "seconds": time.monotonic() - started, **review})
        print(name, review["status"], review["full_view_rows"], flush=True)
    after = {str(p): pin(p) for p in inputs}
    oracle.require(before == after, "control source or probe changed during execution")
    receipt = {"schema": "original_source_word_hybrid_controls_v1",
               "status": "PASS" if args.rust_probe else "ORACLE_ONLY",
               "actual_native_execution": bool(args.rust_probe), "actual_lean_execution": False,
               "source_admission_verified": False, "chosen_table_refinement_proved": False,
               "ancestral_completion_executed": False, "pins_before": before,
               "pins_after": after, "stable": True, "results": records}
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(receipt["status"], len(records), flush=True)


if __name__ == "__main__":
    main()
