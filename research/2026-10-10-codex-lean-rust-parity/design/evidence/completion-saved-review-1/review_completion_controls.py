#!/usr/bin/env python3
"""Independent private completion fixtures and refusal controls.

The frozen reference uses a coupled-generator zero spectral projector. This
review never calls the native lift recurrence, ancestral history formula or Lean.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import time

import source_word_oracle as ref

DESIGN = Path(__file__).resolve().parent
FREEZE = DESIGN / "evidence/word-completion-fixture-freeze-2"
ORACLE_SHA = "bb9f4470e9a5ca4358e5916d546c9009c9abfb62bfa9fc415f589891bfde5102"
CONTRACT_SHA = "272e1694ebe29a6d707435a623d94c99b45fd17f9e88cb06114fe4c109db274f"
INVENTORY_SHA = "5e9e8f6d15c02b51379aa2f12f1678557e7fd1a489edda8fc786f5c9bd45da76"
REJECT = {"completionEmptyRejected": "SOURCE_WORD_COMPLETION_EMPTY_COPY",
          "completionNonrootRejected": "SOURCE_WORD_COMPLETION_ROOT_SUPPORT"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def balanced_four(view):
    tree = view["genealogy"][0]
    return isinstance(tree, list) and len(tree) == 2 and all(
        isinstance(child, list) and len(child) == 2 and all(type(leaf) is int for leaf in child)
        for child in tree)


def closed_form(name, expected):
    if name not in {"completion1", "completion2", "completion3", "completion4",
                    "completionCarriedNonminimum", "completionPermutedFour"}:
        return None
    rows = expected["rows"]
    weights = []
    for row in rows:
        ref.require(len(row["coefficients"]) == 1 and row["coefficients"][0][0] == [],
                    "direct completion unexpectedly uses a symbolic variable")
        weights.append(Fraction(row["coefficients"][0][1]))
    if name in {"completion4", "completionPermutedFour"}:
        ref.require(len(rows) == 120, "four-owner ordered support is incomplete")
        categories = {True: [], False: []}
        for row, weight in zip(rows, weights):
            categories[balanced_four(row["view"])].append(weight)
        ref.require(categories[True] == [Fraction(1, 72)] * 24 and
                    categories[False] == [Fraction(1, 144)] * 96,
                    "four-owner balanced/pectinate weights differ")
        return {"ordered_rows": 120, "balanced_rows": 24, "balanced_weight": "1/72",
                "pectinate_rows": 96, "pectinate_weight": "1/144"}
    count = {"completion1": 1, "completion2": 2, "completion3": 12,
             "completionCarriedNonminimum": 2}[name]
    ref.require(len(rows) == count and weights == [Fraction(1, count)] * count,
                "direct completion closed-form weights differ")
    return {"ordered_rows": count, "weight": str(Fraction(1, count))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rust-probe", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    ref.require(1 <= args.timeout <= 60, "invalid bounded timeout")
    ref.require(digest(DESIGN / "source_word_oracle.py") == ORACLE_SHA and
                digest(DESIGN / "WORD-COMPLETION-EXTENSION-20261010T1300Z.md") == CONTRACT_SHA and
                digest(FREEZE / "INVENTORY.json") == INVENTORY_SHA, "completion freeze changed")
    args.output.mkdir(parents=True, exist_ok=False)
    inventory = ref.epoch.parse_json((FREEZE / "INVENTORY.json").read_bytes())
    paths = [Path(__file__).resolve(), DESIGN / "source_word_oracle.py",
             DESIGN / "boundary_oracle.py", DESIGN / "epoch_oracle.py",
             DESIGN / "population_oracle.py", DESIGN / "chart_check.py",
             DESIGN / "certificate_check.py", DESIGN / "WORD-REFINEMENT.md",
             DESIGN / "WORD-COMPLETION-EXTENSION-20261010T1300Z.md", FREEZE / "INVENTORY.json"]
    if args.rust_probe:
        paths.append(args.rust_probe.resolve())
    requests = {}
    for row in inventory["inputs"]:
        path = Path(row["input"])
        ref.require(path.parent == FREEZE and digest(path) == row["sha256"], "completion input pin differs")
        paths.append(path)
        requests[row["fixture"]] = ref.epoch.parse_json(path.read_bytes())
        ref.check_request(requests[row["fixture"]])
        ref.initial_rows(requests[row["fixture"]])
    before = {str(p): digest(p) for p in paths}
    for path in paths:
        if path.parent == DESIGN:
            (args.output / path.name).write_bytes(path.read_bytes())
    cases = [(name, request, []) for name, request in requests.items()]
    # Challenge precondition priority using the existing private --limit flag.
    # These derived calls require no new producer fixture or input grammar.
    for name, key in [("completionNonrootRejected", "queries"),
                      ("completionEmptyRejected", "initial_assignments")]:
        request = json.loads(ref.epoch.exact_json(requests[name]))
        request["limits"][key] = 0
        cases.append((name, request, ["--limit", key, "0"]))
    records, forms = [], []
    for name, request, overrides in cases:
        label = name + ("-zero-" + overrides[1] if overrides else "")
        started = time.monotonic()
        if name in REJECT:
            ref.require(not request["word"], "refusal control unexpectedly has a finite prefix")
            ref.check_request(request)
            if name == "completionEmptyRejected":
                ref.require(not request["context"]["local_samples"], "empty refusal is not empty")
            else:
                literal, _, _ = ref.initial_rows(request)
                ref.require(any(place != ("A", request["context"]["root"])
                                for code in literal for _, _, place in code.state.roots),
                            "nonroot refusal actually has root support")
            expectation = {"status": "INVALID_INPUT", "reason": REJECT[name]}
            review = {"status": "ORACLE_ONLY", "refused": REJECT[name]}
            result = None
        else:
            expectation, result = ref.expected_probe(name, request)
            if expectation["status"] == "TABLE":
                form = closed_form(name, expectation)
                if form:
                    forms.append({"fixture": name, **form})
                review = {"status": "ORACLE_ONLY", "full_view_rows": len(expectation["rows"]),
                          "terms": sum(len(row["coefficients"]) for row in expectation["rows"])}
                readers = {k: ref.epoch.terms(p) for k, p in
                           ref.unranked(request, expectation["rows"], True).items()}
                (args.output / (label + ".topology.json")).write_text(json.dumps(readers, indent=2) + "\n")
            else:
                ref.require(expectation["status"] == "UNKNOWN" and
                            expectation["limit"]["stage"] == "COMPLETION" and
                            "rows" not in expectation, "completion cap produced partial/unrelated output")
                review = {"status": "ORACLE_ONLY", "unknown": expectation["limit"]}
        (args.output / (label + ".request.json")).write_text(json.dumps(request, indent=2) + "\n")
        (args.output / (label + ".expected.json")).write_text(json.dumps(expectation, indent=2) + "\n")
        if args.rust_probe:
            command = [str(args.rust_probe.resolve()), name, *overrides]
            completed = subprocess.run(command, capture_output=True, check=False, timeout=args.timeout)
            (args.output / (label + ".rust.stdout")).write_bytes(completed.stdout)
            (args.output / (label + ".rust.stderr")).write_bytes(completed.stderr)
            ref.require(len(completed.stdout) <= 4 * 1024 * 1024 and
                        len(completed.stderr) <= 4 * 1024 * 1024, "completion probe exceeded frame cap")
            if name in REJECT:
                ref.require(completed.returncode == 1 and not completed.stdout and
                            ('InvalidInput("' + REJECT[name] + '")').encode() in completed.stderr,
                            "completion precondition was masked or promoted")
                review["status"] = "PASS"
            else:
                ref.require(completed.returncode == 0, "completion probe failed")
                review = ref.check_probe(ref.epoch.parse_json(completed.stdout), expectation, result)
            review.update(command=command, exit_code=completed.returncode, process_started=True)
        records.append({"fixture": name, "control": label, "seconds": time.monotonic() - started, **review})
        print(label, review["status"], flush=True)
    after = {str(p): digest(p) for p in paths}
    ref.require(before == after, "completion inputs/probe changed")
    receipt = {"schema": "private_original_completion_control_review_v1",
               "status": "PASS" if args.rust_probe else "ORACLE_SELF_CHECK_ONLY",
               "actual_native_execution": bool(args.rust_probe), "actual_lean_execution": False,
               "generic_native_refinement_proved": False, "source_admission_verified": False,
               "algorithm": "Coupled ordered-half-rate generator zero spectral projector",
               "pins_before": before, "pins_after": after, "stable": True,
               "controls_total": len(records), "results": records, "closed_forms": forms,
               "initial_input_schema_failure_preserved": True}
    (args.output / "RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(receipt["status"], len(records), flush=True)


if __name__ == "__main__":
    main()
