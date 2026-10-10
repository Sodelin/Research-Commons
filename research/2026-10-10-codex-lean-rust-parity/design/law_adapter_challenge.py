#!/usr/bin/env python3
"""Focused independent attacks on the captured-source LAW launcher.

Synthetic producers intentionally accept their own output. They are controls,
not admitted scientific sources. No historical or production bytes are edited.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time
from types import ModuleType

from certificate_check import require
from law_check import verify_law_certificate
from adapter_challenge import forged_producer

DESIGN = Path(__file__).resolve().parent
PACKET = DESIGN.parent
ROOT = PACKET.parents[1]
ADAPTER = PACKET / "rust/native_law_component.py"
TRANSPORT = PACKET / "rust/native_component.py"
BASELINE = ROOT / "research/2026-10-01-g7-continuous-design/law_compiler.py"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load_adapter(name):
    # Each test instance owns a captured transport object. Drift controls never
    # mutate a live shared module or source file.
    transport = ModuleType("native_component")
    transport.__file__ = str(TRANSPORT)
    sys.modules["native_component"] = transport
    exec(compile(TRANSPORT.read_bytes(), str(TRANSPORT), "exec"), transport.__dict__)
    module = ModuleType(name)
    module.__file__ = str(ADAPTER)
    sys.modules[name] = module
    exec(compile(ADAPTER.read_bytes(), str(ADAPTER), "exec"), module.__dict__)
    return module


def permute_variables(result, permutation):
    """Apply a bijective variable permutation to every full-table polynomial.

    This preserves formal mass and rooted-to-unrooted pushforward. Resorting
    makes the attack a canonical table, so rejection must use source meaning.
    """
    require(sorted(permutation) == list(range(len(permutation))), "nonbijective attack permutation")
    lines = result.decode("ascii").splitlines()
    answer, index = [], 0
    while index < len(lines):
        line = lines[index]
        answer.append(line)
        index += 1
        if not line.startswith(("TREE ", "SPLIT ")):
            continue
        count = int(line.rsplit(" ", 1)[1])
        terms = []
        for _ in range(count):
            fields = lines[index].split(" ")
            index += 1
            require(fields[0] == "TERM", "malformed seed table")
            exponents = tuple(int(value) for value in fields[2:])
            terms.append((tuple(exponents[i] for i in permutation), fields[1]))
        for exponents, coefficient in sorted(terms):
            answer.append("TERM " + coefficient + " " + " ".join(map(str, exponents)))
    return ("\n".join(answer) + "\n").encode("ascii")


def run(args):
    output = args.output.resolve()
    require(not output.exists(), "review output already exists")
    output.mkdir(parents=True)
    inputs = output / "inputs"
    inputs.mkdir()
    binary = args.binary.resolve()
    require(binary.is_file(), "native executable absent")
    watched = (ADAPTER, TRANSPORT, DESIGN / "certificate_check.py", DESIGN / "chart_check.py",
               DESIGN / "law_check.py", BASELINE, Path(__file__).resolve(), binary)
    before = {str(path): sha(path.read_bytes()) for path in watched}
    for path in watched[:-1]:
        (output / path.name).write_bytes(path.read_bytes())
    adapter = load_adapter("independent_law_adapter_review")
    multi = DESIGN / "evidence/law-multi-hybrid-review-1"
    replay = DESIGN / "evidence/law-parity-attempt-1/cases"

    def seed(name, folder, stem):
        request = (folder / (stem + ".req")).read_bytes()
        table = (folder / (stem + ".rust.stdout")).read_bytes()
        code = 2 if b"\nSTATUS UNKNOWN\n" in table else 0
        verify_law_certificate(request, table, code)
        target = inputs / (name + ".req")
        target.write_bytes(request)
        (inputs / (name + ".seed.rc1")).write_bytes(table)
        return target, request, table

    full, full_raw, full_table = seed("two_hybrids_independent", multi, "two_serial_hybrids_independent")
    _, common_raw, common_table = seed("two_hybrids_common", multi, "two_serial_hybrids_common")
    limited, limited_raw, limited_table = seed("history_unknown", replay, "0095-law_history_limit_zero")
    parallel, parallel_raw, parallel_table = seed("parallel_common", replay, "0088-law_parallel_four_common")
    records = []

    def check(name, request, producer, expected, *, instance=adapter, solver=True, checker=False, reference=False):
        destination = output / name
        start = time.monotonic()
        result = instance.execute(request, destination, producer, sha(producer.read_bytes()))
        errors = []
        for field, value in (("status", expected), ("solver_called", solver),
                             ("checker_called", checker), ("reference_checker_called", reference)):
            if result.get(field) != value:
                errors.append(f"{field}: {result.get(field)!r} != {value!r}")
        for field in ("source_admission_verified", "source_witness_certified", "unrestricted_exclusion_certified",
                      "physical_survival_image_verified", "observation_law_admission_verified",
                      "full_joint_calendar_law_verified", "statistical_confidence_verified",
                      "complete_source_registry_verified", "certificate_checked"):
            if result.get(field) is not False:
                errors.append(f"unsupported scientific/certificate promotion: {field}")
        if expected == "FORMAL_GENEALOGY_TABLE":
            checked = verify_law_certificate((destination / "REQUEST.rc1").read_bytes(),
                                             (destination / "TABLE.rc1").read_bytes(), 0)
            if not checked["inherited_baseline_all_coefficients_checked"] or not result["formal_table_checked"]:
                errors.append("formal table lacks full coefficient comparison")
            if result["native_checker_algorithm_independent"] is not False:
                errors.append("replay checker mislabeled independent")
        if expected == "UNKNOWN" and result.get("unknown_mathematical_exclusion") is not False:
            errors.append("budget failure promoted mathematical exclusion")
        records.append({"case": name, "pass": not errors, "errors": errors,
                        "expected": expected, "observed": result["status"],
                        "elapsed_seconds": time.monotonic()-start,
                        "result": str((destination / "RESULT.json").relative_to(output))})
        return destination

    check("actual_two_hybrid_joint_table", full, binary, "FORMAL_GENEALOGY_TABLE", checker=True, reference=True)
    check("actual_history_unknown", limited, binary, "UNKNOWN")
    check("table_exit_mismatch", full, forged_producer(inputs / "table-exit2", full_table, 2),
          "RESOURCE_OR_EXECUTION_FAILURE")
    check("unknown_exit_mismatch", limited, forged_producer(inputs / "unknown-exit0", limited_table, 0),
          "RESOURCE_OR_EXECUTION_FAILURE")

    permutation = list(range(10))
    permutation[-2:] = permutation[-2:][::-1]
    gamma_swap = permute_variables(full_table, permutation)
    require(gamma_swap != full_table, "gamma permutation seed is symmetric")
    rebound = common_table.replace(common_raw, full_raw, 1)
    permutation = list(range(6))
    permutation[2], permutation[3] = permutation[3], permutation[2]
    parent_swap = permute_variables(parallel_table, permutation)
    require(parent_swap != parallel_table, "original parallel edge seed is symmetric")
    for name, request, raw_request, wrong in (
        ("two_hybrid_gamma_indices_swapped", full, full_raw, gamma_swap),
        ("common_law_rebound_to_independent", full, full_raw, rebound),
        ("parallel_parent_survival_occurrences_swapped", parallel, parallel_raw, parent_swap),
    ):
        # These controls still pass normalization and complete pushforward.
        verified = verify_law_certificate(raw_request, wrong, 0, compare_baseline=False)
        require(verified["polynomial_normalization_checked"] and verified["unrooted_pushforward_checked"],
                "attack did not preserve its advertised invariants")
        try:
            verify_law_certificate(raw_request, wrong, 0)
        except ValueError as error:
            require("pinned inherited source compiler" in str(error), "attack failed for a framing reason")
        else:
            raise ValueError("source-changing attack unexpectedly matches baseline")
        check(name, request, forged_producer(inputs / name, wrong), "RESOURCE_OR_EXECUTION_FAILURE",
              checker=True, reference=True)

    wrong_registry = full_table.replace(b"G:0 G:1", b"G:1 G:0", 1)
    check("variable_registry_changed", full, forged_producer(inputs / "wrong-registry", wrong_registry),
          "RESOURCE_OR_EXECUTION_FAILURE")
    for name, constant in (("baseline_pin_drift", "BASELINE_SHA"), ("law_helper_pin_drift", "EXPECTED_LAW_HELPER_SHA")):
        changed = load_adapter("independent_" + name)
        setattr(changed, constant, "0"*64)
        check(name, full, binary, "REFUSED_REQUEST", instance=changed, solver=False)

    changed = load_adapter("independent_original_source_hash_drift")
    source = inputs / "changed-original-provider.py"
    source.write_bytes(b"deliberate test fixture content\n")
    manifest = inputs / "source-pin-control"
    manifest.mkdir()
    (manifest / "INHERITED-SOURCES.json").write_text(json.dumps({"files": [
        {"path": str(source.relative_to(ROOT)), "sha256": sha(b"different pinned content\n")}
    ]}) + "\n")
    changed.transport.HERE = manifest
    check("inherited_source_hash_drift", full, binary, "REFUSED_REQUEST", instance=changed, solver=False)

    existing = output / "actual_two_hybrid_joint_table"
    original_result = sha((existing / "RESULT.json").read_bytes())
    refused = False
    try:
        adapter.execute(full, existing, binary, before[str(binary)])
    except FileExistsError:
        refused = True
    stable_result = sha((existing / "RESULT.json").read_bytes()) == original_result
    records.append({"case": "fresh_output_preservation", "pass": refused and stable_result,
                    "errors": [] if refused and stable_result else ["existing output overwritten or reused"]})
    after = {str(path): sha(path.read_bytes()) for path in watched}
    receipt = {"claim": "INDEPENDENT_BOUNDED_CAPTURED_SOURCE_LAW_ADAPTER_CHALLENGES",
               "source_admission_claim": False, "universal_native_refinement_claim": False,
               "executed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "cases_total": len(records), "cases_passed": sum(record["pass"] for record in records),
               "identities_before": before, "identities_after": after, "identities_stable": before == after,
               "cases": records, "pass": before == after and all(record["pass"] for record in records)}
    target = output / "ADAPTER-CHALLENGE-RECEIPT.json"
    target.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": receipt["pass"], "cases_passed": receipt["cases_passed"],
                      "cases_total": len(records), "receipt": str(target)}))
    return 0 if receipt["pass"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    return run(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
