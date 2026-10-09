#!/usr/bin/env python3
"""Adversarial and exact replay controls for the original-source adapter."""
import argparse
import copy
import importlib.util
import importlib.metadata
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[3]
APP = ROOT / "applications/practical-solver"
spec = importlib.util.spec_from_file_location("certified_bounds", APP / "certified_bounds.py")
bridge = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bridge)


def run(python, output):
    output = Path(output)
    if output.exists():
        raise ValueError("output must be absent")
    output.mkdir(parents=True)
    results = []

    def example(name):
        return bridge.read_request(APP / "examples/certified-bounds" / (name + ".json"))

    def check(name, request, status, reason=None, interpreter=python):
        result = bridge.consume(request, output / name, interpreter)
        (output / name / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
        if result["status"] != status or (reason is not None and reason not in result["reason"]):
            raise AssertionError((name, status, reason, result))
        if result["unrestricted_NO_claimed"] or result["general_G3_resolved"]:
            raise AssertionError("scope escalation")
        results.append({"case": name, "status": result["status"], "reason": result["reason"],
                        "solver_called": result["solver_called"], "checker_called": result["checker_called"]})
        return result

    numeric = bridge.independent_count("3/4", "1/3", "1/4", "2")
    if (numeric["delta"], numeric["rational_upper_bound"], numeric["cell_count_bound"]) != ("1/24", "200/3", 67):
        raise AssertionError(numeric)
    results.append({"case": "exact_rational_ceiling", **numeric})
    positive_b = bridge.independent_count("2", "1", "2", "0")
    if positive_b["cell_count_bound"] != 2 or positive_b["provider_verified"]:
        raise AssertionError("Generic positive b arithmetic claimed source admission")
    results.append({"case": "generic_positive_b_arithmetic", **positive_b})
    count = example("conditional-count-unknown")
    check("missing_cover", count, "UNKNOWN", "UNKNOWN_PROVIDER_VERIFIER_UNAVAILABLE")
    slot = count["count_certificate"]["slots"][0]
    for name, update, reason in [
        ("approximate_zero", {"endpoint_score": "0.00000000001"}, "exact integer or p/q"),
        ("positive_exact_score", {"endpoint_score": "1/100000000000"}, "exact zero"),
        ("invented_floor", {"survival_floor_evidence": None}, "Unobserved survival floors"),
        ("zero_floor", {"b": "0"}, "strictly positive"),
        ("negative_modulus", {"M": "-1"}, "nonnegative"),
        ("floating_epsilon", {"epsilon": 0.5}, "Floating"),
    ]:
        request = copy.deepcopy(count)
        request["count_certificate"]["slots"][0].update(update)
        check(name, request, "REFUSED_REQUEST", reason)
    request = copy.deepcopy(count)
    request["count_certificate"]["provider_evidence"] = True
    check("boolean_provider", request, "REFUSED_REQUEST", "must be an object")
    request = copy.deepcopy(count)
    request["count_certificate"]["all_core_coverage"] = True
    check("boolean_coverage", request, "REFUSED_REQUEST", "unsupported fields")
    request = copy.deepcopy(count)
    request["count_certificate"]["slots"].append(copy.deepcopy(slot))
    check("independent_duplicate_slot_fit", request, "REFUSED_REQUEST", "Repeated physical slots")
    request = copy.deepcopy(count)
    request["count_certificate"]["mode"] = "COMMON"
    check("incompatible_common_mode", request, "REFUSED_REQUEST", "INDEPENDENT or BOTH")
    request = copy.deepcopy(count)
    request["count_certificate"]["mode"] = "BOTH"
    both = check("both_compiler_missing", request, "UNKNOWN", "UNKNOWN_PROVIDER_VERIFIER_UNAVAILABLE")
    if "UNKNOWN_BOTH_MENU_COMPILER_UNAVAILABLE" not in both["integration_blockers"]:
        raise AssertionError("BOTH mismatch hidden")
    request = copy.deepcopy(count)
    request["source_request"]["mechanisms"] = ["independent", "common"]
    source_hash = bridge.digest(request["source_request"])
    request["count_certificate"]["source_request_sha256"] = source_hash
    request["count_certificate"]["slots"][0]["survival_floor_evidence"]["source_request_sha256"] = source_hash
    check("candidate_mode_union_is_not_both", request, "REFUSED_REQUEST", "alternatives do not encode BOTH")
    request = copy.deepcopy(count)
    request["count_certificate"]["source_request_sha256"] = "0" * 64
    check("cross_request_provider", request, "REFUSED_REQUEST", "changed the complete source request")
    request = example("finite-witness")
    request["source_request"]["rows"][0]["independent_slot_values"] = {"fake": "1/2"}
    check("extra_slot_fit_field", request, "REFUSED_REQUEST", "unsupported fields")
    request = example("finite-witness")
    request["source_request"]["clock_contract"] = "shared_clock"
    check("unencoded_shared_clock", request, "REFUSED_REQUEST", "actual joint encoder")
    request = example("finite-witness")
    request["source_request"]["rows"][0]["forced"] = {"unknown-original-id": 0}
    check("unknown_original_id", request, "REFUSED_REQUEST", "original named IDs")
    bad_json = output / "duplicate.json"
    bad_json.write_text('{"schema":"x","schema":"y"}')
    try:
        bridge.read_request(bad_json)
    except bridge.InvalidRequest:
        results.append({"case": "duplicate_json_fields", "status": "REFUSED_REQUEST"})
    else:
        raise AssertionError("duplicate input accepted")
    original_pin = bridge.SOURCE_MANIFEST_SHA256
    bridge.SOURCE_MANIFEST_SHA256 = "0" * 64
    try:
        result = check("pre_dispatch_authentication_failure", example("finite-witness"), "REFUSED_REQUEST", "manifest changed")
        if result["solver_called"]:
            raise AssertionError("authentication failure claimed invocation")
    finally:
        bridge.SOURCE_MANIFEST_SHA256 = original_pin

    versions = {}
    for package in bridge.PINNED_DEPENDENCIES:
        try:
            versions[package] = importlib.metadata.version(package)
        except importlib.metadata.PackageNotFoundError:
            versions[package] = None
    if versions == bridge.PINNED_DEPENDENCIES:
        check("default_available_backend", example("finite-witness"), "CERTIFIED_SOURCE_WITNESS", interpreter=sys.executable)
    else:
        default = check("default_missing_dependencies", example("finite-witness"), "UNKNOWN", "UNKNOWN_BACKEND_UNAVAILABLE", interpreter=sys.executable)
        if default["solver_called"]:
            raise AssertionError("missing backend claimed invocation")
    witness = check("finite_witness", example("finite-witness"), "CERTIFIED_SOURCE_WITNESS")
    check("all_shared_rows_excluded", example("shared-row-exclusion"), "CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS")
    check("strict_positive_boundary", example("strict-positivity-exclusion"), "CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS")
    check("bounded_positive_witness", example("bounded-witness"), "CERTIFIED_SOURCE_WITNESS")
    check("bounded_exhaustion_is_unknown", example("bounded-exhaustion"), "UNKNOWN", "UNKNOWN_BOUNDED_SEARCH_EXHAUSTED")
    original_execute = bridge._execute

    def substitute(command, workdir, name):
        execution = original_execute(command, workdir, name)
        if name == "solver":
            shutil.copyfile(output / "finite_witness/backend/RESULT.json", workdir / "backend/RESULT.json")
        return execution

    bridge._execute = substitute
    try:
        check("valid_certificate_for_other_rows", example("shared-row-exclusion"), "REFUSED_REQUEST", "changed or omitted original rows")
    finally:
        bridge._execute = original_execute
    summary = {"status": "PASS", "cases": len(results), "evidence_tier": "AUTHORED_EXECUTION_NOT_INDEPENDENT_REVIEW",
               "backend_python": str(python), "results": results}
    (output / "TEST-RESULT.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend-python", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()
    summary = run(args.backend_python, args.output)
    print(json.dumps({"status": summary["status"], "cases": summary["cases"]}))
