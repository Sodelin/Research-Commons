#!/usr/bin/env python3
"""Strict independent consumer for the supplied-calendar application.

The TABLE reference uses coupled-generator spectral rows and copy-based
boundary marginalization. Native history recurrences and binaries are not
invoked. Provider UNKNOWN authenticates framing, never proves exhaustion.
The deployment adapter captures this file and all imported reference bytes.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

from certificate_check import MAX_REQUEST_BYTES, MAX_CERTIFICATE_BYTES, read_bounded, require
import source_calendar_oracle as calendar

SCHEMA = "source_calendar_result_v1"
WORD_SCHEMA = "source_word_result_v1"
ERROR_KINDS = {"INVALID_REQUEST", "INTERNAL", "EXECUTION_FAILURE"}
UINT64_MAX = 2**64 - 1
MAX_JSON_DEPTH = 64
SENTINEL = "application-input"


def canonical_json(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def no_duplicates(pairs):
    answer = {}
    for key, value in pairs:
        require(key not in answer, "duplicate JSON object key")
        answer[key] = value
    return answer


def forbidden_number(_token):
    raise ValueError("floating or nonfinite JSON number")


def strict_json(raw, cap, *, canonical=False):
    require(type(raw) is bytes and len(raw) <= cap, "JSON byte cap exceeded")
    text = raw.decode("utf-8", errors="strict")
    # Bound nesting before the standard decoder recursively constructs values.
    quoted = escaped = False
    depth = 0
    for character in text:
        if quoted:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                quoted = False
        elif character == '"':
            quoted = True
        elif character in "[{":
            depth += 1
            require(depth <= MAX_JSON_DEPTH, "JSON nesting exceeds contract cap")
        elif character in "]}":
            depth -= 1
            require(depth >= 0, "unbalanced JSON nesting")
    require(not quoted and depth == 0, "incomplete JSON framing")
    value = json.loads(text, object_pairs_hook=no_duplicates,
                       parse_float=forbidden_number, parse_constant=forbidden_number)
    require(type(value) is dict, "JSON root must be an object")
    if canonical:
        require(raw == canonical_json(value), "noncanonical result JSON bytes")
    return value


def parse_request(raw):
    request = strict_json(raw, MAX_REQUEST_BYTES)
    context = request.get("context")
    if type(context) is dict:
        vertices, edges = context.get("vertices"), context.get("edges")
        if type(vertices) is int and type(edges) is list:
            # Every vertex in a finite root-reachable graph is reached by an
            # original edge, except the root. Reject impossible dimensions
            # before a downstream graph validator can allocate by that count.
            require(vertices <= len(edges) + 1, "vertex count cannot be root reachable from supplied edges")
    try:
        calendar.check_request(request)
    except (KeyError, TypeError, IndexError, OverflowError) as error:
        raise ValueError("malformed supplied-calendar request") from error
    return request


def same(actual, expected, message):
    require(canonical_json(actual) == canonical_json(expected), message)


def common_details(raw_request, status):
    return {"operation": "CALENDAR", "status": status, "result_valid": True,
        "request_sha256": hashlib.sha256(raw_request).hexdigest(),
        "scope": "SUPPLIED_CALENDAR_GENEALOGY_STATE_TABLE",
        "certificate_valid": False, "formal_table_checked": False,
        "independent_all_coefficients_checked": False,
        "calendar_agenda_checked": False, "physical_substitutions_checked": False,
        "word_work_checked": False, "provider_work_checked": False,
        "provider_exhaustion_verified": False, "source_admission_verified": False,
        "complete_source_registry_verified": False, "observation_law_admission_verified": False,
        "statistical_confidence_verified": False, "physical_survival_image_verified": False,
        "full_joint_calendar_law_verified": False, "full_solver_verified": False}


def private_word(frame):
    converted = copy.deepcopy(frame)
    converted["schema"] = "source_word_probe_v1"
    converted["fixture"] = SENTINEL
    return converted


def public_word(frame):
    converted = copy.deepcopy(frame)
    converted.pop("fixture")
    converted["schema"] = WORD_SCHEMA
    return converted


def natural(value, message):
    require(type(value) is int and 0 <= value <= UINT64_MAX, message)


def polynomial_rows(rows, dimension):
    require(type(rows) is list, "table rows must be an array")
    for row in rows:
        require(type(row) is dict and set(row) == {"view", "witness", "coefficients"},
                "unknown or missing table row field")
        polynomial = row["coefficients"]
        require(type(polynomial) is list and polynomial, "empty retained polynomial")
        previous = None
        for term in polynomial:
            require(type(term) is list and len(term) == 2 and type(term[0]) is list
                    and len(term[0]) == dimension, "wrong monomial arity")
            powers = term[0]
            for power in powers:
                natural(power, "invalid monomial exponent")
            exponent = tuple(powers)
            require(previous is None or previous < exponent, "duplicate or unordered monomial")
            previous = exponent
            require(calendar.rational(term[1]) != 0, "explicit zero coefficient")


def stage_valid(stage, child):
    if type(stage) is int:
        require(0 <= stage < len(child["word"]), "UNKNOWN letter stage outside word")
        return
    require(stage in ("INITIAL", "COMPLETION"), "unknown UNKNOWN stage")
    if stage == "COMPLETION":
        require(child["terminal"] == "ANCESTRAL_COMPLETE", "completion UNKNOWN lacks completion request")


def word_unknown(request, child, actual):
    base = {"schema": WORD_SCHEMA, "request": child,
            "variables": calendar.ref.variables(child), "source_admission_verified": False,
            "status": "UNKNOWN"}
    frame = actual["word_result"]
    require(type(frame) is dict and set(frame) == set(base) | {"limit"}, "bad UNKNOWN word fields")
    for key, value in base.items():
        same(frame[key], value, "UNKNOWN child changed " + key)
    limit = frame["limit"]
    require(type(limit) is dict and set(limit) == {"stage", "kind", "required", "cap"},
            "bad UNKNOWN limit fields")
    stage, kind, required, cap = (limit[key] for key in ("stage", "kind", "required", "cap"))
    require(type(kind) is str, "UNKNOWN kind must be a string")
    natural(required, "UNKNOWN required count is not uint64")
    natural(cap, "UNKNOWN cap is not uint64")
    require(required > cap, "UNKNOWN does not exceed its supplied cap")
    stage_valid(stage, child)
    population = actual["consumer_population"]
    original = child["context"]
    if kind in calendar.ref.DEFAULT_LIMITS:
        same(cap, request["word_limits"][kind], "UNKNOWN changed wrapper cap")
        require(population is None, "wrapper UNKNOWN invented a population")
        if kind in ("initial_assignments", "initial_terms"):
            require(stage == "INITIAL", "initial limit outside initialization")
            exact_required = 2**len(original["hybrids"]) if kind == "initial_assignments" else 3**len(original["hybrids"])
            require(required == exact_required, "initial raw counting changed")
        elif kind in ("queries", "branches", "term_products"):
            require(stage != "INITIAL", "transition limit during initialization")
        return "WRAPPER_LIMIT_FRAME"
    provider_kinds = {
        "EPOCH": {"Calls": "calls", "Destinations": "destinations", "LiftedTerms": "lifted_terms",
                  "Branches": "branches", "TermProducts": "term_products"},
        "BOUNDARY": {"Assignments": "assignments", "Destinations": "destinations",
                     "TermContributions": "term_contributions"},
        "COMPLETION": {"Calls": "calls", "Destinations": "destinations", "LiftedTerms": "lifted_terms"}}
    parts = kind.split(":")
    require(len(parts) == 2 and parts[0] in provider_kinds and parts[1] in provider_kinds[parts[0]],
            "UNKNOWN inner limit kind is not declared")
    provider, name = parts
    same(cap, request["provider_limits"][provider.lower()][provider_kinds[provider][name]],
         "UNKNOWN changed inner provider cap")
    if provider == "COMPLETION":
        require(stage == "COMPLETION", "completion provider limit outside completion")
        same(population, ["A", original["root"]], "completion UNKNOWN changed ancestral population")
    else:
        require(type(stage) is int, "inner transition UNKNOWN lacks a letter stage")
        letter = child["word"][stage]
        if provider == "BOUNDARY":
            require(letter[0] in ("EXIT", "ENTER") and population is None,
                    "boundary UNKNOWN has wrong action/population")
        else:
            require(letter[0] == "INTERVAL", "epoch UNKNOWN at a boundary letter")
            require(type(population) is list and len(population) == 2 and type(population[1]) is int,
                    "epoch UNKNOWN lacks an original population")
            require((population[0] == "E" and 0 <= population[1] < len(original["edges"])) or
                    (population[0] == "A" and population[1] == original["root"]),
                    "epoch UNKNOWN population outside original registry")
    return "PROVIDER_LIMIT_FRAME_ONLY"


def verify_certificate(raw_request, raw_result, exit_code=None):
    result = strict_json(raw_result, MAX_CERTIFICATE_BYTES, canonical=True)
    try:
        request = parse_request(raw_request)
    except (ValueError, UnicodeError, OverflowError):
        same(result, {"schema": SCHEMA, "status": "ERROR", "error": "INVALID_REQUEST"},
             "invalid input did not receive exact INVALID_REQUEST refusal")
        require(exit_code is None or exit_code == 1, "input refusal has wrong exit code")
        return common_details(raw_request, "REFUSED") | {"native_error": "INVALID_REQUEST"}
    if result.get("status") == "ERROR":
        require(set(result) == {"schema", "status", "error"} and result["schema"] == SCHEMA
                and result["error"] in {"INTERNAL", "EXECUTION_FAILURE"}, "invalid error frame for admitted request")
        require(exit_code is None or exit_code == 1, "native error has wrong exit code")
        return common_details(raw_request, "ERROR") | {"native_error": result["error"]}
    requirements, agenda, child, compiler_limit = calendar.compile_calendar(request)
    base = {"schema": SCHEMA, "request": request, "source_admission_verified": False,
            "requirements": requirements}
    for key, value in base.items():
        require(key in result, "result omitted " + key)
        same(result[key], value, "result changed " + key)
    status = result.get("status")
    require(status in ("TABLE", "UNKNOWN"), "unknown result status")
    require(exit_code is None or exit_code == (0 if status == "TABLE" else 2), "status/exit pairing differs")
    details = common_details(raw_request, status)
    if compiler_limit:
        same(result, base | {"status": "UNKNOWN", "unknown_scope": "COMPILER", "limit": compiler_limit},
             "compiler UNKNOWN lost first-limit priority or produced partial output")
        return details | {"unknown_scope": "COMPILER", "limit": compiler_limit,
                          "compiler_requirements_checked": True, "unknown_exhaustion_verified": True}
    extra = {"agenda", "word_result"} | ({"unknown_scope", "consumer_population"} if status == "UNKNOWN" else set())
    require(set(result) == set(base) | {"status"} | extra, "unknown or missing calendar result field")
    same(result["agenda"], agenda, "calendar agenda or physical substitutions changed")
    details.update(calendar_agenda_checked=True, physical_substitutions_checked=True)
    if status == "UNKNOWN":
        require(result["unknown_scope"] == "WORD", "UNKNOWN has wrong outer scope")
        qualification = word_unknown(request, child, result)
        return details | {"unknown_scope": "WORD", "limit": result["word_result"]["limit"],
            "consumer_population": result["consumer_population"], "limit_check": qualification,
            "unknown_exhaustion_verified": False}
    # Inner native recurrence budgets are operational. The independent spectral
    # calculation validates the mathematical table and logical wrapper work,
    # without claiming to count the native provider's recursive/lift operations.
    expected, internal = calendar.ref.expected_probe(SENTINEL, child)
    require(expected["status"] == "TABLE", "producer TABLE exceeds independently checked word wrapper caps")
    frame = result["word_result"]
    require(type(frame) is dict and frame.get("schema") == WORD_SCHEMA, "bad nested table schema")
    public_expected = public_word(expected)
    require(set(frame) == set(public_expected), "unknown or missing nested table field")
    polynomial_rows(frame["rows"], len(public_expected["variables"]))
    checked = calendar.ref.check_probe(private_word(frame), expected, internal)
    # Strict JSON comparison additionally distinguishes bool/int monomial tokens
    # even though Python's ordinary numeric equality identifies True and 1.
    expected_rows = {calendar.ref.epoch.exact_json(row["view"]): row["coefficients"] for row in expected["rows"]}
    for row in frame["rows"]:
        same(row["coefficients"], expected_rows[calendar.ref.epoch.exact_json(row["view"])],
             "coefficient JSON types changed")
    details.update(formal_table_checked=True, independent_all_coefficients_checked=True,
                   word_work_checked=True, full_view_rows=checked["full_view_rows"],
                   literal_rows=checked["literal_rows"], terms=checked["terms"],
                   reference_algorithm="COUPLED_GENERATOR_SPECTRAL_AND_COPY_MARGINAL_BOUNDARY")
    return details


def check_response(raw_request, raw_result, exit_code):
    return verify_certificate(raw_request, raw_result, exit_code)["status"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", required=True, type=Path)
    parser.add_argument("--certificate", required=True, type=Path)
    parser.add_argument("--exit-code", type=int)
    args = parser.parse_args()
    checked = verify_certificate(read_bounded(args.request, MAX_REQUEST_BYTES),
                                 read_bounded(args.certificate, MAX_CERTIFICATE_BYTES), args.exit_code)
    sys.stdout.buffer.write(canonical_json(checked))
    return 0 if checked["status"] == "TABLE" else 2 if checked["status"] == "UNKNOWN" else 1


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, UnicodeError, OSError, OverflowError, TypeError, KeyError, IndexError) as error:
        sys.stdout.buffer.write(canonical_json({"result_valid": False, "certificate_valid": False,
                                               "error": str(error)}))
        sys.exit(1)
