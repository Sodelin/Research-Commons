#!/usr/bin/env python3
"""Consume conditional count data and reuse the original exact source solver.

Count arithmetic is executable. Source-provider verification and the bridge
from bounded private slots to the original catalogue remain unavailable.
No supplied hypothesis, hash or boolean can activate that missing bridge.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import time

APP = Path(__file__).resolve().parent
ROOT = APP.parent.parent
SOURCE_MANIFEST = APP / "certified-bounds-sources.json"
SOURCE_MANIFEST_SHA256 = "4f873fa8ee34d4147712ab6eeb15abe45f71b64b0f7d4b312bd35e56b377e1b1"
SCHEMA = "same_source_certified_bounds_v1"
MAX_INPUT_BYTES = 65536
RATIONAL = re.compile(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z")
HEX = re.compile(r"[0-9a-f]{64}\Z")
PINNED_DEPENDENCIES = {"sympy": "1.14.0", "networkx": "3.5", "z3-solver": "4.15.3.0"}


class InvalidRequest(ValueError):
    pass


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":"),
                                     ensure_ascii=True).encode()).hexdigest()


def _require(condition, message):
    if not condition:
        raise InvalidRequest(message)


def _fields(value, allowed, name):
    _require(isinstance(value, dict), name + " must be an object")
    _require(not (set(value) - set(allowed)), name + " contains unsupported fields: " +
             ", ".join(sorted(set(value) - set(allowed))))


def rational(value, name="rational"):
    _require(isinstance(value, str) and len(value) <= 256 and RATIONAL.fullmatch(value),
             name + " requires an exact integer or p/q string, never a decimal or float")
    return Fraction(value)


def _qtext(value):
    return str(value.numerator) if value.denominator == 1 else str(value)


def independent_count(b, epsilon, sigma, M):
    """Exact conditional arithmetic; this function does not verify a provider."""
    values = {name: rational(value, name) for name, value in
              (("b", b), ("epsilon", epsilon), ("sigma", sigma), ("M", M))}
    _require(values["b"] > 0, "b must be strictly positive")
    _require(values["epsilon"] > 0 and values["sigma"] > 0 and values["M"] >= 0,
             "epsilon and sigma must be positive and M nonnegative")
    delta = min(values["epsilon"], values["sigma"] / (2 * (values["M"] + 1)))
    real_bound = 2 * (1 + delta) / (values["b"] * delta)
    bound = (real_bound.numerator + real_bound.denominator - 1) // real_bound.denominator
    return {"status": "CONDITIONAL_ARITHMETIC_ONLY", "parameters": {k: _qtext(v) for k, v in values.items()},
            "delta": _qtext(delta), "rational_upper_bound": _qtext(real_bound),
            "cell_count_bound": bound, "zero_length_case": "0 <= cell_count_bound",
            "ceiling_check": (bound - 1 < real_bound <= bound),
            "provider_verified": False, "source_count_bound_verified": False}


def _no_floats(value):
    if isinstance(value, float):
        raise InvalidRequest("Floating or approximate input is unsupported")
    if isinstance(value, dict):
        for item in value.values():
            _no_floats(item)
    elif isinstance(value, list):
        for item in value:
            _no_floats(item)


def _pairs(pairs):
    out = {}
    for key, value in pairs:
        _require(key not in out, "Duplicate JSON field: " + key)
        out[key] = value
    return out


def read_request(path):
    raw = Path(path).read_bytes()
    _require(len(raw) <= MAX_INPUT_BYTES, "Request exceeds 64 KiB")
    return json.loads(raw, object_pairs_hook=_pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(InvalidRequest("Nonfinite input: " + x)))


def _source_transport(source, operation):
    """Bound transport/resources only; actual source admission stays upstream."""
    _fields(source, {"observation_kind", "clock_contract", "n", "registry", "mechanisms", "taxa",
                     "task", "target_kind", "limits", "rows", "empirical_admission"}, "source_request")
    _require(source.get("observation_kind") == "exact_unranked_law", "Exact unranked laws are required")
    _require(source.get("clock_contract", "free_positive_edge_specific") == "free_positive_edge_specific",
             "Tied clocks or shared physical restrictions need their actual joint encoder")
    _require(source.get("task", "find_source") == "find_source", "This adapter supports find_source")
    n = source.get("n")
    _require(type(n) is int and 2 <= n <= 4, "Adapter resource cap is 2 <= n <= 4")
    registry = source.get("registry")
    _fields(registry, {"complete", "hybrid_ids"}, "registry")
    _require(type(registry.get("complete")) is bool, "Registry completeness must be explicit")
    ids = registry.get("hybrid_ids", [])
    _require(isinstance(ids, list) and len(ids) <= 2 and all(isinstance(x, str) and x for x in ids)
             and len(ids) == len(set(ids)), "At most two distinct nonempty original hybrid IDs")
    if operation == "finite_registry":
        _require(registry["complete"] is True, "finite_registry requires the declared complete original registry")
    if operation == "bounded_search":
        _require(registry["complete"] is False, "bounded_search requires an incomplete original registry")
    modes = source.get("mechanisms", ["independent", "common"])
    _require(isinstance(modes, list) and modes and len(set(modes)) == len(modes)
             and all(x in ("independent", "common") for x in modes), "Invalid tagged inheritance mechanisms")
    limits = source.get("limits", {})
    _fields(limits, {"seconds", "max_sources", "smt_milliseconds"}, "limits")
    _require(set(limits) == {"seconds", "max_sources", "smt_milliseconds"},
             "Explicit bounded seconds, max_sources and smt_milliseconds are required")
    for name, default, cap in (("seconds", 30, 30), ("max_sources", 1000, 1000),
                               ("smt_milliseconds", 10000, 10000)):
        value = limits.get(name, default)
        _require(type(value) is int and 1 <= value <= cap, name + " exceeds the adapter resource contract")
    rows = source.get("rows")
    _require(isinstance(rows, list) and 1 <= len(rows) <= 32, "Supply 1..32 complete rows")
    for row in rows:
        _fields(row, {"samples", "forced", "program", "readout", "quartets", "law"}, "row")
        _require(isinstance(row.get("law"), list) and len(row["law"]) <= 4096, "Bounded exact law required")
        for event in row["law"]:
            _fields(event, {"outcome", "p"}, "law event")
            _require(set(event) == {"outcome", "p"}, "A law event requires outcome and p")
            rational(event["p"], "law probability")
        samples = row.get("samples", {f"L{i}": [f"L{i}"] for i in range(n)})
        _require(isinstance(samples, dict) and all(isinstance(v, list) for v in samples.values())
                 and sum(map(len, samples.values())) <= 8, "Adapter sample cap is eight labelled copies")
        _require(not ("program" in row and "forced" in row), "Use a program or a forced row")
        program = row.get("program", [{"forced": row.get("forced", {}), "weight": "1"}])
        _require(isinstance(program, list) and 1 <= len(program) <= 32, "Bounded finite program required")
        for op in program:
            _fields(op, {"forced", "weight"}, "program operation")
            forcing = op.get("forced", {})
            _require(isinstance(forcing, dict) and set(forcing) <= set(ids)
                     and all(type(v) is int and v in (0, 1) for v in forcing.values()),
                     "Controls must retain original named IDs and incoming bits")
            rational(op.get("weight", "1"), "program weight")
    return source


def _evidence(value, source_hash, name):
    _fields(value, {"provider_id", "artifact_sha256", "source_request_sha256", "row_indices"}, name)
    _require(isinstance(value.get("provider_id"), str) and value["provider_id"], name + " needs a provider ID")
    _require(isinstance(value.get("artifact_sha256"), str) and HEX.fullmatch(value["artifact_sha256"]),
             name + " needs an artifact SHA256, not self-attestation")
    _require(value.get("source_request_sha256") == source_hash, name + " must bind the complete same-source request")
    return value


def _count_request(cert, source):
    _fields(cert, {"schema", "mode", "source_request_sha256", "slots", "provider_evidence"}, "count_certificate")
    _require(cert.get("schema") == "conditional_independent_zero_score_v1", "Unknown count certificate schema")
    _require(cert.get("mode") in ("INDEPENDENT", "BOTH"), "Independent resource bound needs INDEPENDENT or BOTH")
    source_hash = digest(source)
    _require(cert.get("source_request_sha256") == source_hash, "Count certificate changed the complete source request")
    _require(source.get("mechanisms") == ["independent"],
             "The count interface needs the INDEPENDENT source mechanism; alternatives do not encode BOTH rows")
    slots = cert.get("slots")
    _require(isinstance(slots, list) and 1 <= len(slots) <= 32, "Count data needs 1..32 distinct physical slots")
    counts, names = [], set()
    for slot in slots:
        _fields(slot, {"slot_id", "b", "epsilon", "sigma", "M", "endpoint_score", "survival_floor_evidence"}, "slot")
        name = slot.get("slot_id")
        _require(isinstance(name, str) and name and name not in names, "Repeated physical slots cannot be fitted independently")
        names.add(name)
        _require(rational(slot.get("endpoint_score"), "endpoint_score") == 0,
                 "An exact zero endpoint score is required; positive or approximate scores give no count bound")
        count = independent_count(*(slot.get(k) for k in ("b", "epsilon", "sigma", "M")))
        floor = slot.get("survival_floor_evidence")
        _require(isinstance(floor, dict), "Unobserved survival floors cannot be invented; supply a fibre-bound derivation")
        _evidence(floor, source_hash, "survival_floor_evidence")
        indices = floor.get("row_indices")
        _require(isinstance(indices, list) and indices and len(indices) == len(set(indices))
                 and all(type(x) is int and 0 <= x < len(source["rows"]) for x in indices),
                 "Survival floor must cite supplied rows of this physical source")
        counts.append({"slot_id": name, **count})
    evidence = cert.get("provider_evidence")
    if evidence is not None:
        _evidence(evidence, source_hash, "provider_evidence")
    # Intentionally no caller-extensible proof-provider registry. No published
    # executable all-core/analytic verifier currently exists for this interface.
    return {"conditional_counts": counts, "submitted_provider_evidence": copy.deepcopy(evidence),
            "provider_verified": False,
            "missing_provider_obligations": ["source_faithful_all_core_and_piece_coverage",
              "actual_equal_arm_admission_and_chronology", "same_source_nonnegative_additive_score",
              "positive_weighted_exact_endpoint_annihilation", "uniform_weak_cell_modulus",
              "given_fibre_uniform_independent_survival_floor"],
            "integration_blockers": ["UNKNOWN_PROVIDER_VERIFIER_UNAVAILABLE",
                                      "UNKNOWN_CORE_CATALOGUE_COMPILER_UNAVAILABLE"] +
                                    (["UNKNOWN_BOTH_MENU_COMPILER_UNAVAILABLE"] if cert["mode"] == "BOTH" else []),
            "bound_applied_to_catalogue": False}


def _manifest(stage=None):
    raw = SOURCE_MANIFEST.read_bytes()
    _require(hashlib.sha256(raw).hexdigest() == SOURCE_MANIFEST_SHA256, "Inherited adapter manifest changed")
    manifest = json.loads(raw)
    for row in manifest["files"]:
        path = ROOT / row["source"]
        data = path.read_bytes()
        _require(not path.is_symlink() and len(data) == row["bytes"] and
                 hashlib.sha256(data).hexdigest() == row["sha256"], "Inherited source authentication failed: " + row["source"])
        if stage is not None:
            target = stage / row["runtime_relative"]
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    return manifest


def _authenticate_runtime(stage):
    for row in _manifest()["files"]:
        path = stage / row["runtime_relative"]
        data = path.read_bytes()
        _require(not path.is_symlink() and len(data) == row["bytes"] and
                 hashlib.sha256(data).hexdigest() == row["sha256"],
                 "Staged runtime authentication failed: " + row["runtime_relative"])


def _limits():
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_AS, (512 * 2**20, 512 * 2**20))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 2**20, 16 * 2**20))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def _execute(command, workdir, name):
    start = time.monotonic()
    receipt = {"command": list(map(str, command)), "invoked": False, "timeout": False}
    with (workdir / (name + ".stdout")).open("wb") as out, (workdir / (name + ".stderr")).open("wb") as err:
        try:
            proc = subprocess.Popen(command, cwd=workdir, stdout=out, stderr=err,
                                    env={"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}, preexec_fn=_limits)
            receipt["invoked"] = True
            try:
                receipt["returncode"] = proc.wait(timeout=45)
            except subprocess.TimeoutExpired:
                proc.kill()
                receipt.update(returncode=proc.wait(), timeout=True)
        except OSError as error:
            receipt["error"] = str(error)
    receipt["elapsed_seconds"] = time.monotonic() - start
    (workdir / (name + ".execution.json")).write_text(json.dumps(receipt, indent=2) + "\n")
    return receipt


def _dependencies(python, workdir):
    code = "import importlib.metadata as m,json; d={};\nfor p in ['sympy','networkx','z3-solver']:\n try: d[p]=m.version(p)\n except m.PackageNotFoundError: d[p]=None\nprint(json.dumps(d))"
    receipt = _execute([python, "-I", "-B", "-c", code], workdir, "dependency-probe")
    if receipt.get("returncode") != 0:
        return {"available": False, "versions": {}, "execution": receipt}
    versions = json.loads((workdir / "dependency-probe.stdout").read_text())
    return {"available": versions == PINNED_DEPENDENCIES, "versions": versions,
            "required": PINNED_DEPENDENCIES, "execution": receipt}


def consume(request, workdir, python_executable=None):
    """Return a complete receipt. The caller supplies a fresh empty workdir."""
    workdir = Path(workdir).absolute()
    _require(not workdir.exists() or (workdir.is_dir() and not any(workdir.iterdir())), "workdir must be fresh and empty")
    workdir.mkdir(parents=True, exist_ok=True)
    base = {"schema": "same_source_certified_bounds_result_v1", "status": "UNKNOWN",
            "request": copy.deepcopy(request), "request_sha256": digest(request),
            "execution_mode": "FRESH_RUN", "solver_called": False, "checker_called": False,
            "source_feasibility_certified": False, "unrestricted_NO_claimed": False,
            "general_G3_resolved": False, "Lean_kernel_verification_claimed": False,
            "statistical_coverage_verified": False}
    try:
        _fields(request, {"schema", "operation", "source_request", "count_certificate", "max_extra_hybrids"}, "request")
        _require(request.get("schema") == SCHEMA, "Unknown adapter schema")
        _no_floats(request)
        _require(len(json.dumps(request).encode()) <= MAX_INPUT_BYTES, "Request exceeds 64 KiB")
        operation = request.get("operation")
        _require(operation in ("conditional_count", "finite_registry", "bounded_search"), "Unknown operation")
        source = _source_transport(request.get("source_request"), operation)
        base["source_request_sha256"] = digest(source)
        base["source_manifest"] = _manifest()
        if operation == "conditional_count":
            _require("max_extra_hybrids" not in request, "A private-slot bound is not a hybrid search budget")
            base.update(_count_request(request.get("count_certificate"), source))
            return {**base, "reason": "UNKNOWN_PROVIDER_VERIFIER_UNAVAILABLE",
                    "scope": "Exact conditional arithmetic only; neither source coverage nor a bounded source catalogue has been verified."}
        _require("count_certificate" not in request, "A conditional count cannot be applied without its source-provider and core compiler")
        if operation == "bounded_search":
            extra = request.get("max_extra_hybrids")
            _require(type(extra) is int and 0 <= extra <= 2 and len(source["registry"].get("hybrid_ids", [])) + extra <= 2,
                     "Bounded search budget must be 0..2 extra hybrids, at most two total")
        else:
            _require("max_extra_hybrids" not in request, "finite_registry has no extra hybrid budget")
        selected = str(python_executable or sys.executable)
        python = str(Path(shutil.which(selected) or selected).absolute())
        base["dependencies"] = _dependencies(python, workdir)
        if not base["dependencies"]["available"]:
            return {**base, "reason": "UNKNOWN_BACKEND_UNAVAILABLE",
                    "integration_blockers": ["Pinned existing exact backend dependencies missing or mismatched"],
                    "scope": "The original exact source solver was not invoked."}
        stage = workdir / "runtime"
        _manifest(stage)
        original = workdir / "SOURCE-REQUEST.json"
        original.write_text(json.dumps(source, indent=2) + "\n")
        result_dir = workdir / "backend"
        result_dir.mkdir()
        command = [python, "-B", str(stage / ("solver.py" if operation == "finite_registry" else "bounded_search.py")),
                   str(original), "--output", str(result_dir)]
        if operation == "bounded_search":
            command += ["--max-extra-hybrids", str(request["max_extra_hybrids"])]
        execution = _execute(command, workdir, "solver")
        base.update(solver_called=execution["invoked"], solver_execution=execution)
        result_path = result_dir / ("RESULT.json" if operation == "finite_registry" else "SEARCH-RESULT.json")
        if execution.get("timeout") or not result_path.is_file():
            return {**base, "reason": "UNKNOWN_RESOURCE_OR_BACKEND_FAILURE", "scope": "No checked source decision; logs preserved."}
        result = json.loads(result_path.read_text())
        base["backend_result"] = result
        _require(result.get("request") == source and result.get("request_sha256") == digest(source),
                 "Backend certificate changed or omitted original rows, IDs, modes or shared source request")
        _authenticate_runtime(stage)
        if result["status"] == "INVALID_INPUT":
            return {**base, "status": "REFUSED_REQUEST", "reason": result.get("reason", "Invalid source request")}
        if result["status"] not in ("SAT_ONE_COHERENT_ADMITTED_SOURCE", "SAT_ADMITTED_SOURCE_UNKNOWN_SIZE_SEARCH", "UNSAT_COMPLETE_KNOWN_REGISTRY"):
            return {**base, "reason": result["status"], "scope": "No exact source witness or complete checked covered-class exclusion."}
        checker = stage / ("verify_certificate.py" if operation == "finite_registry" else "verify_search.py")
        check_execution = _execute([python, "-B", str(checker), str(result_path), "--replay-backend"], workdir, "checker")
        base.update(checker_called=check_execution["invoked"], checker_execution=check_execution)
        if check_execution.get("returncode") != 0:
            return {**base, "reason": "UNKNOWN_CERTIFICATE_CHECK_FAILED", "scope": "Producer output has not passed semantic recomputation."}
        base["semantic_check"] = json.loads((workdir / "checker.stdout").read_text())
        _authenticate_runtime(stage)
        if result["status"].startswith("SAT"):
            return {**base, "status": "CERTIFIED_SOURCE_WITNESS", "reason": result["status"],
                    "source_feasibility_certified": True,
                    "scope": "One actual strict original source and one physical assignment fit every supplied row; exact software recomputation, no Lean claim."}
        return {**base, "status": "CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS",
                "reason": "UNSAT_COMPLETE_KNOWN_REGISTRY",
                "covered_class": {"n": source["n"], "registry": source["registry"],
                                  "mechanisms": source.get("mechanisms", ["independent", "common"]),
                                  "clock_contract": "free_positive_edge_specific"},
                "scope": "Every source in the declared complete finite registry only; no unknown-size or unrestricted NO."}
    except (InvalidRequest, KeyError, TypeError, ValueError, OSError) as error:
        return {**base, "status": "REFUSED_REQUEST", "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--python-executable", type=Path)
    args = parser.parse_args()
    try:
        _require(not args.output.exists(), "Output must be a new directory")
        request = read_request(args.request)
        result = consume(request, args.output, args.python_executable)
    except (InvalidRequest, OSError, ValueError) as error:
        print(json.dumps({"status": "REFUSED_REQUEST", "reason": str(error)}))
        return 1
    (args.output / "REQUEST.json").write_text(json.dumps(request, indent=2) + "\n")
    (args.output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "reason": result["reason"], "result": str(args.output / "RESULT.json")}, indent=2))
    return 0 if result["status"].startswith("CERTIFIED_") else (2 if result["status"] == "UNKNOWN" else 1)


if __name__ == "__main__":
    raise SystemExit(main())
