#!/usr/bin/env python3
"""Bounded private extractor review; no Lean or accepted native producer runs.

Deterministic old Fraction elimination is an attributed differential oracle.
Certificate equations and saved original whole-row transfers use exact Fraction
arithmetic, without calling the elimination routine for certificate checking.
"""
from __future__ import annotations
import argparse
import copy
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import subprocess
import time
import types

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
COMMONS = PACKET.parent.parent
OLD_SHA = "4760fcd13bb26f648943d9e51a0273e130baa4bf80f56931b305a9874591727e"
HISTORY_SHA = "9bdecf2bbf8ba803b0eba6e7be0cc8ad7595085a685ec1725a3bb3a07f6b1928"

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False) + "\n").encode()

def read_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite")))

def qwire(q):
    return f"{q.numerator}/{q.denominator}"

def rational(token):
    require(type(token) is str, "rational string required")
    value = Fraction(token)
    require(qwire(value) == token, "noncanonical rational")
    return value

def geom(length, z):
    return sum((z ** i for i in range(length)), Fraction(0))

def input_request(m, atom_values, **limits):
    cap = {"atoms": 64, "matrix_cells": 8192, "rational_bits": 4096}
    cap.update(limits)
    return {"schema": "g6_rational_compression_request_v1", "M": m,
            "atoms": [{"z": qwire(z), "alpha": qwire(alpha)} for z, alpha in atom_values], "limits": cap}

def verify_equations(raw, result):
    """Mathematical check only: original IDs, positive weights and moments."""
    request = read_json(raw)
    require(result["status"] == "COMPRESSED", "not a finite compression")
    require(result["request_raw"].encode() == raw and result["request"] == request, "foreign request")
    atoms = [(rational(atom["z"]), rational(atom["alpha"])) for atom in request["atoms"]]
    require(all(0 < z < 1 and alpha >= 0 for z, alpha in atoms), "input domain")
    m = request["M"]
    require(len(result["output_atoms"]) <= m - 1, "output cardinality")
    ids, selected = [], []
    for atom in result["output_atoms"]:
        index = atom["input_index"]
        require(type(index) is int and 0 <= index < len(atoms), "original index")
        beta = rational(atom["beta"])
        require(beta > 0, "positive weight")
        ids.append(index)
        selected.append((atoms[index][0], beta))
    require(ids == sorted(set(ids)), "strict original index order")
    mass = sum((a for _, a in atoms), Fraction(0))
    require(mass == sum((b for _, b in selected), Fraction(0)) == rational(result["mass"]), "mass")
    require(len(result["tail_moments"]) == m - 2, "tail census")
    for level, tail in zip(range(3, m + 1), result["tail_moments"]):
        c = level * (level - 1) // 2
        lhs = sum((a * geom(c, z) for z, a in atoms), Fraction(0))
        rhs = sum((b * geom(c, z) for z, b in selected), Fraction(0))
        require(tail["level"] == level and lhs == rhs == rational(tail["moment"]), "tail moment")
    require(all(result[key] is False for key in ("source_admission_verified", "source_factor_realization_verified",
                                                "arbitrary_real_extraction_verified")), "scientific gates")
    return selected

def process_limits():
    os.setsid()
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_AS, (768 * 1024 * 1024,) * 2)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

def run_binary(binary, args, directory, name, stdin=None):
    started = time.monotonic()
    child = subprocess.Popen([str(binary), *map(str, args)], stdin=subprocess.PIPE if stdin is not None else subprocess.DEVNULL,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, preexec_fn=process_limits)
    timed_out = False
    try:
        stdout, stderr = child.communicate(stdin, timeout=45)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(child.pid, signal.SIGKILL)
        stdout, stderr = child.communicate()
    (directory / (name + ".stdout")).write_bytes(stdout)
    (directory / (name + ".stderr")).write_bytes(stderr)
    require(len(stdout) <= 4 * 1024 * 1024, "process result frame bound")
    receipt = {"args": list(map(str, args)), "process_started": True, "exit_code": child.returncode,
               "timed_out": timed_out, "elapsed_seconds": round(time.monotonic() - started, 6),
               "stdout_sha256": digest(stdout), "stderr_sha256": digest(stderr),
               "limits": {"wall_seconds": 45, "cpu_seconds": 30, "address_bytes": 768 * 1024 * 1024}}
    require(not timed_out, "process timed out")
    return receipt, stdout

def run(args):
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    args.created_output = True
    capture = output / "captured_sources"
    capture.mkdir()
    binary = args.binary.resolve()
    watched = {binary: digest(binary.read_bytes())}
    old_path = PACKET / "design/review_g6_source_generators.py"
    history_path = PACKET / "design/evidence/g6-saved-generator-review-1/RECEIPT.json"
    old_raw, history_raw = old_path.read_bytes(), history_path.read_bytes()
    require(digest(old_raw) == OLD_SHA and digest(history_raw) == HISTORY_SHA, "attributed oracle/history identity")
    (capture / old_path.name).write_bytes(old_raw)
    (capture / "historical-RECEIPT.json").write_bytes(history_raw)
    old = types.ModuleType("private_pinned_inherited_fraction_compression")
    old.__file__ = str(old_path)
    exec(compile(old_raw, str(old_path), "exec"), old.__dict__)
    history = read_json(history_raw)
    require(history["pass"] is True and history["compression_source_row_checks"] == 1363, "historical acceptance")
    for path in [old_path, history_path, HERE / "Cargo.toml", HERE / "Cargo.lock", HERE / "src/lib.rs", HERE / "src/main.rs",
                 HERE / "tests/certificates.rs", Path(__file__).resolve(),
                 HERE.parent / "notes/G6-RATIONAL-COMPRESSION-CONTRACT-2-20261010T1632Z.md"]:
        watched[path] = digest(path.read_bytes())
    cases, controls, results = [], [], {}

    def execute(name, request, expected="COMPRESSED", expected_kind=None, expected_stage=None):
        raw = canonical(request) if isinstance(request, dict) else request
        (output / (name + ".request.json")).write_bytes(raw)
        produced, data = run_binary(binary, ["solve", "--request", output / (name + ".request.json")], output, name + ".producer")
        frame = read_json(data)
        require(canonical(frame) == data, "noncanonical result")
        require(frame["status"] == expected, name + " unexpected status")
        require(produced["exit_code"] == {"COMPRESSED": 0, "UNKNOWN": 2, "ERROR": 1}[expected], "status/exit pairing")
        if expected == "ERROR":
            require(frame == {"schema": "g6_rational_compression_result_v1", "status": "ERROR", "error": "INVALID_REQUEST"}, "error envelope")
            controls.append({"control": name, "process": produced, "pass": True})
            return frame
        require(frame["request_raw"].encode() == raw and frame["request"] == read_json(raw), "request binding")
        if expected == "COMPRESSED":
            verify_equations(raw, frame)
        else:
            require(not any(key in frame for key in ("output_atoms", "mass", "tail_moments")), "UNKNOWN partial certificate")
            require(frame["limit"]["required"] > frame["limit"]["cap"], "UNKNOWN bound")
            if expected_kind: require(frame["limit"]["kind"] == expected_kind, name + " limit kind")
            if expected_stage: require(frame["limit"]["stage"] == expected_stage, name + " limit stage")
        certificate = output / (name + ".result.json")
        certificate.write_bytes(data)
        checked, checked_raw = run_binary(binary, ["check", "--request", output / (name + ".request.json"),
                                                  "--certificate", certificate], output, name + ".checker")
        check = read_json(checked_raw)
        require(checked["exit_code"] == 0 and check["status"] == "ACCEPT" and check["certificate_valid"] is (expected == "COMPRESSED"), "native certificate acceptance")
        require(check["producer_work_verified"] is False and check["resource_exhaustion_verified"] is False, "work/exhaustion promotion")
        result = {"fixture": name, "status": expected, "producer": produced, "checker": checked, "pass": True}
        (cases if expected == "COMPRESSED" else controls).append(result)
        results[name] = (raw, frame)
        return frame

    differential = []
    for case in history["compression_cases"][:3]:
        m = case["cap"]
        atoms = [(Fraction(z), Fraction(a)) for z, a in case["input_atoms"]]
        actual = execute("historicalM" + str(m), input_request(m, atoms))
        old_atoms, steps = old.compress(m, atoms)
        old_indices = [{"input_index": next(i for i, (given, _) in enumerate(atoms) if z == given), "beta": qwire(beta)} for z, beta in old_atoms]
        require(actual["output_atoms"] == old_indices and actual["work"]["elimination_steps"] == steps, "deterministic inherited extractor drift")
        require([[qwire(z), qwire(a)] for z, a in old_atoms] == case["output_atoms"], "saved inherited certificate drift")
        differential.append({"M": m, "pass": True, "output_atoms": old_indices, "elimination_steps": steps})
    execute("empty", input_request(4, []))
    execute("allZero", input_request(4, [(Fraction(1, 3), Fraction(0)), (Fraction(2, 3), Fraction(0))], rational_bits=2))
    duplicate = execute("zeroAndDuplicateIds", input_request(2, [(Fraction(1, 3), Fraction(0)),
        (Fraction(1, 2), Fraction(2)), (Fraction(1, 2), Fraction(3)), (Fraction(2, 3), Fraction(0))]))
    require(duplicate["output_atoms"] == [{"input_index": 1, "beta": "5/1"}], "duplicate original identity")
    two = [(Fraction(1, 3), Fraction(1)), (Fraction(2, 3), Fraction(1))]
    execute("exactMatrixAndAtoms", input_request(2, two, atoms=2, matrix_cells=2))
    execute("matrixOneBelow", input_request(2, two, matrix_cells=1), "UNKNOWN", "matrix_cells", "MOMENTS")
    execute("atomsOneBelow", input_request(2, two, atoms=1), "UNKNOWN", "atoms", "INPUT")
    execute("inputBits", input_request(2, two, rational_bits=1), "UNKNOWN", "rational_bits", "INPUT")
    for name, m, atoms, cap, stage in [
        ("momentBits", 4, [(Fraction(1, 2), Fraction(1))] * 4, 2, "MOMENTS"),
        ("rrefBits", 3, [(Fraction(1, 3), Fraction(1)), (Fraction(1, 2), Fraction(1)), (Fraction(2, 3), Fraction(1))], 5, "RREF"),
        ("updateBits", 2, [(Fraction(1, 2), Fraction(1))] * 4, 2, "UPDATE"),
        ("certificateBits", 4, [(Fraction(1, 2), Fraction(1))], 2, "CERTIFICATE")]:
        execute(name, input_request(m, atoms, rational_bits=cap), "UNKNOWN", "rational_bits", stage)
    execute("matrixBeforeGeometry", input_request(4, [(Fraction(1, 2), Fraction(1))] * 4,
        matrix_cells=0, rational_bits=2), "UNKNOWN", "matrix_cells", "MOMENTS")
    bad = input_request(2, two, atoms=0, matrix_cells=0, rational_bits=0)
    bad["atoms"][1]["z"] = "1/1"
    execute("domainBeforeLimits", bad, "ERROR")
    base_raw = canonical(input_request(2, two))
    for name, raw in [("duplicateField", base_raw.replace(b'"M":2', b'"M":2,"M":2', 1)),
                      ("floatRejected", base_raw.replace(b'"M":2', b'"M":2.0', 1)),
                      ("boolRejected", base_raw.replace(b'"M":2', b'"M":true', 1)),
                      ("uint64Oversize", base_raw.replace(b'"M":2', b'"M":18446744073709551615', 1)),
                      ("frameOversize", b' ' * 65537)]:
        execute(name, raw, "ERROR")
    minus_zero = canonical(input_request(4, [], atoms=0)).replace(b'"atoms":0', b'"atoms":-0')
    execute("minusZero", minus_zero)

    def forge(name, from_name, mutate):
        raw, before = results[from_name]
        frame = copy.deepcopy(before)
        mutate(frame)
        (output / (name + ".request.json")).write_bytes(raw)
        (output / (name + ".result.json")).write_bytes(canonical(frame))
        checked, data = run_binary(binary, ["check", "--request", output / (name + ".request.json"),
                                           "--certificate", output / (name + ".result.json")], output, name + ".checker")
        require(checked["exit_code"] == 1 and read_json(data)["status"] == "REJECT", "forged certificate accepted: " + name)
        controls.append({"control": name, "process": checked, "pass": True})
    def balanced(frame):
        frame["output_atoms"][0]["beta"] = qwire(Fraction(frame["output_atoms"][0]["beta"]) + Fraction(1, 1000))
        frame["output_atoms"][1]["beta"] = qwire(Fraction(frame["output_atoms"][1]["beta"]) - Fraction(1, 1000))
    forge("sameMassWrongTail", "historicalM3", balanced)
    forge("duplicateIndex", "historicalM3", lambda f: f["output_atoms"][1].update(input_index=f["output_atoms"][0]["input_index"]))
    forge("outsideOriginalIndex", "historicalM3", lambda f: f["output_atoms"][1].update(input_index=999))
    forge("zeroBeta", "historicalM3", lambda f: f["output_atoms"][0].update(beta="0/1"))
    forge("nullLimitOnCompressed", "historicalM2", lambda f: f.update(limit=None))
    forge("nullErrorOnCompressed", "historicalM2", lambda f: f.update(error=None))
    forge("nullAtomsOnUnknown", "inputBits", lambda f: f.update(output_atoms=None))
    forge("foreignRawBinding", "historicalM2", lambda f: f.update(request_raw=f["request_raw"] + " "))
    forge("scientificGate", "historicalM2", lambda f: f.update(source_admission_verified=True))
    forge("wrongUnknownCap", "matrixOneBelow", lambda f: f["limit"].update(cap=0))
    # Input bit requirements are independent of whether M2 uses its z in mass.
    raw, high = results["exactMatrixAndAtoms"]
    low_request = read_json(raw)
    low_request["limits"]["rational_bits"] = 1
    low_raw = canonical(low_request)
    high = copy.deepcopy(high)
    high["request"], high["request_raw"] = low_request, low_raw.decode()
    (output / "m2InputBitsForgery.request.json").write_bytes(low_raw)
    (output / "m2InputBitsForgery.result.json").write_bytes(canonical(high))
    checked, data = run_binary(binary, ["check", "--request", output / "m2InputBitsForgery.request.json",
        "--certificate", output / "m2InputBitsForgery.result.json"], output, "m2InputBitsForgery.checker")
    require(checked["exit_code"] == 1 and read_json(data)["status"] == "REJECT", "M2 input bit forgery")
    controls.append({"control": "m2InputBitsForgery", "process": checked, "pass": True})
    for name in ["sameMassWrongTail", "duplicateIndex", "outsideOriginalIndex", "zeroBeta", "foreignRawBinding", "scientificGate"]:
        try:
            verify_equations((output / (name + ".request.json")).read_bytes(), read_json((output / (name + ".result.json")).read_bytes()))
        except (ValueError, IndexError):
            pass
        else:
            raise ValueError("direct Fraction verifier accepted forgery: " + name)

    # Existing actual original Lean/Rust tables are reused, not re-executed.
    population = PACKET / "design/evidence/population-lean-rust-review-1"
    saved = read_json((population / "RECEIPT.json").read_bytes())
    require(saved["pass"] is True and saved["languages_executed"] == ["rust", "lean"], "saved original execution qualification")
    watched[population / "RECEIPT.json"] = digest((population / "RECEIPT.json").read_bytes())
    transfer = []
    for m in range(2, 5):
        raw, frame = results["historicalM" + str(m)]
        request = read_json(raw)
        original = [(Fraction(a["z"]), Fraction(a["alpha"])) for a in request["atoms"]]
        selected = verify_equations(raw, frame)
        count = 0
        for case in saved["cases"]:
            name = case["fixture"]
            raw_actual = []
            for language in ("lean", "rust"):
                path = population / (name + "." + language + ".stdout")
                content = path.read_bytes()
                require(digest(content) == case["process_runs"][language]["stdout_sha256"], "saved source table identity")
                watched[path] = digest(content)
                raw_actual.append(read_json(content))
            require(sorted(canonical(row) for row in raw_actual[0]["rows"]) ==
                    sorted(canonical(row) for row in raw_actual[1]["rows"]), "saved whole literal rows differ")
            actual = raw_actual[0]
            if len(actual["context"]["start"]["live"]) > m:
                continue
            for row in actual["rows"]:
                coefficients = {rate: Fraction(value) for rate, value in row["coefficients"]}
                def quotient(z):
                    return -sum((a * geom(rate, z) for rate, a in coefficients.items()), Fraction(0))
                lhs = sum((alpha * quotient(z) for z, alpha in original), Fraction(0))
                rhs = sum((beta * quotient(z) for z, beta in selected), Fraction(0))
                require(lhs == rhs, "one shared compressed list failed an original full row")
                count += 1
        require(count == history["compression_cases"][m - 2]["original_source_row_checks"], "full-row transfer census")
        transfer.append({"M": m, "complete_original_rows_checked": count, "pass": True})
    require(sum(c["complete_original_rows_checked"] for c in transfer) == 331, "331 full-row checks")
    after = {str(path): digest(path.read_bytes()) for path in watched}
    before = {str(path): sha for path, sha in watched.items()}
    require(before == after, "reviewed sources/artifacts changed")
    receipt = {"schema": "private_rational_compression_review_v1", "pass": True,
        "date_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "binary_sha256": watched[binary],
        "cases": cases, "controls": controls, "case_count": len(cases), "control_count": len(controls),
        "deterministic_inherited_differential": differential, "full_original_row_transfers": transfer,
        "complete_original_rows_checked": 331, "inputs_before": before, "inputs_after": after,
        "lean_compiler_or_evaluator_executed": False, "accepted_native_producers_reexecuted": False,
        "private_native_producer_and_checker_executed": True, "producer_work_independently_verified": False,
        "resource_exhaustion_proved": False, "source_admission_verified": False,
        "source_factor_realization_verified": False, "arbitrary_real_extraction_verified": False,
        "rref_producer_refinement_proved": False,
        "scope": "M2..4 supplied rational common atoms; exact finite original-index certificate and saved full-row transfers only"}
    (output / "RECEIPT.json").write_bytes(canonical(receipt))
    print(json.dumps({key: receipt[key] for key in ("pass", "case_count", "control_count", "complete_original_rows_checked", "binary_sha256")}))

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.created_output = False
    try:
        run(args)
    except Exception as error:
        if args.created_output:
            (args.output / "FAILURE-RECEIPT.json").write_bytes(canonical({"pass": False, "error": str(error)}))
        raise

if __name__ == "__main__":
    main()
