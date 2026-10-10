#!/usr/bin/env python3
"""Independently authenticate saved private compression outputs; rerun no binary."""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

from review_support_join import PACKET, identity, read

ROOT = PACKET.parents[1]
DIRECTORY = PACKET / "rust/evidence/rational-compression-review-2"
GATES = ("source_admission_verified", "source_factor_realization_verified",
         "arbitrary_real_extraction_verified")


def require(value, message):
    if not value:
        raise ValueError(message)


def q(token):
    require(isinstance(token, str), "rational string")
    value = Fraction(token)
    require(token == f"{value.numerator}/{value.denominator}", "canonical rational")
    return value


def bits(value):
    return max(abs(value.numerator).bit_length(), value.denominator.bit_length())


def geom(length, z):
    return sum((z ** i for i in range(length)), Fraction(0))


def canonical(value):
    return (json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n").encode()


def equations(raw_request, frame):
    request = json.loads(raw_request)
    require(frame["schema"] == "g6_rational_compression_result_v1", "result schema")
    require(frame["request_raw"].encode() == raw_request and frame["request"] == request, "raw/semantic binding")
    require(all(frame[k] is False for k in GATES), "scientific gate")
    common = {"schema", "status", "request_raw", "request", "work", *GATES}
    require(frame["status"] == "COMPRESSED" and set(frame) == common | {"output_atoms", "mass", "tail_moments"},
            "exact compressed fields")
    m = request["M"]
    require(type(m) is int and 2 <= m <= 4, "supported cap")
    atoms = [(q(a["z"]), q(a["alpha"])) for a in request["atoms"]]
    require(all(0 < z < 1 and alpha >= 0 for z, alpha in atoms), "atom domain")
    require(len(atoms) <= request["limits"]["atoms"], "atom budget")
    bit_cap = request["limits"]["rational_bits"]
    require(max([1] + [bits(x) for atom in atoms for x in atom]) <= bit_cap, "input bit budget")
    selected, indices = [], []
    for atom in frame["output_atoms"]:
        require(set(atom) == {"input_index", "beta"}, "atom certificate fields")
        i, beta = atom["input_index"], q(atom["beta"])
        require(type(i) is int and 0 <= i < len(atoms) and beta > 0 and bits(beta) <= bit_cap,
                "positive bounded original index")
        selected.append((atoms[i][0], beta))
        indices.append(i)
    require(len(selected) <= m - 1 and indices == sorted(set(indices)), "common cardinality/order")
    mass = sum((a for _, a in atoms), Fraction(0))
    require(mass == sum((b for _, b in selected), Fraction(0)) == q(frame["mass"]), "mass")
    require(len(frame["tail_moments"]) == m - 2, "tail census")
    for level, tail in zip(range(3, m + 1), frame["tail_moments"]):
        require(set(tail) == {"level", "moment"} and tail["level"] == level, "tail level")
        exponent = level * (level - 1) // 2
        original = sum((a * geom(exponent, z) for z, a in atoms), Fraction(0))
        compressed = sum((b * geom(exponent, z) for z, b in selected), Fraction(0))
        require(original == compressed == q(tail["moment"]), "common geometric moment")
    return atoms, selected


def main():
    errors, process_count = [], 0
    freeze_path = PACKET / "rust/notes/G6-RATIONAL-COMPRESSION-SOURCE-FREEZE-3.json"
    freeze = read(freeze_path)
    first_path = PACKET / "rust/notes/G6-RATIONAL-COMPRESSION-SOURCE-FREEZE-1.json"
    first = read(first_path)
    source_checks = 0
    for rows, snapshot in ((freeze["inputs"], freeze["snapshot_directory"]),
                           (freeze["accepted_source_guards"], first["snapshot_directory"])):
      for row in rows:
        for path in (ROOT / row["path"], ROOT / snapshot / row["path"]):
            require(identity(path) == {k: row[k] for k in ("bytes", "sha256")}, "frozen source: " + str(path))
            source_checks += 1
    original_inputs = {row["path"]: row["sha256"] for row in first["inputs"]}
    require(all(row["sha256"] == original_inputs[row["path"]] for row in freeze["inputs"]
                if not row["path"].endswith("/review.py")), "unchanged compile inputs")
    for row in freeze["accepted_binary_guards"]:
        require(identity(Path(row["path"]))["sha256"] == row["sha256"], "accepted native identity")
        source_checks += 1
    for row in freeze["third_party_archives"]:
        require(identity(Path(row["path"]))["sha256"] == row["sha256"] == row["cargo_lock_checksum"], "archive identity")
        source_checks += 1
        for item in row["unpacked_files"]:
            require(identity(Path(item["path"])) == {k: item[k] for k in ("bytes", "sha256")}, "unpacked identity")
            source_checks += 1
    receipt_path = DIRECTORY / "RECEIPT.json"
    saved, final = read(receipt_path), read(DIRECTORY / "FINAL-IDENTITY.json")
    require(saved["pass"] and saved["case_count"] == 8 and saved["control_count"] == 25, "runtime census")
    require(final["review_receipt_sha256"] == identity(receipt_path)["sha256"], "review receipt binding")
    require(identity(Path(final["binary"]))["sha256"] == saved["binary_sha256"] == final["binary_sha256"], "private native identity")
    require(saved["inputs_before"] == saved["inputs_after"], "runtime before/after stability")
    for path, digest in saved["inputs_after"].items():
        require(identity(Path(path))["sha256"] == digest, "runtime input identity")
    require(all(saved[k] is False for k in (*GATES, "rref_producer_refinement_proved",
        "producer_work_independently_verified", "resource_exhaustion_proved",
        "lean_compiler_or_evaluator_executed", "accepted_native_producers_reexecuted")), "scope")
    build_dir = PACKET / "rust/evidence/rational-compression-build-1"
    build = read(build_dir / "RECEIPT.json")
    require(build["pass"] and final["build_receipt_sha256"] == identity(build_dir / "RECEIPT.json")["sha256"], "build binding")
    for name, row in zip(("build", "tests"), build["commands"]):
        require(row["process_started"] and row["exit_code"] == 0, "build/test process")
        for stream in ("stdout", "stderr"):
            require(identity(build_dir / f"{name}.{stream}")["sha256"] == row[f"{stream}_sha256"], "build/test output")
    tests = (build_dir / "tests.stdout").read_text()
    counts = re.findall(r"test result: ok\. (\d+) passed; (\d+) failed", tests)
    require(sum(int(a) for a, _ in counts) == 10 and all(b == "0" for _, b in counts), "ten focused tests")
    cases = []
    for row in saved["cases"] + saved["controls"]:
        name = row.get("fixture", row.get("control"))
        for kind in ("producer", "checker", "process"):
            if kind not in row:
                continue
            process = row[kind]
            stream_name = ("producer" if process["args"][0] == "solve" else "checker") if kind == "process" else kind
            for stream in ("stdout", "stderr"):
                require(identity(DIRECTORY / f"{name}.{stream_name}.{stream}")["sha256"]
                        == process[f"{stream}_sha256"], "saved actual process output")
            require(process["process_started"] and not process["timed_out"]
                    and process["limits"] == {"address_bytes": 768 * 1024 * 1024,
                                              "cpu_seconds": 30, "wall_seconds": 45}, "runtime bounds")
            process_count += 1
        if "producer" in row:
            raw = (DIRECTORY / f"{name}.request.json").read_bytes()
            frame = read(DIRECTORY / f"{name}.result.json")
            require(canonical(frame) == (DIRECTORY / f"{name}.producer.stdout").read_bytes(), "canonical output")
            checked = read(DIRECTORY / f"{name}.checker.stdout")
            require(checked["status"] == "ACCEPT" and row["checker"]["exit_code"] == 0
                    and checked["producer_work_verified"] is False
                    and checked["resource_exhaustion_verified"] is False, "independent checker qualification")
            if row["status"] == "COMPRESSED":
                equations(raw, frame)
                require(row["producer"]["exit_code"] == 0 and checked["certificate_valid"] is True, "successful exit")
                cases.append(name)
            else:
                require(frame["status"] == "UNKNOWN" and row["producer"]["exit_code"] == 2
                        and checked["certificate_valid"] is False, "UNKNOWN exit/framing")
                require(not any(k in frame for k in ("output_atoms", "mass", "tail_moments")), "no partial certificate")
                require(frame["request_raw"].encode() == raw and frame["request"] == json.loads(raw), "UNKNOWN binding")
                require(frame["limit"]["required"] > frame["limit"]["cap"], "resource framing")
        elif "process" in row and row["process"]["args"][0] == "solve":
            require(row["process"]["exit_code"] == 1 and read(DIRECTORY / f"{name}.producer.stdout")
                    == {"schema": "g6_rational_compression_result_v1", "status": "ERROR", "error": "INVALID_REQUEST"}, "invalid input")
        else:
            process = row.get("checker", row.get("process"))
            require(process["exit_code"] == 1 and read(DIRECTORY / f"{name}.checker.stdout")["status"] == "REJECT", "forgery refusal")
    forged = read(DIRECTORY / "sameMassWrongTail.result.json")
    request_raw = (DIRECTORY / "sameMassWrongTail.request.json").read_bytes()
    request = json.loads(request_raw)
    require(sum((q(a["alpha"]) for a in request["atoms"]), Fraction(0))
            == sum((q(a["beta"]) for a in forged["output_atoms"]), Fraction(0)), "balanced control mass")
    try:
        equations(request_raw, forged)
    except ValueError as error:
        require(str(error) == "common geometric moment", "wrong-tail independent diagnosis")
    else:
        raise ValueError("balanced wrong-tail control passed independent equations")
    require(saved["complete_original_rows_checked"] == 331
            == sum(row["complete_original_rows_checked"] for row in saved["full_original_row_transfers"]), "full-row evidence census")
    proof_path = PACKET / "quality/RATIONAL-COMPRESSION-PROOF-REVIEW.json"
    require(read(proof_path)["pass"], "separate generic formal consumer")
    result = {"schema": "private_rational_compression_saved_root_review_v1",
        "observed_utc": datetime.now(timezone.utc).isoformat(), "pass": True, "errors": errors,
        "source_identity_checks": source_checks, "runtime_input_pins": len(saved["inputs_after"]),
        "actual_saved_processes": process_count, "certificate_cases": cases,
        "focused_tests": 10, "controls": 25, "saved_full_original_row_transfers": 331,
        "independent_moment_checks": len(cases), "balanced_wrong_tail_refuted": True,
        "freeze3": identity(freeze_path), "runtime_review": identity(receipt_path),
        "generic_formal_consumer_review": identity(proof_path), "reviewer": identity(Path(__file__)),
        "source_admission_verified": False, "whole_solver_refinement_verified": False,
        "actual_finite_Lean_checker_agreement_inferred": False,
        "scope": "Frozen privateM2..4 port/build and actual saved native process outputs; independent exact mass/tail/index/positivity checks, scope/resource framing and source identities. Existing331 full-row transfer evidence is authenticated; no new solver/old native suite run, general parser/RREF theorem, positive source construction or arbitrary-real extraction. Reviewer-only failed freezes/runs remain preserved."}
    (PACKET / "quality/RATIONAL-COMPRESSION-NATIVE-REVIEW.json").write_text(json.dumps(result, sort_keys=True, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("pass", "source_identity_checks", "actual_saved_processes", "focused_tests", "controls")}))


if __name__ == "__main__":
    main()
