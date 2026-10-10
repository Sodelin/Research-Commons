#!/usr/bin/env python3
"""Authenticate saved Lean/native rational checks; execute no producer/compiler."""
import datetime
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import re
import types

COMMONS = Path(__file__).resolve().parents[4]
PACKET = COMMONS / "research/2026-10-10-codex-lean-rust-parity"
RUST = PACKET / "rust"
LEAN = PACKET / "lean"
ORIGIN = RUST / "evidence/rational-compression-review-2"
EXECUTION = LEAN / "evidence/rational-compression-compiled-fixtures/20261010T170521.316057Z"
OUT = RUST / "evidence/rational-compression-lean-rust-review-3"

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def main():
    OUT.mkdir(exist_ok=False)
    capture = OUT / "captured"
    capture.mkdir()
    watched = {}
    def preserve(path, expected=None):
        raw = path.read_bytes()
        require(expected is None or sha(raw) == expected, "identity: " + str(path))
        watched[str(path)] = sha(raw)
        try:
            relative = path.relative_to(PACKET)
        except ValueError:
            relative = Path("external") / sha(str(path).encode()) / path.name
        target = capture / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
        return raw
    own = Path(__file__).resolve()
    preserve(own)
    reference_path = RUST / "rational-compression/review.py"
    reference_raw = preserve(reference_path, "785168c6187263e86fcb829221d745c266f29dc4a8c3b0f7838be3bbe45b90f7")
    reference = types.ModuleType("pinned_private_rational_equations")
    reference.__file__ = str(reference_path)
    exec(compile(reference_raw, str(reference_path), "exec"), reference.__dict__)
    origin = json.loads(preserve(ORIGIN / "RECEIPT.json", "c57c3f512124ff8eb667a37b24a4d6b24c8e6b90326aa10f180cd0ac75905fd3"))
    require(origin["pass"] is True and origin["case_count"] == 8 and origin["control_count"] == 25, "native origin accepted")
    successful = []
    for case in origin["cases"]:
        name = case["fixture"]
        request = preserve(ORIGIN / (name + ".request.json"))
        result = preserve(ORIGIN / (name + ".result.json"), case["producer"]["stdout_sha256"])
        native = json.loads(preserve(ORIGIN / (name + ".checker.stdout"), case["checker"]["stdout_sha256"]))
        reference.verify_equations(request, json.loads(result))
        require(case["producer"]["process_started"] is True and case["checker"]["process_started"] is True
                and case["producer"]["exit_code"] == case["checker"]["exit_code"] == 0
                and native["certificate_valid"] is True, "native certificate receipt")
        successful.append(name)
    typed_capture_path = PACKET / "reuse/RATIONAL-COMPRESSION-EXAMPLES-CAPTURE-20261010T165956Z.json"
    typed = json.loads(preserve(typed_capture_path, "2b50ebe181ed716dceb26bfbd796968f30d178cd8f9efeb56505e592a9f3390e"))
    source_raw = {}
    for pin in typed["source_pins"]:
        source_raw[Path(pin["path"]).stem] = preserve(PACKET / pin["path"], pin["sha256"])
    fixture = source_raw["G6RationalCompressionCertificateFixture"].decode()
    expected_checks = {}
    translated = []
    def body(name):
        found = re.search(r"^def " + re.escape(name) + r"\b[^\n]* :=[ \t]*(.*?)(?=\n(?:def |/--|#)|\Z)", fixture, re.M | re.S)
        require(found is not None, "literal definition missing: " + name)
        return found.group(1).strip()
    def q_literals(text):
        result = []
        pattern = r"\(\((-?\d+) : ℚ\) / (\d+)\)|\((-?\d+) : ℚ\)"
        for a, b, integer in re.findall(pattern, text):
            value = Fraction(int(a), int(b)) if a else Fraction(integer)
            result.append(reference.qwire(value))
        return result
    for case in typed["cases"]:
        name = case["name"]
        request_raw = preserve(PACKET / case["request"]["path"], case["request"]["sha256"])
        result_raw = preserve(PACKET / case["result"]["path"], case["result"]["sha256"])
        request, result = json.loads(request_raw), json.loads(result_raw)
        native = json.loads(preserve(PACKET / case["native_checker"]["path"], case["native_checker"]["sha256"]))
        z = [a["z"] for a in request["atoms"]]
        alpha = [a["alpha"] for a in request["atoms"]]
        atom = [a["input_index"] for a in result["output_atoms"]]
        beta = [a["beta"] for a in result["output_atoms"]]
        require(case["M"] == request["M"] and case["n"] == len(z) and case["r"] == len(atom)
                and case["z"] == z and case["alpha"] == alpha and case["atom"] == atom and case["beta"] == beta,
                "typed capture value mismatch")
        for suffix, values in [("z", z), ("alpha", alpha), ("beta", beta)]:
            text = body(name + "_" + suffix)
            require(q_literals(text) == values and (bool(values) or text == "Fin.elim0"), "literal source values: " + name + "_" + suffix)
        literal_ids = list(map(int, re.findall(r"⟨(\d+), by decide⟩", body(name + "_atom"))))
        require(literal_ids == atom and all(0 <= i < len(z) for i in atom), "literal Fin index mismatch")
        require(re.search(r"checkCompression " + str(request["M"]) + r"\b", body(name + "_check")), "literal M mismatch")
        try:
            reference.verify_equations(request_raw, result)
            mathematical = True
        except ValueError as error:
            require(name == "sameMassWrongTail" and str(error) == "tail moment", "unexpected equation failure")
            mathematical = False
        require(mathematical is case["expected"] and mathematical is native["certificate_valid"], "native/typed/mathematical verdict disagreement")
        expected_checks[name] = mathematical
        translated.append({"case": name, "M": request["M"], "n": len(z), "r": len(atom), "expected": mathematical,
                           "literal_values_and_original_indices_match": True})
    wrong_request = read(ORIGIN / "sameMassWrongTail.request.json")
    wrong = read(ORIGIN / "sameMassWrongTail.result.json")
    zs = [Fraction(a["z"]) for a in wrong_request["atoms"]]
    alphas = [Fraction(a["alpha"]) for a in wrong_request["atoms"]]
    betas = [Fraction(a["beta"]) for a in wrong["output_atoms"]]
    ids = [a["input_index"] for a in wrong["output_atoms"]]
    expected_checks["wrongTailMass"] = sum(alphas) == sum(betas)
    expected_checks["wrongTailOtherPremises"] = (wrong_request["M"] >= 2 and all(0 < z < 1 for z in zs)
        and all(a >= 0 for a in alphas) and len(betas) <= wrong_request["M"] - 1 and all(b > 0 for b in betas))
    expected_checks["wrongTailMomentDiffers"] = sum(a * reference.geom(3, z) for a, z in zip(alphas, zs)) != sum(b * reference.geom(3, zs[i]) for b, i in zip(betas, ids))
    require(all(expected_checks[k] for k in ["wrongTailMass", "wrongTailOtherPremises", "wrongTailMomentDiffers"]), "balanced negative control classification")
    execution = json.loads(preserve(EXECUTION / "RECEIPT.json", "116e228788b15793fe873ab2dbd58d8d61e6192621144983c9a746ae8c673920"))
    config = json.loads(preserve(EXECUTION / "LEAN-EXECUTION-CONFIG.json", execution["execution_config_sha256"]))
    process = json.loads(preserve(EXECUTION / "LEAN-PROCESS-RESULT.json"))
    stdout = preserve(EXECUTION / "lean.stdout", process["stdout_sha256"])
    stderr = preserve(EXECUTION / "lean.stderr", process["stderr_sha256"])
    require(process["exit_code"] == 0 and not stderr and process["command"] == config["command_prefix"], "actual evaluator command/result")
    actual = {}
    for line in stdout.decode().splitlines():
        match = re.fullmatch(r"([A-Za-z0-9]+): (true|false) \(expected (true|false)\)", line)
        require(match is not None and match[1] not in actual, "Lean output line")
        actual[match[1]] = match[2] == "true"
        require(actual[match[1]] == (match[3] == "true"), "Lean expected marker disagreement")
    require(actual == expected_checks and execution["checks"] == len(actual) == 9
            and execution["certificate_cases"] == 6 and execution["extra_wrong_tail_controls"] == 3,
            "full actual Lean Boolean comparison")
    require(execution["lean_evaluator_processes"] == 1 and execution["native_producer_processes"] == 0
            and execution["execution_mode"] == "compiled_lean_evaluator_not_standalone_elf"
            and execution["universal_native_parser_or_elimination_refinement_claimed"] is False, "execution qualification")
    binary = Path("/workspace/scratch/lean-rust-parity-native/runtime/rational-compression-candidate-1/rational-compression-probe")
    require(sha(binary.read_bytes()) == execution["private_native_binary_sha256"] == origin["binary_sha256"], "private runtime identity")
    watched[str(binary)] = sha(binary.read_bytes())
    preserve(Path(config["compiler_path"]), config["compiler_sha256"])
    preserve(Path(config["driver_path"]), config["driver_sha256"])
    summary_path = LEAN / "RATIONAL-COMPRESSION-FIXTURE-EVALUATOR-RESULT.json"
    summary = json.loads(preserve(summary_path))
    certificate_path = LEAN / "RATIONAL-COMPRESSION-FIXTURE-CERTIFICATE.json"
    certificate = json.loads(preserve(certificate_path, summary["kernel_certificate_sha256"]))
    require(certificate["kernel_checking"] is True and certificate["compiler_and_native_final_stable"] is True, "kernel certificate qualification")
    audited = []
    for name, target in certificate["targets"].items():
        archive = LEAN / certificate["evidence"] / target["audit_distribution"]
        raw = gzip.decompress(preserve(archive))
        require(sha(raw) == target["audit_raw_sha256"], "owned audit decompressed identity")
        audit = json.loads(raw)
        require(not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"], "owned audit failure")
        require(len(audit["selected_modules"]) == target["closure_modules"]
                and len(audit["declarations"]) == audit["declaration_count"] == target["owned_declarations"]
                and audit["theorem_declaration_count"] == target["owned_theorems"], "owned audit counts")
        audited.append({"target": name, "modules": target["closure_modules"], "declarations": target["owned_declarations"],
                        "theorems": target["owned_theorems"], "owned_axioms": 0, "nonstandard_axioms": 0, "missing_modules": 0})
    prepins = json.loads(preserve(EXECUTION / "PRE-EVALUATION-PINS.json"))
    owned_artifacts = 0
    for path, expected in prepins.items():
        if path.startswith(config["workdir"] + "/") or path in [config["compiler_path"], config["driver_path"]]:
            require(sha(Path(path).read_bytes()) == expected, "checked owned/driver import artifact changed")
            watched[path] = expected
            owned_artifacts += 1
    for row in json.loads(preserve(EXECUTION / "PRESERVATION-MANIFEST.json"))["files"]:
        path = EXECUTION / row["path"]
        preserve(path, row["sha256"])
    after = {path: sha(Path(path).read_bytes()) for path in watched}
    require(watched == after, "saved bindings changed during review")
    receipt = {"schema": "private_rational_compression_saved_lean_rust_review_v1", "pass": True,
        "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "native_successful_cases_rechecked": successful,
        "native_certificates_rechecked": len(successful), "typed_translations": translated,
        "actual_lean_checks": actual, "actual_lean_check_count": 9, "typed_certificate_cases": 6,
        "wrong_tail_controls": 3, "audits": audited, "audited_counts_overlap_not_additive": True,
        "owned_import_artifacts_rehashed": owned_artifacts, "external_import_audit_repeated": False,
        "inputs_before": watched, "inputs_after": after, "new_native_processes": 0, "new_lean_processes": 0,
        "execution_mode": execution["execution_mode"], "mathematical_rational_certificates_checked": True,
        "native_json_or_producer_refinement_proved": False, "resource_exhaustion_verified": False,
        "source_admission_verified": False, "source_factor_realization_verified": False, "arbitrary_real_extraction_verified": False}
    (OUT / "RECEIPT.json").write_text(json.dumps(receipt, sort_keys=True, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ("pass", "native_certificates_rechecked", "typed_certificate_cases", "actual_lean_check_count", "owned_import_artifacts_rehashed")}))

if __name__ == "__main__":
    main()
