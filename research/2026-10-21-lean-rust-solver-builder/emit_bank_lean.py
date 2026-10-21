#!/usr/bin/env python3
"""SOURCE-ONLY pure literal-bank Lean emitter; no compiler, file output or origin grant.

The supplied mathematical bank and old certificate are independently checked
before template substitution. Every actual emitted proof still needs an actual
Lean check in its explicitly selected source/import context.
"""
import hashlib
from pathlib import Path
import bank_codec

TEMPLATE_SHA256 = "dc5c4f7bfdb23d53889ae896b67ffe3630586655036fec8cfea57b7c80ea4361"
MAX_SOURCE_BYTES = 262144
RECEIVER_SHA256 = "879518802d5bbe0ce1e2cf6392a0a6cbe8b70fc9fedb421035ad129684f0530e"

def rational_literal(token):
    parts = token.split("/")
    numerator = f"({parts[0]} : ℚ)"
    return numerator if len(parts) == 1 else f"({numerator} / ({parts[1]} : ℚ))"

def balanced_sum(terms):
    if len(terms) == 1:
        return terms[0]
    middle = len(terms)//2
    return "("+balanced_sum(terms[:middle])+" + "+balanced_sum(terms[middle:])+")"

def render(bank_literal, bank_native_stdout, receiver_literal, *, checker):
    """Accept original RAM byte buffers and an actual original-checker binding.

    Returns source plus a SOURCE artifact descriptor, never a compiled result.
    Caller must mediate any first persistence through the existing record/source
    policy; this function creates no output directory and starts no process.
    """
    checker.require(type(bank_literal) is bytes and type(receiver_literal) is bytes,
                    "literal bank and receiver bytes required")
    bank_obj = bank_codec.request(bank_literal,checker)
    report = bank_codec.decode(bank_native_stdout,bank_obj,checker,
                               hashlib.sha256(bank_literal).hexdigest())
    checker.require(report["candidate_request"] is not None,"supported r<=3/L=2r+1 bank required")
    receiver = checker.loads(receiver_literal)
    checker.fields(receiver,["schema","task","input"])
    checker.require(receiver["schema"] == "unified_research_solver_v1" and
                    receiver["task"] == "check_certificate","original certificate request required")
    checked = checker.checked(receiver["input"])
    checker.require(receiver["input"]["level"] == bank_obj["copy_level_count"] and
                    receiver["input"]["moments"] == report["moments"],
                    "certificate must use this exact bank/L/moment vector")
    template_raw = Path(__file__).with_name("bank_lean.template").read_bytes()
    checker.require(hashlib.sha256(template_raw).hexdigest() == TEMPLATE_SHA256,
                    "literal Lean template source changed")
    identity = checker.digest({"bank_request_sha256":report["literal_request_sha256"],
                               "certificate_sha256":checked["certificate_sha256"]})
    namespace = "Astra.Generated.BankWitness_"+identity
    certificate_namespace = "Astra.Generated.Certificate_"+checked["certificate_sha256"]
    nodes = report["nodes"]
    weight = "(0 : ℚ)"
    for node in reversed(nodes):
        weight = ("if q = "+rational_literal(node["survival"])+" then "+
                  rational_literal(node["weight"])+" else "+weight)
    terms = [rational_literal(atom["weight"])+" * "+rational_literal(atom["survival"])+"^n"
             for atom in bank_obj["atoms"]]
    sparse = []
    for k, value in enumerate(report["moments"],start=1):
        sparse.append(
            f"theorem sparse_moment_{k} : moment law (({k} : ℕ).choose 2) = "
            f"({rational_literal(value)} : ℝ) := by\n"
            "  rw [law_moment_raw]\n"
            "  norm_num [rawMoment, Nat.choose]\n")
    substitutions = {
        "CERTIFICATE_MODULE":certificate_namespace,
        "CERTIFICATE_NAMESPACE":certificate_namespace,
        "NAMESPACE":namespace,
        "NODES":"{"+", ".join(rational_literal(node["survival"]) for node in nodes)+"}",
        "WEIGHT":weight,
        "RAW_SUM":balanced_sum(terms),
        "CASES":" | ".join("rfl" for _ in nodes),
        "SPARSE_MOMENTS":"\n".join(sparse),
    }
    source = template_raw.decode("utf-8")
    for name, value in substitutions.items():
        source = source.replace("@@"+name+"@@",value)
    checker.require("@@" not in source,"unresolved Lean source placeholder")
    encoded = source.encode("utf-8")
    if len(encoded) > MAX_SOURCE_BYTES:
        return {"status":"UNKNOWN","reason":"literal bank Lean source cap exhausted",
                "compiled":False,"source_existence_certified":False}
    audits = ["grouped_moment_raw","law_moment_raw","law_nodes_Ioc","bank_nodes_root"]
    audits.extend(f"sparse_moment_{k}" for k in range(1,len(report["moments"])+1))
    return {"status":"EMITTED_LEAN_SOURCE","source":source,
            "source_sha256":hashlib.sha256(encoded).hexdigest(),"source_bytes":len(encoded),
            "module":namespace,"source_path":namespace.replace(".","/")+".lean",
            "selected_audits":[namespace+"."+name for name in audits],
            "literal_bank_request_sha256":report["literal_request_sha256"],
            "certificate_sha256":checked["certificate_sha256"],
            "required_receiver_source_sha256":RECEIVER_SHA256,
            "template_sha256":TEMPLATE_SHA256,
            "original_bank_rows":len(bank_obj["atoms"]),
            "distinct_positive_nodes":len(nodes),"level":bank_obj["copy_level_count"],
            "provenance_kind":"supplied_mathematical_law",
            "compiled":False,"native_refinement_proved":False,
            "physical_source_existence_certified":False}
