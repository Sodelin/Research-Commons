#!/usr/bin/env python3
"""Strict bank transport plus independent exact request-bound result checking.

Uses the captured original checker grammar and Fraction arithmetic. The native
engine groups equal values; this verifier evaluates moments on the original
positive atoms. No physical realization or real-equality algorithm is implied.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
from codec import original_checker

MAX_BYTES = 262144
INTERNAL_BITS = 8192

def request(raw, checker):
    obj = checker.loads(raw)
    checker.fields(obj, ["schema", "copy_level_count", "atoms"])
    checker.require(obj["schema"] == "rational_finite_bank_moments_v1", "bank schema")
    level, atoms = obj["copy_level_count"], obj["atoms"]
    checker.require(type(level) is int and 1 <= level <= 8, "copy-level count 1..8")
    checker.require(type(atoms) is list and 1 <= len(atoms) <= 256, "finite carrier 1..256")
    for atom in atoms:
        checker.fields(atom, ["weight", "survival"])
        weight, value = map(checker.rational, (atom["weight"], atom["survival"]))
        checker.require(0 <= weight <= 1, "weight domain")
        checker.require(not weight or 0 < value <= 1, "positive-mass survival domain")
    return obj

def encode(obj):
    fields = ["COMMON_BANK_MOMENTS_V1", str(obj["copy_level_count"]), str(len(obj["atoms"]))]
    for atom in obj["atoms"]:
        fields.extend([atom["weight"], atom["survival"]])
    return " ".join(fields)+"\n"

def oracle(obj, checker):
    def bounded(q):
        checker.require(max(abs(q.numerator).bit_length(),q.denominator.bit_length()) <= INTERNAL_BITS,
                        "independent arithmetic verification bound exhausted")
        return q
    pairs = [(checker.rational(a["weight"]),checker.rational(a["survival"])) for a in obj["atoms"]]
    total, grouped = Fraction(0), {}
    positive = [(w,x) for w,x in pairs if w]
    for weight, value in pairs:
        total = bounded(total+weight)
        if weight:
            grouped[value] = bounded(grouped.get(value,Fraction(0))+weight)
    checker.require(total == 1, "mass must equal one without renormalization")
    nodes = sorted(grouped)
    moments = []
    # Evaluate on ORIGINAL positive atoms, independently of native regrouping.
    for k in range(1,obj["copy_level_count"]+1):
        exponent, moment = k*(k-1)//2, Fraction(0)
        for weight, value in positive:
            moment = bounded(moment+bounded(weight*value**exponent))
        moments.append(moment)
    for value in nodes:
        checker.rational(str(value))
        checker.rational(str(grouped[value]))
    for moment in moments:
        checker.rational(str(moment))
    return nodes, grouped, moments, len(positive)

def decode(raw, obj, checker, literal_request_sha256):
    checker.require(type(raw) is bytes and len(raw) <= MAX_BYTES, "complete bank stdout bound")
    nodes, weights, moments, positives = oracle(obj,checker)
    fields = ["CHECKED_RATIONAL_BANK_MOMENTS_V1",str(obj["copy_level_count"]),
              str(len(obj["atoms"])),str(positives),str(len(nodes))]
    for value in nodes:
        fields.extend([str(value),str(weights[value])])
    fields.extend(map(str,moments))
    checker.require(raw == (" ".join(fields)+"\n").encode("ascii"),
                    "native bank output does not match the exact original law")
    acquisition = None
    if len(nodes) <= 3 and obj["copy_level_count"] == 2*len(nodes)+1:
        acquisition = {"schema":"rational_support_acquisition_v1",
                       "candidate_survivals":list(map(str,nodes)),
                       "moments":list(map(str,moments))}
    # SOURCE follow-on: fixed scalar-law identity differs from literal request
    # and from its selected finite moment order. Execution awaits record binding.
    grouped_nodes = [{"survival":str(x),"weight":str(weights[x])} for x in nodes]
    scalar_law = {"schema":"rational_scalar_pushforward_law_v1","nodes":grouped_nodes}
    scalar_law_sha256 = checker.digest(scalar_law)
    moment_order = {"schema":"fixed_bank_sparse_moment_vector_v1",
                    "scalar_law_sha256":scalar_law_sha256,
                    "copy_levels":list(range(1,obj["copy_level_count"]+1)),
                    "exponents":[k*(k-1)//2 for k in range(1,obj["copy_level_count"]+1)],
                    "moments":list(map(str,moments))}
    return {"schema":"checked_rational_bank_moments_v1",
            "status":"CHECKED_RATIONAL_BANK_MOMENTS",
            "literal_request_sha256":literal_request_sha256,
            "input_atoms":len(obj["atoms"]), "positive_atoms":positives,
            "distinct_nodes":len(nodes),
            "nodes":grouped_nodes,
            "scalar_law_sha256":scalar_law_sha256,
            "scalar_law_identity_scope":"exact_rational_scalar_pushforward",
            "moment_vector_sha256":checker.digest(moment_order),
            "candidate_request_sha256":checker.digest(acquisition) if acquisition is not None else None,
            "copy_levels":list(range(1,obj["copy_level_count"]+1)),
            "exponents":[k*(k-1)//2 for k in range(1,obj["copy_level_count"]+1)],
            "moments":list(map(str,moments)),
            "candidate_request":acquisition,
            "moments_origin":"derived from this supplied exact rational law",
            "provenance":{"schema":"solver_moment_provenance_v1",
                          "kind":"supplied_mathematical_law",
                          "observation_binding":None,
                          "error_confidence_contract":None},
            "source_existence_certified":False, "native_refinement_proved":False}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["encode","decode"])
    parser.add_argument("--repository",type=Path,required=True)
    parser.add_argument("--request",type=Path)
    parser.add_argument("--emit",choices=["report","acquisition"],default="report")
    args = parser.parse_args()
    try:
        checker = original_checker(args.repository)
        raw = sys.stdin.buffer.read(MAX_BYTES+1)
        if args.mode == "encode":
            obj = request(raw,checker)
            sys.stdout.write(encode(obj))
        else:
            if args.request is None:
                raise ValueError("literal request path required")
            with args.request.open("rb") as stream:
                literal = stream.read(MAX_BYTES+1)
            obj = request(literal,checker)
            result = decode(raw,obj,checker,hashlib.sha256(literal).hexdigest())
            if args.emit == "acquisition":
                if result["candidate_request"] is None:
                    print(json.dumps({"status":"UNKNOWN","reason":"existing acquisition shape requires r<=3 and L=2r+1",
                                      "source_existence_certified":False},sort_keys=True))
                    return 2
                result = result["candidate_request"]
            print(json.dumps(result,sort_keys=True,separators=(",",":")))
    except Exception as error:
        print("REFUSED "+str(error),file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    sys.exit(main())
