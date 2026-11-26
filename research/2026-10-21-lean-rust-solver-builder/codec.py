#!/usr/bin/env python3
"""Transport-only bridge to the unchanged unified certificate checker.

UNEXECUTED proposal. No native child, build, network, source witness or
exclusion. Run only in the separately admitted online environment.
"""
import argparse
import hashlib
from pathlib import Path
import sys
import types

CERT_PATH = "research/2026-10-13-astra-unified-solver-0645z/certificates.py"
CERT_SHA256 = "ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3"
MAX_BYTES = 262144


def original_checker(repository):
    path = repository / CERT_PATH
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != CERT_SHA256:
        raise ValueError("original checker source identity changed")
    module = types.ModuleType("builder_original_certificates")
    # Execute exactly the hash-checked object; do not reopen the source.
    exec(compile(raw, str(path), "exec"), module.__dict__)
    return module


def request(raw, checker):
    obj = checker.loads(raw)
    checker.fields(obj, ["schema", "candidate_survivals", "moments"])
    checker.require(obj["schema"] == "rational_support_acquisition_v1", "request schema")
    nodes, moments = obj["candidate_survivals"], obj["moments"]
    checker.require(type(nodes) is list and 1 <= len(nodes) <= 3, "supply 1..3 candidates")
    parsed = list(map(checker.rational, nodes))
    checker.require(all(0 < a <= 1 for a in parsed) and len(set(parsed)) == len(parsed),
                    "distinct candidate survivals in (0,1] required")
    checker.require(type(moments) is list and len(moments) == 2*len(nodes)+1,
                    "exactly 2r+1 supplied moments required")
    values = list(map(checker.rational, moments))
    checker.require(values[0] == 1 and all(0 <= y <= 1 for y in values),
                    "normalized moment domain")
    return obj


def encode(obj):
    nodes, moments = obj["candidate_survivals"], obj["moments"]
    return " ".join(["COMMON_GENERATE_SUPPORT_V1", str(len(nodes)), *nodes,
                     str(len(moments)), *moments]) + "\n"


def decode(raw, obj, checker):
    checker.require(len(raw) <= MAX_BYTES+128, "native stdout cap")
    try:
        text = raw.decode("ascii")
    except UnicodeError as error:
        raise checker.Refused("ASCII native stdout required") from error
    header, separator, certificate_wire = text.partition("\n")
    cap = len(obj["moments"])-1
    checker.require(separator and header ==
                    f"GENERATED_AND_CHECKED support_cap={cap} source_existence=false",
                    "complete expected generation header required")
    parts = iter(certificate_wire.split())

    def token():
        try:
            return next(parts)
        except StopIteration as error:
            raise checker.Refused("truncated certificate wire") from error

    def natural(maximum):
        value = token()
        checker.require(value and value.isascii() and value.isdigit() and
                        (len(value) == 1 or not value.startswith("0")), "natural grammar")
        checker.require(len(value) <= 2, "natural cap")
        number = int(value)
        checker.require(number <= maximum, "natural cap")
        return number

    checker.require(token() == "COMMON_CERT_V1", "original certificate wire required")
    level = natural(8)
    checker.require(level == len(obj["moments"]), "request-bound level mismatch")
    coefficients = [token() for _ in range(level)]
    moments = [token() for _ in range(level)]
    checker.require(moments == obj["moments"], "original literal moment mismatch")
    count = natural(16)
    terms = []
    for _ in range(count):
        weight, left, right, size = token(), natural(1), natural(1), natural(15)
        terms.append(dict(weight=weight, left=left, right=right,
                          square=[token() for _ in range(size)]))
    checker.require(next(parts, None) is None, "trailing certificate token")
    certificate = dict(schema="common_sparse_certificate_v1", level=level,
                       coefficients=coefficients, moments=moments, nonnegative_terms=terms)
    checker.checked(certificate)
    # A valid independent certificate may only be transported against THIS
    # original moment vector. No producer success or stdout alone is trusted.
    return dict(schema="unified_research_solver_v1", task="check_certificate",
                input=certificate)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=["encode", "decode"])
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--request", type=Path,
                        help="decode requires the original acquisition JSON")
    args = parser.parse_args()
    checker = original_checker(args.repository.resolve())
    if args.operation == "encode":
        obj = request(sys.stdin.buffer.read(MAX_BYTES+1), checker)
        sys.stdout.write(encode(obj))
    else:
        if args.request is None:
            parser.error("decode requires --request")
        with args.request.open("rb") as file:
            obj = request(file.read(MAX_BYTES+1), checker)
        output = decode(sys.stdin.buffer.read(MAX_BYTES+129), obj, checker)
        import json
        sys.stdout.write(json.dumps(output, sort_keys=True, indent=2)+"\n")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, TypeError, OSError) as error:
        # Operational/input failure never becomes a mathematical NO.
        print("REFUSED "+str(error), file=sys.stderr)
        raise SystemExit(1)
