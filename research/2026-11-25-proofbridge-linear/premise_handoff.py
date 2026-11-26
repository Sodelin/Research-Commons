"""Producer/consumer handoff for zero-weight assumption deletion."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

import assumption_relay
import linear

SCHEMA = "commons.proofbridge.premise_handoff.v1"
CHECKER = "8872348bfde6b6961e985e8bcfac1db320239e973b84cb79d3b36ec065ae7ee5"


def identity(c, row):
    pairs = sorted(zip(c["variables"], row["coeffs"]))
    body = {"domain": "commons.linear-int.inequality.v1", "terms": pairs, "le": row["le"]}
    return "int-ineq:" + linear.sha(assumption_relay.canonical(body))


def shape(source, expected_hash, theorem_id):
    linear.require(re.fullmatch(r"[A-Za-z][A-Za-z0-9_:.\-]{0,127}", theorem_id), "invalid theorem ID")
    linear.require(linear.sha(source) == expected_hash, "source certificate hash mismatch")
    linear.require(linear.sha(Path(linear.__file__).read_bytes()) == CHECKER, "unexpected checker bytes")
    c = linear.parse(source)
    ids = [identity(c, row) for row in c["premises"]]
    linear.require(len(ids) == len(set(ids)), "duplicate premise identities")
    keep = [i for i, m in enumerate(c["multipliers"]) if m]
    reduced = {**c, **{k: [c[k][i] for i in keep] for k in ("premises", "multipliers")}}
    retained = [ids[i] for i in keep]
    dropped = [p for p, m in zip(ids, c["multipliers"]) if not m]
    return {
        "schema": SCHEMA,
        "theorem_id": theorem_id,
        "source_certificate_sha256": expected_hash,
        "target_id": identity(c, c["target"]),
        "original_premise_ids": ids,
        "retained_premise_ids": retained,
        "dropped_premise_ids": dropped,
        "reduced_certificate": reduced,
        "status": "checked_under_fewer_premises" if dropped else "no_zero_weight_premise"
    }


def produce(raw, source_hash, theorem_id):
    record = shape(raw, source_hash, theorem_id)
    record["original_replay"] = linear.checked(raw)
    if record["dropped_premise_ids"]:
        record["reduced_replay"] = linear.checked(
            assumption_relay.canonical(record["reduced_certificate"]))
    return record


def consume(raw, source_hash, theorem_id, record):
    expected = shape(raw, source_hash, theorem_id)
    linear.require(type(record) is dict, "invalid handoff")
    keys = set(expected) | {"original_replay"}
    if expected["dropped_premise_ids"]:
        keys.add("reduced_replay")
    linear.require(set(record) == keys, "unexpected handoff keys")
    linear.require(assumption_relay.canonical({k: record[k] for k in expected}) ==
                   assumption_relay.canonical(expected), "handoff statement or premise IDs mismatch")
    # Only the local replay, not the supplied producer receipts, grants verified status.
    reduced = assumption_relay.canonical(expected["reduced_certificate"])
    replay = linear.checked(reduced)
    return {"schema": "commons.proofbridge.premise_acceptance.v1",
            "theorem_id": theorem_id, "source_certificate_sha256": source_hash,
            "target_id": expected["target_id"], "premise_ids": expected["retained_premise_ids"],
            "dropped_premise_ids": expected["dropped_premise_ids"],
            "replay": replay}


def read(path, cap):
    with path.open("rb") as f:
        data = f.read(cap + 1)
    linear.require(len(data) <= cap, "input exceeds size limit")
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=Path, help="trusted pinned direct Lean executable")
    parser.add_argument("op", choices=["produce", "consume"])
    parser.add_argument("theorem_id")
    parser.add_argument("source_sha256")
    parser.add_argument("source", type=Path)
    parser.add_argument("handoff", type=Path, nargs="?")
    args = parser.parse_args()
    if args.lean is not None:
        linear.LEAN[:] = [str(args.lean.resolve(strict=True))]
    raw = read(args.source, 16384)
    if args.op == "produce":
        linear.require(args.handoff is None, "unexpected handoff path")
        result = produce(raw, args.source_sha256, args.theorem_id)
    else:
        linear.require(args.handoff is not None, "missing handoff path")
        result = consume(raw, args.source_sha256, args.theorem_id,
                         json.loads(read(args.handoff, 65536), object_pairs_hook=linear.object_pairs))
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        sys.exit(str(exc))
