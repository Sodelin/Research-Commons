"""Validate anchored proof-job evidence; never run Lean, SMT, shell, or plugins."""
import argparse
import hashlib
import json
import os
import re
import stat
import sys

HEX = re.compile(r"[0-9a-f]{64}", re.ASCII)
COMMIT = re.compile(r"[0-9a-f]{40}", re.ASCII)
KEY = re.compile(r"[a-z][a-z0-9_.-]{0,79}", re.ASCII)
STAGES = ("exact", "smt", "lean")
EVIDENCE = {
    "exact": {"passed": "exact_checked", "failed": "failed"},
    "smt": {"sat": "smt_sat", "unsat": "smt_unsat", "unknown": "inconclusive", "failed": "failed"},
    "lean": {"passed": "kernel_checked", "failed": "failed"},
}
GOOD = {"exact": {"passed"}, "smt": {"sat", "unsat"}, "lean": {"passed"}}

class Bad(ValueError):
    pass

def need(condition, msg):
    if not condition:
        raise Bad(msg)

def matches(regex, value):
    return type(value) is str and regex.fullmatch(value) is not None

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def pairs(items):
    out = {}
    for k, v in items:
        need(k not in out, "duplicate JSON field")
        out[k] = v
    return out

def decode(raw):
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(Bad("nonfinite JSON")))

def fields(obj, *names):
    need(type(obj) is dict and set(obj) == set(names), "unexpected/missing fields")

def arr(obj, limit):
    need(type(obj) is list and len(obj) <= limit, "invalid list or limit")
    return obj

def load(path, limit=262144):
    # Deployment passes fixed local paths. Don't follow a final symlink or
    # block opening a replacement FIFO; check the opened file, not its name.
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    with os.fdopen(fd, "rb") as f:
        need(stat.S_ISREG(os.fstat(f.fileno()).st_mode), "not a regular input file")
        raw = f.read(limit + 1)
    need(len(raw) <= limit, "oversized input")
    return raw

def pinned(raw, expected, kind):
    need(matches(HEX, expected) and digest(raw) == expected, "untrusted " + kind)
    return decode(raw)

def binding(obj):
    need(matches(KEY, obj["job"]), "invalid job id")
    need(matches(COMMIT, obj["commit"]), "expected full source commit")
    for attr in ("source_sha256", "statement_sha256"):
        need(matches(HEX, obj[attr]), "invalid " + attr)
    return tuple(obj[attr] for attr in ("job", "commit", "source_sha256", "statement_sha256"))

def pinmap(registry):
    fields(registry, "schema", "jobs")
    need(registry["schema"] == "proofbridge.job-registry.v1", "incorrect registry schema")
    bindings = {}
    for job in arr(registry["jobs"], 512):
        fields(job, "job", "commit", "source_sha256", "statement_sha256", "stages")
        ident = binding(job)
        need(ident[0] not in bindings, "ambiguous registered job")
        stages = {}
        last = -1
        for rule in arr(job["stages"], 3):
            fields(rule, "stage", "checker_sha256", "input_sha256", "accept")
            stage = rule["stage"]
            need(type(stage) is str and stage in STAGES and STAGES.index(stage)>last,
                 "unknown/duplicate/out-of-order registered stage")
            last = STAGES.index(stage)
            for attr in ("checker_sha256", "input_sha256"):
                need(matches(HEX, rule[attr]), "invalid stage pin")
            need(type(rule["accept"]) is str and rule["accept"] in GOOD[stage],
                 "invalid registered success outcome")
            stages[stage] = rule
        need("lean" in stages, "proof job lacks a Lean stage")
        bindings[ident[0]] = (ident, stages)
    return bindings

def ledger_map(ledger, registry_sha256):
    fields(ledger, "schema", "registry_sha256", "receipts")
    need(ledger["schema"] == "proofbridge.evidence-ledger.v1" and
         ledger["registry_sha256"] == registry_sha256, "ledger not bound to registry")
    out = {}
    for r in arr(ledger["receipts"], 1024):
        fields(r, "job", "commit", "source_sha256", "statement_sha256",
               "stage", "checker_sha256", "input_sha256", "result", "output_sha256")
        binding(r)
        s = r["stage"]
        need(type(s) is str and s in STAGES and type(r["result"]) is str and r["result"] in EVIDENCE[s],
             "invalid stage evidence or result")
        for attr in ("checker_sha256", "input_sha256", "output_sha256"):
            need(matches(HEX, r[attr]), "invalid receipt " + attr)
        k = digest(json.dumps(r, sort_keys=True, separators=(",", ":")).encode())
        need(k not in out, "duplicate ledger receipt")
        out[k] = r
    return out

def evaluate(registry_raw, registry_pin, ledger_raw, ledger_pin, job_raw, source_raw):
    reg = pinmap(pinned(registry_raw, registry_pin, "registry"))
    ledger = ledger_map(pinned(ledger_raw, ledger_pin, "ledger"), registry_pin)
    job = decode(job_raw)
    fields(job, "schema", "job", "commit", "source_sha256", "statement_sha256", "receipt_refs")
    need(job["schema"] == "proofbridge.proof-job.v1", "incorrect job schema")
    ident = binding(job)
    need(ident[0] in reg and reg[ident[0]][0] == ident, "job not registered at this binding")
    need(digest(source_raw) == ident[2], "source bytes mismatch")
    stages = reg[ident[0]][1]
    used = {}
    for ref in arr(job["receipt_refs"], 3):
        need(matches(HEX, ref) and ref in ledger, "missing or untrusted receipt")
        r = ledger[ref]
        s = r["stage"]
        need(s in stages and s not in used, "unexpected/duplicate stage receipt")
        need(binding(r) == ident, "receipt job/commit/source/statement mismatch")
        for attr in ("checker_sha256", "input_sha256"):
            need(r[attr] == stages[s][attr], "receipt checker/input mismatch")
        used[s] = (ref, r)
    results = {}
    prefix = True
    for s, rule in stages.items():
        if s not in used:
            results[s] = {"disposition": "pending" if prefix else "blocked"}
            prefix = False
            continue
        need(prefix, "receipt out of stage order or after unresolved/failed check")
        ref, r = used[s]
        accepted = r["result"] == rule["accept"]
        results[s] = {"disposition": EVIDENCE[s][r["result"]], "accepted": accepted,
                      "receipt_ref": ref, "output_sha256": r["output_sha256"]}
        prefix = accepted
    return {"schema": "proofbridge.ingress-disposition.v1", "job": ident[0], "commit": ident[1],
            "source_sha256": ident[2], "statement_sha256": ident[3],
            "registry_sha256": registry_pin, "ledger_sha256": ledger_pin,
            "fresh_checker_execution": False,
            "disposition": "trusted_kernel_receipt_matched" if prefix else "not_certified",
            "stages": results}

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("registry", "registry-sha256", "ledger", "ledger-sha256", "job", "source"):
        parser.add_argument("--"+name, required=True)
    args = parser.parse_args(argv)
    try:
        result = evaluate(load(args.registry), args.registry_sha256, load(args.ledger),
                          args.ledger_sha256, load(args.job, 16384), load(args.source, 4194304))
    except (ValueError, OSError, RecursionError) as e:
        print(json.dumps({"disposition": "rejected", "reason": str(e)}))
        return 2
    print(json.dumps(result, indent=2))
    return 0

if __name__ == "__main__":
    sys.exit(main())
