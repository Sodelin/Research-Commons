"""Read-only health check for the Git-backed v2 Discovery index; never runs indexed code."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = "docs/discovery/generated-source-index/"
ROOTS = ("research", "packages/research", "lean", "docs/discovery/lean-bank",
         ".github/workflows/discovery-source-index.yml")
REF = re.compile(r"[A-Za-z0-9][A-Za-z0-9_./~-]{0,127}\Z")
OID = re.compile(r"[a-f0-9]{40}(?:[a-f0-9]{24})?\Z")
DIGEST = re.compile(r"[a-f0-9]{64}\Z")

def need(cond, message):
    if not cond:
        raise ValueError(message)

def git(repo, *args):
    r = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, timeout=15)
    need(r.returncode == 0, "git failed: " + r.stderr.decode("utf-8", "replace")[:200])
    return r.stdout

def exact_commit(repo, ref):
    need(bool(REF.fullmatch(ref)), "invalid ref")
    oid = git(repo, "rev-parse", "--verify", "--end-of-options", ref+"^{commit}").decode().strip()
    need(bool(OID.fullmatch(oid)), "malformed Git commit")
    return oid

def blob_oid(repo, head, path):
    need(type(path) is str and len(path) <= 4096 and "\x00" not in path
         and not path.startswith("/") and all(x not in ("", ".", "..") for x in path.split("/")),
         "invalid indexed path")
    oid = git(repo, "rev-parse", "--verify", "--end-of-options", head+":"+path).decode().strip()
    need(bool(OID.fullmatch(oid)), "malformed Git blob")
    return oid

def blob(repo, head, path, limit):
    oid = blob_oid(repo, head, path)
    need(int(git(repo, "cat-file", "-s", oid)) <= limit, "oversized " + path)
    return git(repo, "cat-file", "blob", oid)

def unique_pairs(pairs):
    d = {}
    for k, v in pairs:
        need(k not in d, "duplicate JSON key: " + k)
        d[k] = v
    return d

def json_read(data):
    d = json.loads(data, object_pairs_hook=unique_pairs)
    need(type(d) is dict, "expected JSON object")
    return d

def sha(b):
    return hashlib.sha256(b).hexdigest()

def status(repo, ref, verify_shards=False):
    head = exact_commit(repo, ref)
    def read(name):
        return json_read(blob(repo, head, BASE+name, 131072))
    m, c, q = [read(x) for x in ("receipt.json", "checks.json", "query-smoke.json")]
    need(m["schema"] == "commons.discovery.git-source-index.v2" and m["evidence"] == "indexed_only",
         "not an index-only v2 receipt")
    src, digest = m["source_commit"], m["sha256"]
    need(bool(OID.fullmatch(src)) and bool(DIGEST.fullmatch(digest)), "invalid manifest pin")
    need(c["schema"] == "commons.discovery.check-battery.v1" and q["schema"] == "commons.discovery.query-smoke.v1",
         "unexpected companion schema")
    for side in (c,q):
        need(side["source_commit"] == src and side["index_sha256"] == digest, "mixed source/index receipt pins")
    need(type(m["shards"]) is list and len(m["shards"]) == 256, "expected 256 shards")
    need(type(m["rows"]) is int and m["rows"] >= 0, "invalid manifest row count")
    for i, s in enumerate(m["shards"]):
        need(s["path"] == f"shards/{i:02x}.jsonl" and type(s["rows"]) is int and 0 <= s["rows"] <= m["rows"]
             and bool(DIGEST.fullmatch(s["sha256"])), "invalid shard descriptor")
    need(sum(s["rows"] for s in m["shards"]) == m["rows"], "manifest row total mismatch")
    need(type(q["checks"]) is list and 0 < len(q["checks"]) <= 32, "invalid query-smoke count")
    need(type(c["checks"]) is dict and 0 < len(c["checks"]) <= 32, "invalid check battery")
    need(c["checks"]["source_index"]["status"] == "passed", "source-index battery did not pass")
    sample = {}
    for item in q["checks"]:
        path = item["path"]
        need(blob_oid(repo, src, path) == item["git_blob"], "query pin differs from source tree")
        need(type(item["decl_hint"]) is str and 0 < len(item["decl_hint"]) <= 256, "invalid declaration hint")
        s = m["shards"][int(sha(path.encode())[:2], 16)]
        if s["path"] not in sample:
            sample[s["path"]] = blob(repo, head, BASE+s["path"], 1_000_000)
        body = sample[s["path"]]
        need(sha(body) == s["sha256"], "smoke shard body mismatch")
        hits = [row for raw in body.splitlines() if (row := json_read(raw)).get("path") == path]
        need(len(hits) == 1 and hits[0].get("git_blob") == item["git_blob"]
             and item["decl_hint"] in hits[0].get("declaration_hints", [])
             and hits[0].get("evidence") == "indexed_only", "missing or mismatched query row")
    git(repo, "merge-base", "--is-ancestor", src, head)
    changed = bool(git(repo, "diff", "--name-only", "-z", src, head, "--", *ROOTS))
    shard_count = 0
    if verify_shards:
        combined = hashlib.sha256()
        for s in m["shards"]:
            body = blob(repo, head, BASE+s["path"], 1_000_000)
            need(sha(body) == s["sha256"] and body.count(b"\n") == s["rows"]
                 and (not body or body.endswith(b"\n")), "shard body mismatch: " + s["path"])
            combined.update(body)
            shard_count += 1
        need(combined.hexdigest() == digest, "aggregate index mismatch")
    return {"schema": "commons.discovery.index-health.v1",
            "status": "stale" if changed else "current_for_index_scope",
            "head": head, "source_commit": src, "index_sha256": digest,
            "rows": m["rows"], "smoke_blob_pins_checked": len(q["checks"]),
            "shard_bodies_checked": shard_count if verify_shards else len(sample),
            "full_shard_verification": verify_shards, "evidence": "indexed_only",
            "check_status_counts": {k: v["status"] for k, v in c["checks"].items()}}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo",type=Path,default=Path.cwd())
    p.add_argument("--head",default="HEAD")
    p.add_argument("--verify-shards",action="store_true")
    a = p.parse_args()
    try:
        data = status(a.repo, a.head, a.verify_shards)
        print(json.dumps(data, sort_keys=True))
        return 0 if data["status"] == "current_for_index_scope" else 1
    except (OSError, ValueError, KeyError, TypeError, AttributeError, subprocess.SubprocessError) as e:
        print(json.dumps({"status":"invalid_or_unavailable","diagnostic":str(e)[:240]}, sort_keys=True))
        return 2

if __name__ == "__main__":
    raise SystemExit(main())
