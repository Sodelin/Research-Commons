#!/usr/bin/env python3
"""Reconcile Discovery v2 shards against an immutable Git tree; inventory, never proof."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import sys

ROOTS = ("research", "packages/research", "lean", "docs/discovery/lean-bank")
SCHEMA = "commons.discovery.git-source-index.v2"
REPORT = "commons.discovery.coverage-reconciliation.v1"
OID = re.compile(r"(?:[a-f0-9]{40}|[a-f0-9]{64})\Z")
DIGEST = re.compile(r"[a-f0-9]{64}\Z")
MODES = {b"100644", b"100755"}
SHARDS = tuple(f"shards/{n:02x}.jsonl" for n in range(256))
ERROR_LIMIT = 20


class Failure(ValueError):
    def __init__(self, code, **info):
        self.code = code
        self.info = info
        super().__init__(code)


def ensure(cond, code, **info):
    if not cond:
        raise Failure(code, **info)


def is_match(pattern, value):
    return type(value) is str and pattern.fullmatch(value) is not None


def sha(payload):
    return sha256(payload).hexdigest()


def git(root, *args):
    p = subprocess.run(["git", "--no-replace-objects", "-C", str(root), *args],
                       stdin=subprocess.DEVNULL, capture_output=True, timeout=60)
    ensure(p.returncode == 0, "git_command_failed", command=args[0], exit_code=p.returncode,
           detail=p.stderr.decode("utf-8", "backslashreplace").strip()[:1000])
    return p.stdout


def kind_for(path):
    # Independently encode the maintained v2 inventory policy. No indexer import.
    if path.endswith(".lean"):
        return "lean_source"
    if path.endswith((".md", ".mdx")) and not path.startswith("docs/discovery/lean-bank/tools/"):
        return "research_note"
    if path.endswith((".receipt.json", "-receipt.json", "/receipt.json", "/SHA256SUMS")):
        return "receipt_locator"
    return None


def read_tree(root, commit):
    ensure(is_match(OID, commit), "invalid_requested_commit", commit=commit)
    actual = git(root, "rev-parse", "--verify", commit + "^{commit}").decode("ascii").strip()
    ensure(actual == commit, "git_commit_mismatch", expected=commit, actual=actual)
    payload = git(root, "ls-tree", "-r", "-z", "--full-tree", commit, "--", *ROOTS)
    ensure(not payload or payload.endswith(b"\0"), "malformed_git_tree_boundary")
    expected, excluded, seen = {}, Counter(), set()
    for record in payload.split(b"\0")[:-1]:
        head, separator, raw_path = record.partition(b"\t")
        parts = head.split()
        ensure(separator and raw_path and len(parts) == 3, "malformed_git_tree_record")
        mode, obj_kind, blob = parts
        try:
            path = raw_path.decode("utf-8")
        except UnicodeDecodeError:
            # Producer's UTF-8 replacement cannot identify the original path.
            ensure(False, "non_utf8_git_path", git_path_hex=raw_path.hex())
        ensure(path not in seen, "duplicate_git_path", path=path)
        seen.add(path)
        if mode == b"120000":
            excluded["symlink"] += 1
        elif mode == b"160000":
            excluded["gitlink"] += 1
        elif obj_kind != b"blob" or mode not in MODES:
            excluded["nonregular_git_entry"] += 1
        elif path.startswith("docs/discovery/lean-bank/tools/") and path.endswith((".md",".mdx")):
            excluded["tooling_documentation"] += 1
        elif (category := kind_for(path)) is None:
            excluded["unsupported_extension_or_basename"] += 1
        else:
            ensure(len(blob) == len(commit) and is_match(OID, blob.decode("ascii")),
                   "invalid_git_blob", path=path)
            expected[path] = (category, blob.decode("ascii"))
    return expected, dict(sorted(excluded.items())), len(seen)


def unique_object(items):
    out = {}
    for key, value in items:
        ensure(key not in out, "duplicate_json_key", key=key)
        out[key] = value
    return out


def parse(payload, location):
    try:
        def invalid(c):
            raise Failure("non_json_constant", constant=c)
        return json.loads(payload.decode("utf-8"), object_pairs_hook=unique_object, parse_constant=invalid)
    except (ValueError, RecursionError) as e:
        if isinstance(e, Failure):
            raise Failure(e.code, location=location, **e.info) from e
        raise Failure("malformed_json", location=location, detail=str(e)[:200]) from e


def require_fields(value, keys, location):
    ensure(type(value) is dict and set(value) == set(keys.split()),
           "invalid_json_fields", location=location, expected=keys)


def read_file(path):
    ensure(path.is_file() and not path.is_symlink(), "missing_or_nonregular_index_file", path=str(path))
    return path.read_bytes()


def read_index(index, commit):
    manifest = parse(read_file(index/"receipt.json"), "receipt.json")
    fields = "schema source_commit rows sha256 evidence shards"
    if type(manifest) is dict and ("hint_version" in manifest or "scan" in manifest):
        fields += " hint_version scan"
    require_fields(manifest, fields, "receipt.json")
    if "hint_version" in manifest:
        ensure(manifest["hint_version"] == "line-hints.v1", "unsupported_hint_version")
        scan = manifest["scan"]
        require_fields(scan, "prior_index reused_rows source_bodies_read", "receipt.json:scan")
        ensure(type(scan["prior_index"]) is str and
               all(type(scan[x]) is int and scan[x] >= 0 for x in ("reused_rows","source_bodies_read")) and
               type(manifest["rows"]) is int and
               scan["reused_rows"] + scan["source_bodies_read"] == manifest["rows"],
               "invalid_incremental_scan_counts")
    ensure(manifest["schema"] == SCHEMA and manifest["evidence"] == "indexed_only",
           "wrong_manifest_scope")
    ensure(manifest["source_commit"] == commit, "manifest_commit_mismatch",
           expected=commit, actual=manifest["source_commit"])
    ensure(type(manifest["rows"]) is int and manifest["rows"] >= 0 and
           is_match(DIGEST, manifest["sha256"]), "invalid_manifest_counts_or_digest")
    ensure(type(manifest["shards"]) is list and len(manifest["shards"]) == len(SHARDS),
           "invalid_shard_count", expected=len(SHARDS))
    shard_dir = index/"shards"
    ensure(shard_dir.is_dir() and not shard_dir.is_symlink(), "missing_or_nonregular_shard_directory")
    actual_files = {p.name for p in shard_dir.iterdir()}
    expected_files = {Path(p).name for p in SHARDS}
    ensure(actual_files == expected_files, "unexpected_shard_directory_contents",
           missing=sorted(expected_files-actual_files), extra=sorted(actual_files-expected_files))
    indexed = {}
    aggregate = sha256()
    for path, entry in zip(SHARDS, manifest["shards"]):
        require_fields(entry, "path rows sha256", path)
        ensure(entry["path"] == path, "noncanonical_shard_order", expected=path, actual=entry["path"])
        ensure(type(entry["rows"]) is int and entry["rows"] >= 0 and is_match(DIGEST, entry["sha256"]),
               "invalid_shard_counts_or_digest", shard=path)
        payload = read_file(index/path)
        aggregate.update(payload)
        ensure(sha(payload) == entry["sha256"], "shard_digest_mismatch", shard=path,
               expected=entry["sha256"], actual=sha(payload))
        ensure(not payload or payload.endswith(b"\n"), "noncanonical_jsonl_boundary", shard=path)
        lines = payload.split(b"\n")[:-1]
        ensure(len(lines) == entry["rows"], "shard_row_count_mismatch", shard=path,
               expected=entry["rows"], actual=len(lines))
        for line_no,line in enumerate(lines,1):
            location=f"{path}:{line_no}"
            row=parse(line, location)
            require_fields(row, "path git_blob kind title declaration_hints evidence", location)
            key=row["path"]
            ensure(type(key) is str and key and "\0" not in key and not re.search(r"[\ud800-\udfff]",key),
                   "invalid_index_path", location=location)
            ensure(key not in indexed, "duplicate_index_path", path=key, location=location)
            ensure(path == f"shards/{sha(key.encode())[:2]}.jsonl",
                   "wrong_path_shard", path=key, location=location)
            ensure(row["evidence"] == "indexed_only", "index_row_overstates_evidence",
                   path=key, location=location)
            ensure(type(row["kind"]) is str and is_match(OID,row["git_blob"]) and
                   len(row["git_blob"]) == len(commit), "invalid_index_metadata", location=location)
            ensure(type(row["title"]) is str and type(row["declaration_hints"]) is list and
                   len(row["declaration_hints"]) <= 256 and
                   all(type(x) is str for x in row["declaration_hints"]),
                   "invalid_search_hints", location=location)
            indexed[key]=(row["kind"],row["git_blob"])
    ensure(aggregate.hexdigest() == manifest["sha256"], "aggregate_digest_mismatch",
           expected=manifest["sha256"], actual=aggregate.hexdigest())
    ensure(len(indexed) == manifest["rows"], "manifest_row_count_mismatch",
           expected=manifest["rows"], actual=len(indexed))
    return indexed, manifest["sha256"]


def reconcile(root, index, commit):
    expected, excluded, visited = read_tree(root, commit)
    indexed, digest = read_index(index, commit)
    missing=sorted(expected.keys()-indexed.keys())
    unexpected=sorted(indexed.keys()-expected.keys())
    changed=[{"path":p, "expected_kind":expected[p][0], "expected_blob":expected[p][1],
              "indexed_kind":indexed[p][0], "indexed_blob":indexed[p][1]}
             for p in sorted(expected.keys() & indexed.keys()) if expected[p] != indexed[p]]
    ensure(not (missing or unexpected or changed), "git_index_coverage_mismatch",
           missing_count=len(missing), unexpected_count=len(unexpected), changed_count=len(changed),
           missing=missing[:ERROR_LIMIT], unexpected=unexpected[:ERROR_LIMIT], changed=changed[:ERROR_LIMIT])
    return {"schema":REPORT,"status":"passed","evidence":"inventory_only","source_commit":commit,
            "index_sha256":digest,"roots":list(ROOTS),"tree_entries_in_roots":visited,
            "indexed_rows":len(indexed),"by_kind":dict(sorted(Counter(k for k,_ in indexed.values()).items())),
            "excluded_in_roots":excluded,"out_of_scope":"all paths outside these roots were not enumerated"}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,default=Path.cwd())
    p.add_argument("--index",type=Path,required=True)
    p.add_argument("--commit",required=True)
    p.add_argument("--report",type=Path)
    a=p.parse_args()
    try:
        result=reconcile(a.root,a.index,a.commit)
    except (Failure,OSError,subprocess.TimeoutExpired,UnicodeError) as e:
        metadata=e.info if isinstance(e,Failure) else {"detail":str(e)}
        result={"schema":REPORT,"status":"failed","evidence":"inventory_only",
                "source_commit":a.commit,"error":{"code":e.code if isinstance(e,Failure) else type(e).__name__,
                                                 **metadata}}
    content=json.dumps(result,sort_keys=True,ensure_ascii=True)+"\n"
    if a.report is not None:
        a.report.write_text(content,encoding="utf-8")
    print(content,end="")
    return 0 if result["status"]=="passed" else 2


if __name__=="__main__":
    raise SystemExit(main())
