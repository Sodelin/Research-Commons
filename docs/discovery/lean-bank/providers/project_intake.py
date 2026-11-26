"""Verify an approved, bounded GitHub metadata capture and project source-only rows."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from urllib.parse import quote

MAX_BYTES = 2_000_000
MAX_PROVIDERS = 32
MAX_FILES = 256
MAX_TREES = 128
MAX_ENTRIES = 16_384
MAX_DEPTH = 24
H40 = re.compile(r"[0-9a-f]{40}")
REPO = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
PROVIDER = re.compile(r"[a-z][a-z0-9_]{0,63}")
VALID_MODES = {"040000": "tree", "100644": "blob", "100755": "blob",
               "120000": "blob", "160000": "commit"}
REGULAR = {"100644", "100755"}

def require(test, text):
    if not test:
        raise ValueError(text)

def exact(obj, fields):
    require(type(obj) is dict and set(obj) == set(fields.split()), "unexpected JSON fields")

def sha(value):
    require(type(value) is str and H40.fullmatch(value), "full lowercase Git SHA-1 required")
    return value

def segment(value):
    require(type(value) is str and 0 < len(value) <= 255
            and value not in (".", "..")
            and not any(c in value for c in "/\\")
            and all(ord(c) >= 32 and ord(c) != 127 for c in value),
            "noncanonical Git path segment")
    return value

def path_parts(value):
    require(type(value) is str and 0 < len(value) <= 1024, "invalid file path")
    parts = [segment(x) for x in value.split("/")]
    require(len(parts) <= MAX_DEPTH, "path exceeds depth cap")
    return parts

def unique_object(pairs):
    obj = dict(pairs)
    require(len(obj) == len(pairs), "duplicate JSON key")
    return obj

def load_json(path):
    with Path(path).open("rb") as f:
        data = f.read(MAX_BYTES + 1)
    require(len(data) <= MAX_BYTES, "JSON input exceeds byte cap")
    def reject_const(_):
        raise ValueError("nonfinite JSON number")
    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=unique_object,
                          parse_constant=reject_const)
    except RecursionError as exc:
        raise ValueError("JSON nesting limit exceeded") from exc

def canonical(obj):
    return (json.dumps(obj, ensure_ascii=True, sort_keys=True, separators=(",", ":"))+"\n").encode("ascii")

def content_hash(data):
    return hashlib.sha256(data).hexdigest()

def git_tree_hash(entries):
    # Git sorts a tree entry as if its name ends in "/" and serializes mode 040000
    # as 40000. No Git commands, checkout, worktree filters, or external execution.
    def order(e):
        return e["path"].encode("utf-8") + (b"/" if e["mode"] == "040000" else b"")
    payload = b"".join(("%o" % int(e["mode"], 8)).encode("ascii") + b" " +
                       e["path"].encode("utf-8") + b"\0" + bytes.fromhex(e["sha"])
                       for e in sorted(entries, key=order))
    return hashlib.sha1(b"tree " + str(len(payload)).encode("ascii") + b"\0" + payload).hexdigest()

def verify(provider, allowlist, capture):
    exact(allowlist, "schema providers")
    require(allowlist["schema"] == "proofbridge.github-allowlist.v1", "unknown allowlist schema")
    providers = allowlist["providers"]
    require(type(providers) is dict and len(providers) <= MAX_PROVIDERS, "bad provider registry")
    require(type(provider) is str and PROVIDER.fullmatch(provider) and provider in providers,
            "provider not approved")
    policy = providers[provider]
    exact(policy, "repo commit tree paths max_files evidence")
    repo = policy["repo"]
    require(type(repo) is str and REPO.fullmatch(repo) and not any(x in (".","..") for x in repo.split("/")),
            "invalid repository")
    commit = sha(policy["commit"])
    approved_tree = sha(policy["tree"])
    require(policy["evidence"] == "source_path_only", "evidence promotion not permitted")
    cap, paths = policy["max_files"], policy["paths"]
    require(type(cap) is int and 1 <= cap <= MAX_FILES and type(paths) is list
            and 1 <= len(paths) <= cap, "path count outside approved cap")
    for path in paths:
        path_parts(path)
        require(path.endswith(".lean"), "only .lean source paths are approved")
    require(len(set(paths)) == len(paths), "duplicate approved path")

    api = f"https://api.github.com/repos/{repo}/git"
    web = f"https://github.com/{repo}/blob/{commit}"
    exact(capture, "schema commit trees corroboration")
    require(capture["schema"] == "proofbridge.github-metadata.v1", "unknown capture schema")
    ref = capture["commit"]
    exact(ref, "sha url tree")
    require(sha(ref["sha"]) == commit and ref["url"] == f"{api}/commits/{commit}",
            "commit does not match approved repository/revision")
    exact(ref["tree"], "sha url")
    root = sha(ref["tree"]["sha"])
    require(root == approved_tree, "root tree does not match approved revision metadata")
    require(ref["tree"]["url"] == f"{api}/trees/{root}", "wrong root tree origin")

    trees = capture["trees"]
    require(type(trees) is list and 1 <= len(trees) <= MAX_TREES, "tree count outside cap")
    index, entries_total = {}, 0
    for t in trees:
        exact(t, "sha url truncated tree")
        tid = sha(t["sha"])
        require(t["url"] == f"{api}/trees/{tid}" and t["truncated"] is False,
                "unexpected tree origin or incomplete tree")
        require(tid not in index, "duplicate tree capture")
        entries = t["tree"]
        require(type(entries) is list, "expected a nonrecursive Git tree")
        entries_total += len(entries)
        require(entries_total <= MAX_ENTRIES, "tree entry cap exceeded")
        names = {}
        for e in entries:
            exact(e, "path mode type sha")
            name, mode = segment(e["path"]), e["mode"]
            require(type(mode) is str and mode in VALID_MODES and VALID_MODES[mode] == e["type"],
                    "invalid Git mode/type")
            sha(e["sha"])
            require(name not in names, "duplicate tree name")
            names[name] = e
        require(git_tree_hash(entries) == tid, "Git tree hash mismatch")
        index[tid] = names

    corroboration = capture["corroboration"]
    require(type(corroboration) is list and len(corroboration) == len(paths), "missing file corroboration")
    proof = {}
    approved = set(paths)
    for e in corroboration:
        exact(e, "path sha url")
        path_parts(e["path"])
        path = e["path"]
        require(path in approved and path not in proof and e["url"] == f"{web}/{quote(path)}",
                "unexpected file path or pinned URL")
        proof[path] = sha(e["sha"])

    used, rows = set(), []
    for path in sorted(paths):
        tree_id = root
        parts = path_parts(path)
        for i, part in enumerate(parts):
            require(tree_id in index, "missing required tree metadata")
            used.add(tree_id)
            names = index[tree_id]
            require(part in names, "approved path absent from pinned tree")
            e = names[part]
            if i == len(parts)-1:
                require(e["mode"] in REGULAR and e["type"] == "blob", "not a regular Lean Git source blob")
                require(proof[path] == e["sha"], "file corroboration disagrees with pinned tree")
                rows.append({"path": path, "sha": e["sha"]})
            else:
                require(e["mode"] == "040000" and e["type"] == "tree", "intermediate path is not a Git tree")
                tree_id = e["sha"]
    require(used == set(index), "unreferenced tree metadata outside approved paths")
    return rows, {
        "repo": repo, "commit": commit, "tree": root, "count": len(rows),
        "count_unit": "selected Lean file paths, not theorem/declaration/build counts",
        "evidence": "source_path_only",
        "scope": "explicit approved sample, not complete repository inventory",
    }

def products(provider, allowlist, capture):
    rows, record = verify(provider, allowlist, capture)
    index = b"".join(canonical(row) for row in rows)
    receipt = {"schema": "proofbridge.external-source-snapshot.v1", "provider": provider,
               **record, "rows_sha256": content_hash(index),
               "capture_sha256": content_hash(canonical(capture)),
               "authorization_sha256": content_hash(canonical(allowlist)),
               "tree_object_hashes_recomputed": True, "source_bytes_fetched_by_adapter": False,
               "source_bytes_verified": False, "lean_replay": False}
    return index, record, receipt

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--provider", required=True)
    parser.add_argument("--allowlist", type=Path, required=True)
    parser.add_argument("--capture", type=Path, required=True)
    parser.add_argument("--format", choices=("rows", "providers", "receipt"), default="rows")
    args = parser.parse_args(argv)
    import sys
    try:
        index, provider, receipt = products(args.provider, load_json(args.allowlist), load_json(args.capture))
    except (ValueError, OSError) as exc:
        parser.error(str(exc))
    sys.stdout.buffer.write({"rows": index, "providers": canonical({args.provider: provider}),
                             "receipt": canonical(receipt)}[args.format])

if __name__ == "__main__":
    main()
