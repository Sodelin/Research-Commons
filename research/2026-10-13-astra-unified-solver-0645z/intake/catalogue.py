#!/usr/bin/env python3
"""Pin the whole public archive without selecting every historical file as current.

No network, compiler, theorem inference, or private-repository access occurs here.
Git object IDs authenticate the archive. Selected Lean bodies receive a separate
SHA256 check against the accepted 1613 graph. The catalogue is a discovery index,
not a proof of mathematical acceptance or executable native correspondence.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
BASE = "7239e89dea5caad68a54227cee3b44a7d9b96389"
PACKAGE = "research/2026-10-12-dot-accepted-connected-union1613-1737z"
REPOSITORY = "Sodelin/Research-Commons"


def git(*args):
    # Git's large default mmap window can exhaust a conservative address-space
    # cap even for a small tree walk. These per-command settings bound windows;
    # no persistent repository or operating-system configuration is changed.
    return subprocess.check_output(["git", "-c", "core.packedGitWindowSize=16m",
                                    "-c", "core.packedGitLimit=64m",
                                    "-C", str(REPO), *args])


def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def sha(data):
    return hashlib.sha256(data).hexdigest()


def object_rows(ref):
    rows = []
    for raw in git("ls-tree", "-r", "-l", "-z", ref).split(b"\0"):
        if not raw:
            continue
        head, path = raw.split(b"\t", 1)
        mode, kind, blob, size = head.decode("ascii").split()
        rows.append({"path": path.decode("utf-8"), "git_object": blob,
                     "kind": kind, "mode": mode,
                     "bytes": None if size == "-" else int(size)})
    return rows


def build(ref, destination):
    if not re.fullmatch(r"[0-9a-f]{40}", ref):
        raise ValueError("use an immutable full 40-character Git commit, not a branch")
    commit = git("rev-parse", ref + "^{commit}").decode().strip()
    if commit != ref:
        raise ValueError("the supplied object must be a commit")
    rows = object_rows(ref)
    lookup = {row["path"]: row for row in rows}
    tree_stream = b"".join(encoded(row) for row in rows)
    compressed = gzip.compress(tree_stream, compresslevel=6, mtime=0)
    packets = {}
    for row in rows:
        parts = row["path"].split("/")
        key = "/".join(parts[:2]) if len(parts) > 2 else parts[0]
        record = packets.setdefault(key, {"path": key, "files": 0, "bytes": 0,
                                         "entry_points": []})
        record["files"] += 1
        record["bytes"] += row["bytes"] or 0
        if parts[-1] in {"README.md", "REPORT.md", "CURRENT-SCOPE.md", "AGENTS.md",
                         "PROOF.md", "Cargo.toml", "lakefile.lean", "lakefile.toml",
                         "MANIFEST.json", "PUBLICATION.json"}:
            record["entry_points"].append(row["path"])
    catalogue = {
        "schema": "research_commons_discovery_v1", "repository": REPOSITORY,
        "snapshot_commit": ref, "snapshot_tree": git("rev-parse", ref + "^{tree}").decode().strip(),
        "scope": "all tracked public paths at this commit, including older work",
        "acceptance_rule": "presence, filename, date and file counts do not establish acceptance",
        "inventory": {"path": "TREE.jsonl.gz", "sha256": sha(compressed),
                      "uncompressed_sha256": sha(tree_stream), "records": len(rows)},
        "packets": sorted(packets.values(), key=lambda row: row["path"]),
    }
    graph_path = PACKAGE + "/DEPENDENCY-GRAPH.json"
    graph_bytes = git("show", BASE + ":" + graph_path)
    target = json.loads(graph_bytes)["targets"]["current/connected"]
    base_lookup = {row["path"]: row for row in object_rows(BASE)}
    modules = []
    for name in target["order"]:
        row = target["modules"][name]
        path = PACKAGE + "/source-store/" + row["sha256"] + ".lean"
        # Read only public source. A workspace edit cannot pass without exactly
        # matching both the selected SHA256 and the immutable Git blob.
        data = (REPO / path).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if sha(data) != row["sha256"] or blob != base_lookup[path]["git_object"]:
            raise ValueError("selected source identity mismatch: " + name)
        # Some original graph values omit their name because it is the map
        # key. Preserve that authoritative key explicitly in this list form.
        modules.append({**row, "module": name, "path": path, "git_blob": blob, "bytes": len(data),
                        "aggregate_root": name in target["roots"]})
    aggregate = "".join("import " + name + "\n" for name in target["roots"]).encode()
    selected = {
        "schema": "selected_lean_graph_v1", "repository": REPOSITORY,
        "accepted_package_commit": BASE, "package": PACKAGE,
        "selected_target": "current/connected", "graph_path": graph_path,
        "graph_sha256": sha(graph_bytes), "aggregate_sha256": sha(aggregate),
        "roots": target["roots"], "external_imports": target["external_imports"],
        "modules": modules,
        "execution_status": "historical accepted component reuse plus fresh aggregate/audit; this intake authenticates source bytes only",
        "fresh_intake_source_authentication": "all selected bodies checked for SHA256 and immutable Git blob equality",
        "evidence": [PACKAGE + "/evidence/FINAL-RECEIPT.json.projected",
                     PACKAGE + "/evidence/LAKE-ATTEMPT1-TERMINAL.json.projected",
                     PACKAGE + "/lakefile.lean", PACKAGE + "/scripts/run_current.py"],
    }
    outputs = {"TREE.jsonl.gz": compressed, "CATALOGUE.json": encoded(catalogue),
               "SELECTED-LEAN.json": encoded(selected)}
    destination.mkdir(parents=True, exist_ok=True)
    for name, data in outputs.items():
        target_file = destination / name
        if target_file.exists() and target_file.read_bytes() != data:
            raise ValueError("refuse to overwrite a different snapshot: " + str(target_file))
        target_file.write_bytes(data)
    return {"status": "SOURCE_AND_ARCHIVE_INDEX_VERIFIED", "snapshot_commit": ref,
            "fresh_compilation": False,
            "files": {name: {"bytes": len(data), "sha256": sha(data)} for name, data in outputs.items()}}


def query(directory, module, path):
    if module:
        data = json.loads((directory / "SELECTED-LEAN.json").read_bytes())
        matches = [row for row in data["modules"] if row["module"] == module]
        return {"selection_commit": data["accepted_package_commit"], "matches": matches,
                "missing_means": "not selected in public1613; does not prove absent from all historical work"}
    data = json.loads((directory / "CATALOGUE.json").read_bytes())
    blob = (directory / data["inventory"]["path"]).read_bytes()
    if sha(blob) != data["inventory"]["sha256"]:
        raise ValueError("archive inventory identity mismatch")
    matches = []
    for line in gzip.decompress(blob).splitlines():
        row = json.loads(line)
        if row["path"] == path or row["path"].startswith(path.rstrip("/") + "/"):
            matches.append(row)
    return {"snapshot_commit": data["snapshot_commit"], "matches": matches}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="command", required=True)
    create = subs.add_parser("build")
    create.add_argument("--ref", required=True)
    create.add_argument("--output", type=Path, default=HERE)
    find = subs.add_parser("query")
    find.add_argument("--directory", type=Path, default=HERE)
    selection = find.add_mutually_exclusive_group(required=True)
    selection.add_argument("--module")
    selection.add_argument("--path")
    args = parser.parse_args()
    try:
        result = build(args.ref, args.output) if args.command == "build" else query(args.directory, args.module, args.path)
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        print(json.dumps({"status": "REFUSED", "reason": str(error)}))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
