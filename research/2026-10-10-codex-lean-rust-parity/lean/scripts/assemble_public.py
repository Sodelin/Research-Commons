#!/usr/bin/env python3
"""Freeze public proof bytes and explicit version-separated import closures.

Only public checked source packets are inputs. A historical certificate is not
used as a source manifest. No compiler objects, held source trees, or remote
workflows are imported. Re-running this script verifies existing source blobs.
"""
from __future__ import annotations
import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parents[2]
IMPORT = re.compile(r"(?:^|\n)\s*(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)")
STORE = ROOT / "source-store"
EXTERNAL = ("Mathlib", "Lean", "Std", "Init", "Lake", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient")

def imports(text):
    # Lean block comments nest. Documentation can contain apparent `import`
    # lines, and literal strings are not import commands either.
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == "/-": depth += 1; out.extend("  "); i += 2
            elif pair == "-/": depth -= 1; out.extend("  "); i += 2
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif quoted:
            if text[i] == "\\": out.extend("  "); i += 2
            elif text[i] == '"': quoted = False; out.append(" "); i += 1
            else: out.append("\n" if text[i] == "\n" else " "); i += 1
        elif pair == "/-": depth = 1; out.extend("  "); i += 2
        elif pair == "--":
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
            out.extend(" " * (j-i)); i = j
        elif text[i] == '"': quoted = True; out.append(" "); i += 1
        else: out.append(text[i]); i += 1
    assert depth == 0 and not quoted
    return list(dict.fromkeys(IMPORT.findall("".join(out))))

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def load(rel: str):
    return json.loads((REPO / rel).read_bytes())

def save(name: str, value):
    (ROOT / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

def clean(row):
    return {k: row[k] for k in ("module", "sha256", "imports")}

def topo(roots, modules):
    order, active, done, external = [], set(), set(), set()
    def visit(name):
        if name in done:
            return
        if name not in modules:
            if name.split(".")[0] in EXTERNAL:
                external.add(name)
                return
            raise RuntimeError("Missing public logical provider " + name)
        if name in active:
            raise RuntimeError("Import cycle " + name)
        active.add(name)
        for dep in modules[name]["imports"]:
            visit(dep)
        active.remove(name)
        done.add(name)
        order.append(name)
    for name in roots:
        visit(name)
    return {"roots": roots, "order": order,
            "modules": {name: modules[name] for name in order},
            "external_imports": sorted(external)}

def main(fetch_missing=False):
    STORE.mkdir(exist_ok=True)
    origins = {}
    source_index = {}
    blob_index = {}
    g5pins = "research/2026-10-10-dot-g5-full-binary-m3-0209z/PROVIDER-SOURCE-PINS.json"
    for row in load(g5pins)["providers"]:
        blob_index[row["sha256"]] = (row["git_blob"], g5pins)
    g7pins = "research/2026-10-09-dot-g7-completed-calendar-polynomial-2330z/DEPENDENCY-HASHES.json"
    for row in load(g7pins)["sources"]:
        if row.get("public_git_blob"):
            blob_index[row["source_sha256"]] = (row["public_git_blob"], g7pins)
    # All entries here are already available in the checkout. This does not
    # authenticate unavailable files merely because a hash appears in prose.
    tracked = subprocess.check_output(["git", "ls-files", "*.lean"], cwd=REPO, text=True).splitlines()
    for rel in tracked:
        path = REPO / rel
        data = path.read_bytes()
        digest = sha(data)
        source_index.setdefault(digest, path)
        origins.setdefault(digest, []).append(rel)

    def install(row):
        digest = row["sha256"]
        path = source_index.get(digest)
        if path is None:
            if digest not in blob_index:
                raise RuntimeError(f"Missing public source bytes {row['module']} {digest}")
            blob, pinfile = blob_index[digest]
            existing = STORE / (digest + ".lean")
            if existing.is_file():
                data = existing.read_bytes()
            else:
                local = subprocess.run(["git", "cat-file", "blob", blob], cwd=REPO, capture_output=True)
                if local.returncode == 0:
                    data = local.stdout
                elif fetch_missing:
                    url = "https://api.github.com/repos/Sodelin/Research-Commons/git/blobs/" + blob
                    with urllib.request.urlopen(url, timeout=30) as response:
                        public_blob = json.load(response)
                    assert public_blob["sha"] == blob and public_blob["encoding"] == "base64"
                    data = base64.b64decode(public_blob["content"])
                else:
                    raise RuntimeError(f"Public blob {blob} requires --fetch-missing HTTPS retrieval")
            assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == blob
            origins.setdefault(digest, []).append(f"git-blob:{blob} pinned-by:{pinfile}")
        else:
            data = path.read_bytes()
        assert sha(data) == digest
        dest = STORE / (digest + ".lean")
        if dest.exists():
            assert dest.read_bytes() == data
        else:
            dest.write_bytes(data)
        assert imports(data.decode()) == row["imports"], row["module"]

    oldrel = "research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/DEPENDENCY-GRAPH.json"
    old = load(oldrel)
    targets = {}
    for label, target in old["targets"].items():
        modules = {name: clean(row) for name, row in target["modules"].items()}
        for row in modules.values():
            install(row)
        targets["historical/" + label] = topo(target["roots"], modules)
        targets["historical/" + label]["source_contract"] = oldrel

    current = {name: clean(row) for name, row in old["targets"]["connected/compatible"]["modules"].items()}
    replacements = []
    def merge(modules, origin):
        for name, row in modules.items():
            row = clean({**row, "module": name})
            install(row)
            if name in current and current[name]["sha256"] != row["sha256"]:
                replacements.append({"module": name, "old": current[name]["sha256"], "new": row["sha256"], "origin": origin})
            current[name] = row

    g2rel = "research/2026-10-10-dot-g2-current-source-verification-0042z/DEPENDENCY-GRAPH.json"
    g2 = next(iter(load(g2rel)["targets"].values()))
    merge(g2["modules"], g2rel)
    targets["current/G2"] = topo(g2["roots"], current)

    g5path = ROOT / "inherited/G5-DEPENDENCY-GRAPH.json"
    g5 = next(iter(json.loads(g5path.read_bytes())["targets"].values()))
    merge(g5["modules"], str(g5path.relative_to(ROOT)))
    targets["current/G5-binary-M3"] = topo(g5["roots"], current)

    packets = [
        ("current/G6-cell", "research/2026-10-10-dot-g6-completed-cell-tv-0258z/CELL-SOURCE-PINS.json"),
        ("current/G6-TV", "research/2026-10-10-dot-g6-completed-cell-tv-0258z/TV-SOURCE-PINS.json"),
        ("current/G6-protected-bin", "research/2026-10-10-dot-g6-protected-bin-bridge-0912z/SOURCE-PINS.json"),
    ]
    for label, rel in packets:
        packet = load(rel)
        modules = {row["module"]: row for row in packet["sources"]}
        merge(modules, rel)
        targets[label] = topo(packet["roots"], current)
        assert targets[label]["order"] == packet["topological_order"], label

    # Accepted G7 noncomputable representation and registry admission are
    # distinct from the later failed executable coefficient candidates.
    g7rel = "research/2026-10-09-dot-g7-completed-calendar-polynomial-2330z/DEPENDENCY-HASHES.json"
    packet = load(g7rel)
    modules = {r["logical_module"]: {"module": r["logical_module"], "sha256": r["source_sha256"], "imports": r["imports"]} for r in packet["sources"]}
    merge(modules, g7rel)
    public_dirs = [
        "research/2026-10-09-dot-g7-completed-calendar-polynomial-2330z",
        "research/2026-10-09-dot-g7-original-registry-admission-1908z/sources",
    ]
    for rel in public_dirs:
        additions = {}
        for path in sorted((REPO / rel).glob("*.lean")):
            if "Audit" in path.stem:
                continue
            data = path.read_bytes()
            additions[path.stem] = {"module": path.stem, "sha256": sha(data), "imports": imports(data.decode())}
        merge(additions, rel)
    targets["current/G7-calendar"] = topo(["G7CompletedCalendarPolynomial"], current)
    targets["current/G7-registry"] = topo(["G7OriginalAdmission", "G7OriginalCensus"], current)
    targets["current/connected"] = topo(sorted(current), current)

    graph = {"schema": "codex-public-version-separated-G1-G7-closure-v1", "targets": targets,
             "historical_53_certificate_replayed_or_reconstructed": False,
             "held_1411_module_graph_included": False, "source_replacements": replacements}
    save("DEPENDENCY-GRAPH.json", graph)
    used = sorted({r["sha256"] for t in targets.values() for r in t["modules"].values()})
    save("SOURCE-MANIFEST.json", {"schema": "exact-public-source-store-v1", "sources": [
        {"sha256": digest, "bytes": (STORE / (digest + ".lean")).stat().st_size,
         "origins": origins[digest], "logical_modules": sorted({name for t in targets.values() for name,r in t["modules"].items() if r["sha256"] == digest})}
        for digest in used], "source_count": len(used), "target_count": len(targets),
        "compile_status": "NOT_A_COMPILATION_RECEIPT"})
    print(json.dumps({"targets": len(targets), "source_versions": len(used),
                      "current_modules": len(targets["current/connected"]["order"]),
                      "replacement_count": len(replacements)}))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-missing", action="store_true", help="Retrieve exact pinned public GitHub blobs over HTTPS when absent locally")
    args = parser.parse_args()
    main(args.fetch_missing)
