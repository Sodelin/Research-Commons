#!/usr/bin/env python3
"""Offline Lean source closure. Never downloads, executes, or compiles."""
import argparse, hashlib, json, re
from pathlib import Path, PurePosixPath

module = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
repo = re.compile(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
hex40 = re.compile(r"[a-f0-9]{40}")
hex64 = re.compile(r"[a-f0-9]{64}")
version = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]{0,95}")

def lean_header(data):
    """Top-level imports; ordinary nested comments, module flags, import all."""
    s = data.decode("utf-8-sig")
    n, i = len(s), 0
    def skip():
        nonlocal i
        while i < n:
            if s[i].isspace():
                i += 1
            elif s.startswith("--", i):
                end = s.find("\n", i+2)
                i = n if end < 0 else end+1
            elif s.startswith("/-", i) and not s.startswith(("/--", "/-!"), i):
                i, depth = i+2, 1
                while depth and i < n:
                    if s.startswith("/-", i):
                        i, depth = i+2, depth+1
                    elif s.startswith("-/", i):
                        i, depth = i+2, depth-1
                    else:
                        i += 1
                if depth:
                    raise ValueError("unterminated ordinary header comment")
            else:
                break
    def word():
        nonlocal i
        skip()
        m = module.match(s, i)
        if m:
            i = m.end()
            return m.group()
    imports, prelude, started = [], False, False
    while True:
        skip()
        if i == n or s.startswith(("/--", "/-!"), i):
            break
        t = word()
        if t == "module" and not started:
            started = True
            continue
        if t == "prelude" and not imports and not prelude:
            prelude = started = True
            continue
        if t in ("public", "meta"):
            flags = {t}
            while (t := word()) in ("public", "meta"):
                if t in flags:
                    raise ValueError("repeated import flag")
                flags.add(t)
        if t != "import":
            if t in ("prelude", "module"):
                raise ValueError("unexpected header marker")
            break
        started = True
        target = word()
        if target == "all":
            target = word()
        if target is None or (i < n and not (s[i].isspace() or s.startswith(("--","/-"), i))):
            raise ValueError("missing or unsupported import identifier/separator")
        imports.append(target)
    return list(dict.fromkeys(([] if prelude else ["Init"])+imports))

def path_inside(base, path):
    if not isinstance(path,str) or any(x in ("", ".", "..") for x in path.split("/")) or "\\" in path:
        raise ValueError(f"unsafe relative path: {path!r}")
    root = base.resolve()
    q = (root / PurePosixPath(path)).resolve()
    if not q.is_relative_to(root):
        raise ValueError(f"resolved outside root: {path!r}")
    return q

def source_path(m):
    if not isinstance(m,str) or not module.fullmatch(m):
        raise ValueError(f"unsupported module name: {m!r}")
    return m.replace(".", "/")+".lean"

def namespace(m,p):
    return m == p or m.startswith(p+".")

def check_cfg(cfg):
    if cfg.get("schema") != "commons.lean-source-planner.v1" or not cfg.get("targets"):
        raise ValueError("supported schema and nonempty targets required")
    for m in cfg["targets"]:
        source_path(m)
    for k in ("version", "toolchain"):
        if not version.fullmatch(cfg.get(k,"")):
            raise ValueError(f"explicit safe {k} required")
    repos, bindings = set(), {}
    for r in cfg.get("repositories", []):
        name, commit = r["repo"], r["commit"]
        if not repo.fullmatch(name) or any(x in (".", "..") for x in name.split("/")) or not hex40.fullmatch(commit):
            raise ValueError(f"invalid repository or non-immutable pin: {name!r}")
        if name.lower() in repos:
            raise ValueError(f"repository duplicated or multiple pins selected: {name!r}")
        repos.add(name.lower())
        if r["source_prefix"]:
            path_inside(Path("/"), r["source_prefix"])
        for p in r["module_prefixes"]:
            source_path(p)
            if p in bindings:
                raise ValueError(f"ambiguous repository prefix {p!r}")
            bindings[p] = r
        for m, blob in r.get("blobs",{}).items():
            source_path(m)
            if not hex40.fullmatch(blob) or not any(namespace(m,p) for p in r["module_prefixes"]):
                raise ValueError(f"invalid git blob pin/namespace for {m}")
    for m, rec in cfg.get("local_sources",{}).items():
        source_path(m)
        if not hex64.fullmatch(rec["sha256"]):
            raise ValueError(f"local sha256 required for {m}")
        path_inside(Path("/"), rec["path"])
    for p in cfg.get("toolchain_module_prefixes", []):
        source_path(p)
    return bindings

def git_blob(data):
    return hashlib.sha1(b"blob "+str(len(data)).encode("ascii")+b"\0"+data).hexdigest()
def sha256(data):
    return hashlib.sha256(data).hexdigest()

def plan(cfg, store, local_root):
    binding = check_cfg(cfg)
    local = cfg.get("local_sources", {})
    builtin_prefixes = cfg.get("toolchain_module_prefixes", [])
    entries, order, requests, stack, cycles = {}, [], [], [], set()
    def walk(m):
        if m in stack:
            cycles.add(tuple(stack[stack.index(m):]+[m]))
            return
        if m in entries:
            return
        row = entries[m] = {"module":m, "imports":[]}
        selected = sorted((p for p in binding if namespace(m,p)), key=len, reverse=True)
        builtin = any(namespace(m,p) for p in builtin_prefixes)
        if sum((m in local, bool(selected), builtin)) > 1:
            row.update(status="ambiguous_origin")
            return
        if builtin:
            row.update(status="toolchain_dependency_unverified",toolchain=cfg["toolchain"])
            return
        if m in local:
            spec = local[m]
            path = path_inside(local_root,spec["path"])
            verify, expected, status = sha256,spec["sha256"],"local_source_present"
            row["local_path"] = spec["path"]
            if not path.is_file():
                row.update(status="missing_local_source")
                return
        elif selected:
            r = binding[selected[0]]
            inner = "/".join(filter(None, [r["source_prefix"],source_path(m)]))
            rel = f"{cfg['version']}/{r['repo']}/{r['commit']}/{inner}"
            path = path_inside(store,rel)
            verify, expected, status = git_blob,r.get("blobs",{}).get(m),"pinned_source_present"
            row.update(repo=r["repo"],commit=r["commit"],repo_path=inner,staging_path=rel,
                       expected_git_blob=expected)
            if not path.is_file() or not expected:
                row.update(status="pending_source" if not path.is_file() else "pending_blob_attestation")
                requests.append({"repo":r["repo"],"ref":r["commit"],"path":inner,"module":m,
                                 "staging_path":rel,"expected_git_blob":expected})
                return
        else:
            row.update(status="unmapped_import")
            return
        data = path.read_bytes()
        actual = verify(data)
        if actual != expected:
            row.update(status="integrity_mismatch",expected=expected,actual=actual)
            return
        row["sha256"] = sha256(data)
        try:
            imports = lean_header(data)
        except (UnicodeError, ValueError) as e:
            row.update(status="unsupported_header",detail=str(e))
            return
        row.update(status=status,imports=imports)
        stack.append(m)
        for imp in imports:
            walk(imp)
        stack.pop()
        order.append(m)
    for t in cfg["targets"]:
        walk(t)
    okay = {"local_source_present","pinned_source_present","toolchain_dependency_unverified"}
    blocking = sorted(m for m,row in entries.items() if row["status"] not in okay)
    return {"schema":"commons.lean-source-plan.v1","version":cfg["version"],"toolchain":cfg["toolchain"],
            "targets":cfg["targets"],"package_source_closure":"incomplete" if blocking or cycles else "present",
            "scope":"Explicit source-header imports; declared toolchain prefixes excluded and unresolved",
            "compilability":"not_checked","toolchain_dependency_status":"not_checked",
            "dependency_first_source_order":None if cycles else order,
            "entries":entries,"blocking_modules":blocking,
            "cycles":[list(c) for c in sorted(cycles)],"fetch_requests":requests}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("config",type=Path)
    p.add_argument("--source-store",required=True,type=Path)
    p.add_argument("--local-root",required=True,type=Path)
    a=p.parse_args()
    try:
        r=plan(json.loads(a.config.read_text()),a.source_store,a.local_root)
    except (KeyError,TypeError,ValueError,OSError) as e:
        p.error(str(e))
    print(json.dumps(r,indent=2,sort_keys=True))
    return 0 if r["package_source_closure"] == "present" else 2

if __name__=="__main__":
    raise SystemExit(main())
