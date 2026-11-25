"""Batch-index pinned Lean package metadata and preserved sources without compiling."""
import argparse, json, re, subprocess, sys
from collections import Counter
from pathlib import Path

ROOT="packages/research/"
SOURCES=("integration/lean-modules.json","vendor/accepted/MANIFEST.json")
HASH=re.compile(r"[0-9a-f]{64}")
REV=re.compile(r"[A-Za-z0-9_./-]+")
ENTRY_ROOT="research/proofbridge-lean"

def git(repo,*args):
    p=subprocess.run(["git","-C",str(repo),*args],capture_output=True,timeout=30)
    if p.returncode:
        raise ValueError(p.stderr.decode(errors="replace")[:500])
    return p.stdout

def snapshot(repo,ref):
    if not REV.fullmatch(ref) or ref.startswith("-"):
        raise ValueError("invalid revision")
    c=git(repo,"rev-parse","--verify",ref+"^{commit}").decode().strip()
    if not re.fullmatch("[0-9a-f]{40}",c):
        raise ValueError("invalid commit")
    def load(p):
        blob=git(repo,"rev-parse","--verify",c+":"+ROOT+p).decode().strip()
        size=int(git(repo,"cat-file","-s",blob))
        if size>8*1024*1024:
            raise ValueError("manifest exceeds size bound")
        return json.loads(git(repo,"cat-file","blob",blob)),blob
    rows={}
    def put(key,**row):
        if key in rows or not HASH.fullmatch(row["declared_sha256"]):
            raise ValueError("duplicate logical ID or invalid digest")
        rows[key]={"id":key,"snapshot":c,**row}
    a,a_blob=load(SOURCES[0])
    for x in a["modules"]:
        put("package:"+x["module"],kind="named_package_module",path=ROOT+x["path"],
            declared_sha256=x["sha256"],imports=x["imports"],record_blob=a_blob,
            status="listed_in_pinned_module_manifest")
    b,b_blob=load(SOURCES[1])
    for x in b["files"]:
        if re.fullmatch(r"source-store/[0-9a-f]{64}\.lean",x["path"]):
            if x["path"].split("/")[-1]!=x["sha256"]+".lean":
                raise ValueError("content-addressed source key mismatch")
            put("retained:"+x["sha256"],kind="retained_source_blob",
                path=ROOT+"vendor/accepted/"+x["path"],declared_sha256=x["sha256"],
                git_blob=x["git_blob"],record_blob=b_blob,
                status="listed_in_retained_archive_no_new_build")
    for item in git(repo,"ls-tree","-r","-z",c,"--",ENTRY_ROOT).split(b"\x00"):
        if not item:
            continue
        meta, p=item.decode("ascii").split("\t",1)
        mode, kind, blob=meta.split()
        if kind!="blob" or mode!="100644" or not re.fullmatch(ENTRY_ROOT+r"/[A-Za-z][A-Za-z0-9_]*\.lean",p):
            raise ValueError("unsupported entry in standalone Lean registry")
        size=int(git(repo,"cat-file","-s",blob))
        if size>256*1024:
            raise ValueError("oversized standalone module")
        import hashlib
        digest=hashlib.sha256(git(repo,"cat-file","blob",blob)).hexdigest()
        name=p.split("/")[-1][:-5]
        put("standalone:"+name,kind="standalone_source",path=p,declared_sha256=digest,
            git_blob=blob,status="registered_source_not_a_build")
    return c,rows

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo",type=Path,default=Path(__file__).resolve().parents[3])
    p.add_argument("--at",default="HEAD")
    p.add_argument("--since")
    p.add_argument("--summary",action="store_true")
    p.add_argument("--delta-only",action="store_true")
    a=p.parse_args()
    c,rows=snapshot(a.repo,a.at)
    base,old=snapshot(a.repo,a.since) if a.since else (None,{})
    out=[]
    for key in sorted(set(rows)|set(old)):
        row=rows.get(key) or old[key]
        if not base:
            d="present"
        elif key not in rows:
            d="removed"
        elif key not in old:
            d="new"
        else:
            fields=("path","declared_sha256","imports","git_blob")
            d="changed" if any(row.get(k)!=old[key].get(k) for k in fields) else "unchanged"
        if not a.delta_only or d not in {"unchanged","present"}:
            out.append({"schema":"commons.lean_inventory.record.v1","delta":d,**row})
    summary={"schema":"commons.lean_inventory.summary.v1","snapshot":c,"baseline":base,
             "counts_by_delta":Counter(r["delta"] for r in out),
             "counts_by_kind":Counter(r["kind"] for r in out),"rows":len(out)}
    if a.summary:
        print(json.dumps(summary,sort_keys=True))
    else:
        for r in out:
            print(json.dumps(r,sort_keys=True))

if __name__=="__main__":
    try:
        main()
    except (ValueError,TypeError,KeyError,OSError,subprocess.SubprocessError) as exc:
        print(str(exc),file=sys.stderr)
        sys.exit(2)
