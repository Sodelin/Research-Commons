"""Index committed source, never run it. All proof labels are discovery hints."""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOTS = ("research", "packages/research", "lean", "docs/discovery/lean-bank")
LIMIT = 1_000_000
DECL = re.compile(r"(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|inductive|structure|abbrev)\s+([^\s:(<{\[]+)")
HEADING = re.compile(r"(?m)^#\s+(.{1,180})$")

def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])

def kind(path):
    if path.endswith(".lean"):
        return "lean_source"
    if path.endswith((".md", ".mdx")) and not path.startswith("docs/discovery/lean-bank/tools/"):
        return "research_note"
    if path.endswith((".receipt.json", "-receipt.json", "/receipt.json", "/SHA256SUMS")):
        return "receipt_locator"
    return None

def discover(root, ref):
    if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", ref):
        raise ValueError("an immutable full Git commit is required")
    actual = git(root, "rev-parse", "--verify", ref+"^{commit}").decode().strip()
    if actual != ref:
        raise ValueError("source identifier does not name the exact commit")
    # Read paths and object IDs from Git, not filesystem enumeration or symlinks.
    raw = git(root, "ls-tree", "-r", "-z", "--full-tree", ref, "--", *ROOTS)
    selected = []
    for item in raw.split(b"\x00"):
        if not item:
            continue
        head,path = item.split(b"\t",1)
        mode,typ,blob = head.split()
        path = path.decode("utf-8","replace")
        category = kind(path)
        if mode in (b"100644",b"100755") and typ==b"blob" and category:
            selected.append((path,blob,category))
    rows=[]
    owner=subprocess.Popen(["git","-C",str(root),"cat-file","--batch"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    try:
        for path,blob,category in selected:
            owner.stdin.write(blob+b"\n")
            owner.stdin.flush()
            returned,typ,size=owner.stdout.readline().split()
            if returned!=blob or typ!=b"blob":
                raise ValueError("Git returned a different object")
            size=int(size)
            text=""
            if size<=LIMIT:
                text=owner.stdout.read(size).decode("utf-8","replace")
            else:
                remaining=size
                while remaining:
                    data=owner.stdout.read(min(remaining,65536))
                    if not data: raise ValueError("short Git object")
                    remaining-=len(data)
            if owner.stdout.read(1)!=b"\n":
                raise ValueError("malformed Git object boundary")
            # Names are search hints only. Comments, notation and namespace rules
            # are not a Lean parser, and no checked declaration is inferred.
            names=list(dict.fromkeys(DECL.findall(text)))[:256] if category=="lean_source" else []
            h=HEADING.search(text) if category=="research_note" else None
            rows.append({"source_commit":ref,"path":path,"git_blob":blob.decode(),"kind":category,
                         "title":h[1].strip() if h else Path(path).name,"declaration_hints":names,
                         "evidence":"indexed_only"})
    finally:
        owner.stdin.close()
        owner.stdout.close()
        if owner.wait(): raise ValueError("git cat-file failed")
    return rows

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,default=Path.cwd())
    p.add_argument("--commit",required=True)
    p.add_argument("--dest",type=Path,required=True)
    args=p.parse_args()
    rows=discover(args.root,args.commit)
    args.dest.mkdir(parents=True,exist_ok=True)
    path=args.dest/"index.jsonl"
    payload="".join(json.dumps(row,ensure_ascii=False,separators=(",",":"))+"\n" for row in rows)
    path.write_text(payload,encoding="utf-8")
    meta={"schema":"commons.discovery.git-source-index.v1","source_commit":args.commit,"rows":len(rows),
          "sha256":hashlib.sha256(payload.encode()).hexdigest(),"evidence":"indexed_only"}
    (args.dest/"receipt.json").write_text(json.dumps(meta,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(meta))
if __name__=="__main__":
    main()
