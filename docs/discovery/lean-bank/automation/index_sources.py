"""Index committed source, never run it. All proof labels are discovery hints."""
import argparse
import hashlib
import json
import re
import subprocess
from collections import defaultdict
from pathlib import Path

ROOTS = ("research", "packages/research", "lean", "docs/discovery/lean-bank")
LIMIT = 1_000_000
HINT_VERSION = 'line-hints.v1'
LEGACY_HINT_SNAPSHOT = ('0cfd1b7a1fa2d5d544ceb9bd195e3b7dbfe565e3', '5eb5932eda63afa5c1f6523b58a78864a8268f44c9c8147146217630de92714b')
DECL = re.compile(r"(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma|def|inductive|structure|abbrev)\s+([^\s:(<{\[]+)")
HEADING = re.compile(r"(?m)^#\s+(.{1,180})$")

def git(root, *args):
    return subprocess.check_output(["git","--no-replace-objects", "-C", str(root), *args])

def kind(path):
    if path.endswith(".lean"):
        return "lean_source"
    if path.endswith((".md", ".mdx")) and not path.startswith("docs/discovery/lean-bank/tools/"):
        return "research_note"
    if path.endswith((".receipt.json", "-receipt.json", "/receipt.json", "/SHA256SUMS")):
        return "receipt_locator"
    return None

def read_cache(root):
    if root is None or not (root/"receipt.json").is_file():
        return {}, "absent"
    try:
        manifest=json.loads((root/"receipt.json").read_text())
        if manifest.get("schema")!="commons.discovery.git-source-index.v2":
            return {}, "unsupported_previous_schema"
        if (manifest.get("hint_version")!=HINT_VERSION and
                (manifest.get("source_commit"),manifest.get("sha256"))!=LEGACY_HINT_SNAPSHOT):
            return {}, "previous_hint_version"
        files=manifest["shards"]
        if [s["path"] for s in files]!=[f"shards/{i:02x}.jsonl" for i in range(256)]:
            raise ValueError("unexpected shard list")
        aggregate=hashlib.sha256(); result={}
        for spec in files:
            data=(root/spec["path"]).read_bytes()
            if hashlib.sha256(data).hexdigest()!=spec["sha256"]:
                raise ValueError("shard bytes changed")
            records=data.splitlines()
            if len(records)!=spec["rows"]:
                raise ValueError("shard row count mismatch")
            aggregate.update(data)
            for raw in records:
                r=json.loads(raw)
                keys={"path","git_blob","kind","title","declaration_hints","evidence"}
                if set(r)!=keys or r["evidence"]!="indexed_only" or r["path"] in result:
                    raise ValueError("unreusable cache row")
                if not isinstance(r["title"],str) or not isinstance(r["declaration_hints"],list) or not all(isinstance(x,str) for x in r["declaration_hints"]):
                    raise ValueError("invalid cache text fields")
                result[r["path"]]=r
        if len(result)!=manifest["rows"] or aggregate.hexdigest()!=manifest["sha256"]:
            raise ValueError("cache aggregate mismatch")
        return result, "verified"
    except (OSError,ValueError,TypeError,KeyError):
        return {}, "rejected_rebuild"

def discover(root, ref, cache=None, metrics=None):
    cache={} if cache is None else cache
    metrics={} if metrics is None else metrics
    metrics.update({"reused_rows":0,"source_bodies_read":0})
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
        path = path.decode("utf-8")
        category = kind(path)
        if mode in (b"100644",b"100755") and typ==b"blob" and category:
            selected.append((path,blob,category))
    rows=[]
    owner=subprocess.Popen(["git","--no-replace-objects","-C",str(root),"cat-file","--batch"],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    try:
        for path,blob,category in selected:
            old=cache.get(path)
            if old and old["git_blob"]==blob.decode() and old["kind"]==category:
                rows.append({"source_commit":ref,**old})
                metrics["reused_rows"]+=1
                continue
            metrics["source_bodies_read"]+=1
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
    p.add_argument("--reuse",type=Path)
    args=p.parse_args()
    cache,state=read_cache(args.reuse)
    metrics={"prior_index":state}
    rows=discover(args.root,args.commit,cache,metrics)
    args.dest.mkdir(parents=True,exist_ok=True)
    # Shard by path, not offsets. A new commit changes only affected buckets.
    # The source commit is bound once by the manifest, not repeated in every row.
    groups=defaultdict(list)
    for row in rows:
        key=hashlib.sha256(row["path"].encode()).hexdigest()[:2]
        record={k:v for k,v in row.items() if k!="source_commit"}
        groups[key].append(json.dumps(record,ensure_ascii=False,separators=(",",":"))+"\n")
    (args.dest/"shards").mkdir(exist_ok=True)
    digest=hashlib.sha256()
    entries=[]
    for i in range(256):
        key=f"{i:02x}"
        payload="".join(groups[key]).encode()
        f=f"shards/{key}.jsonl"
        (args.dest/f).write_bytes(payload)
        digest.update(payload)
        entries.append({"path":f,"rows":len(groups[key]),"sha256":hashlib.sha256(payload).hexdigest()})
    meta={"schema":"commons.discovery.git-source-index.v2","source_commit":args.commit,"rows":len(rows),
          "sha256":digest.hexdigest(),"evidence":"indexed_only","shards":entries,"scan":metrics,"hint_version":HINT_VERSION}
    (args.dest/"receipt.json").write_text(json.dumps(meta,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(meta))
if __name__=="__main__":
    main()
