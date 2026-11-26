#!/usr/bin/env python3
"""Verify local GitHub tree metadata and create a bounded selected-source index."""
import argparse
import hashlib
import json
from collections import defaultdict
from pathlib import Path
import re
import statistics
import time

CAP_BYTES = 16 * 1024 * 1024
CAP_ENTRIES = 50_000
CAP_FILES = 25_000
CAP_DEPTH = 32
CAP_SLICES = 64
CAP_PARENTS = 128
REGULAR = {"100644", "100755"}
MODES = {**dict.fromkeys(REGULAR, "blob"), "040000":"tree", "120000":"blob", "160000":"commit"}

def check(ok, spec):
    if not ok:
        raise ValueError(spec)

def keys(obj, names):
    check(type(obj) is dict and set(obj) == set(names.split()), "wrong metadata fields")

def sha(s):
    check(type(s) is str and re.fullmatch(r"[0-9a-f]{40}",s), "expected full SHA-1 object ID")
    return s

def path(s, maxdepth=CAP_DEPTH):
    check(type(s) is str and 0 < len(s) <= 1024, "bad path length/type")
    parts=s.split("/")
    check(len(parts) <= maxdepth and all(0 < len(x) <= 255 and x not in (".","..") and
          all(ord(c) >= 32 and ord(c) != 127 and c != "\\" for c in x) for x in parts),
          "noncanonical Git path")
    return parts

def row(e, depth):
    keys(e,"path mode type sha")
    path(e["path"],depth)
    check(type(e["mode"]) is str and MODES.get(e["mode"]) == e["type"] and e["mode"] in MODES,
          "bad Git entry mode/type")
    sha(e["sha"])
    return e

def json_bytes(x):
    return (json.dumps(x,sort_keys=True,separators=(",",":"),ensure_ascii=True)+"\n").encode("ascii")

def digest(data):
    return hashlib.sha256(data).hexdigest()

def git_tree(entries):
    # The trailing slash is part of Git's comparison key, not the stored name.
    def cmp(x):
        return x["path"].encode("utf8") + (b"/" if x["mode"]=="040000" else b"")
    payload=b"".join(x["mode"].lstrip("0").encode("ascii")+b" "+x["path"].encode("utf8")+b"\0"+bytes.fromhex(x["sha"])
                     for x in sorted(entries,key=cmp))
    return hashlib.sha1(b"tree "+str(len(payload)).encode("ascii")+b"\0"+payload).hexdigest()

def object_pairs(pairs):
    d=dict(pairs)
    check(len(d)==len(pairs),"duplicate metadata key")
    return d

def load(file):
    with open(file,"rb") as f:
        data=f.read(CAP_BYTES+1)
    check(len(data)<=CAP_BYTES,"metadata byte cap exceeded")
    return json.loads(data.decode(),object_pairs_hook=object_pairs)

def verify(scope,capture):
    keys(scope,"schema repo commit root_tree prefixes max_files")
    check(scope["schema"]=="proofbridge.github-prefix-allowlist.v1","unknown policy schema")
    repo=scope["repo"]
    check(type(repo) is str and re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+",repo)
          and all(x not in (".","..") for x in repo.split("/")),"invalid approved repository")
    api=f"https://api.github.com/repos/{repo}/git/trees/"
    sha(scope["commit"])
    root=sha(scope["root_tree"])
    cap=scope["max_files"]
    check(type(cap) is int and 1<=cap<=CAP_FILES,"bad approved file cap")
    prefixes=scope["prefixes"]
    check(type(prefixes) is list and 1<=len(prefixes)<=CAP_SLICES,"bad list of approved prefixes")
    for prefix in prefixes:
        path(prefix)
    check(len(set(prefixes))==len(prefixes) and
          not any(x!=y and y.startswith(x+"/") for x in prefixes for y in prefixes),
          "duplicate or overlapping approved prefixes")
    keys(capture,"schema parents subtrees")
    check(capture["schema"]=="proofbridge.github-prefix-capture.v1","unknown capture schema")
    parents=capture["parents"]
    subs=capture["subtrees"]
    check(type(parents) is list and 1<=len(parents)<=CAP_PARENTS and
          type(subs) is list and len(subs)==len(prefixes),"metadata request count mismatch/cap")
    entries=0
    def tree_head(t,sub=False):
        nonlocal entries
        keys(t,"sha url truncated entries"+(" prefix" if sub else ""))
        tid=sha(t["sha"])
        check(t["url"]==api+tid and t["truncated"] is False,"unexpected tree origin/truncation")
        check(type(t["entries"]) is list,"bad tree entries array")
        entries+=len(t["entries"])
        check(entries<=CAP_ENTRIES,"tree entries exceed cap")
        return tid
    parent_index={}
    for t in parents:
        h=tree_head(t)
        children={}
        for e in t["entries"]:
            row(e,1)
            n=e["path"]
            check(n not in children,"duplicate parent entry")
            children[n]=e
        check(git_tree(children.values())==h and h not in parent_index,
              "parent tree hash mismatch or duplicate")
        parent_index[h]=children
    used=set()
    seen=set()
    rows=[]
    stats={}
    for t in subs:
        h=tree_head(t,True)
        prefix=t["prefix"]
        check(prefix in prefixes and prefix not in seen,"subtree not in approved scope")
        seen.add(prefix)
        pointer=root
        for component in path(prefix):
            check(pointer in parent_index,"missing approved ancestor tree")
            used.add(pointer)
            e=parent_index[pointer].get(component)
            check(e is not None and e["type"]=="tree","approved prefix not a directory")
            pointer=e["sha"]
        check(pointer==h,"recursive subtree disagrees with approved ancestry")
        child_lists=defaultdict(list)
        expected={"":h}
        names=set()
        selected=0
        for e in t["entries"]:
            row(e,CAP_DEPTH)
            leaf=e["path"]
            check(leaf not in names,"duplicate recursive entry")
            names.add(leaf)
            parent,_,name=leaf.rpartition("/")
            child_lists[parent].append({**e,"path":name})
            if e["type"]=="tree":
                expected[leaf]=e["sha"]
            if e["mode"] in REGULAR and leaf.endswith(".lean"):
                full=prefix+"/"+leaf
                path(full)
                check(len(rows)<cap,"selected files exceed approved cap")
                rows.append({"path":full,"sha":e["sha"]})
                selected+=1
        check(set(child_lists)<=set(expected),"recursive entry lacks parent tree")
        for rel, sha_id in expected.items():
            check(git_tree(child_lists[rel])==sha_id,"recursive tree hash mismatch")
        stats[prefix]={"entries":len(t["entries"]),"directories_verified":len(expected),"lean_paths":selected}
    check(used==set(parent_index),"unused parent metadata")
    return sorted(rows,key=lambda r:r["path"]),stats,entries,len(used)

def output(scope,capture,bits):
    rows,parts,entries,parents=verify(scope,capture)
    buckets=[bytearray() for _ in range(2**bits)]
    digest_rows=hashlib.sha256()
    for row in rows:
        data=json_bytes(row)
        digest_rows.update(data)
        key=hashlib.sha256(row["path"].encode()).digest()[0]>>(8-bits)
        buckets[key].extend(data)
    payload={f"{i:02x}.jsonl":bytes(data) for i,data in enumerate(buckets) if data}
    receipt={"schema":"proofbridge.github-prefix-index.v1","repo":scope["repo"],"commit":scope["commit"],
             "root_tree":scope["root_tree"],"coverage":parts,"source_files":len(rows),"entries_examined":entries,
             "tree_objects_verified":parents+sum(p["directories_verified"] for p in parts.values()),
             "rows_sha256":digest_rows.hexdigest(),"shard_prefix_bits":bits,
             "shards":{name:{"bytes":len(data),"rows":data.count(b"\n"),"sha256":digest(data)} for name,data in payload.items()},
             "status":"source_path_only","source_bytes_checked":False,"lean_replay":False}
    return payload,receipt

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--scope",default="scope.json")
    p.add_argument("--capture",default="capture.json")
    p.add_argument("--bits",type=int,choices=range(1,9),default=4)
    p.add_argument("--benchmark",type=int,choices=range(1,101),default=1)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    try:
        times=[]
        for _ in range(args.benchmark):
            start=time.perf_counter_ns()
            payload,r=output(load(args.scope),load(args.capture),args.bits)
            times.append((time.perf_counter_ns()-start)/1e6)
    except (ValueError,OSError,RecursionError) as error:
        p.error(str(error))
    if args.out:
        args.out.mkdir(parents=True,exist_ok=False)
        for name,data in payload.items():
            (args.out/name).write_bytes(data)
        (args.out/"receipt.json").write_bytes(json_bytes(r))
    print(json.dumps({**r,"benchmark":{"runs":len(times),"min_ms":round(min(times),3),
            "median_ms":round(statistics.median(times),3),"max_ms":round(max(times),3),
            "source_rows_per_second_at_median":round(r["source_files"]*1000/statistics.median(times)),
            "index_bytes":sum(map(len,payload.values()))}},sort_keys=True,indent=2))

if __name__=="__main__":
    main()
