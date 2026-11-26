#!/usr/bin/env python3
"""Offline exact-token postings cache for Discovery source metadata; never proof evidence."""
import argparse
from contextlib import closing
import hashlib
import json
import os
from pathlib import Path
import re
import sqlite3
import subprocess
import sys

TOKENIZER = "discovery-search-bank-ascii-camel-v1"
INDEX_SCHEMA = "commons.discovery.git-source-index.v2"
DB_SCHEMA = "commons.discovery.local-postings.v1"
HEX = re.compile(r"(?:[a-f0-9]{40}|[a-f0-9]{64})\Z")
CAMEL = re.compile(r"([a-z0-9])([A-Z])")
TOKEN = re.compile(r"[a-z0-9]+")


def tokens(value):
    return set(TOKEN.findall(CAMEL.sub(r"\1 \2", value).lower()))


def rowterms(row):
    return tokens(json.dumps(row, ensure_ascii=False))


def _sha(data):
    return hashlib.sha256(data).hexdigest()


def _expect(cond, msg):
    if not cond:
        raise ValueError(msg)


def _unique_pairs(items):
    d = dict(items)
    _expect(len(d)==len(items), "duplicate JSON key")
    return d


def _read(data):
    return json.loads(data, object_pairs_hook=_unique_pairs)


def load_generated(index):
    """Accept manifest-bound v2 inventory only. Not the independent Git-tree gate."""
    index = Path(index)
    m = _read((index/"receipt.json").read_bytes())
    _expect(m.get("schema")==INDEX_SCHEMA and m.get("evidence")=="indexed_only", "unexpected manifest scheme/evidence")
    commit=m["source_commit"]
    _expect(HEX.fullmatch(commit) is not None, "manifest commit must be pinned")
    _expect([e["path"] for e in m["shards"]]==[f"shards/{i:02x}.jsonl" for i in range(256)], "noncanonical shards")
    aggregate=hashlib.sha256()
    rows=[]
    seen=set()
    for e in m["shards"]:
        data=(index/e["path"]).read_bytes()
        aggregate.update(data)
        _expect(_sha(data)==e["sha256"], f'digest mismatch: {e["path"]}')
        _expect(not data or data.endswith(b"\n"), f'bad JSONL boundary: {e["path"]}')
        lines=data.split(b"\n")[:-1]
        _expect(type(e["rows"]) is int and len(lines)==e["rows"], f'count mismatch: {e["path"]}')
        for line in lines:
            r=_read(line)
            path=r["path"]
            _expect(path not in seen, f"duplicate path: {path}")
            _expect(f"shards/{_sha(path.encode())[:2]}.jsonl"==e["path"], f"mis-sharded path: {path}")
            _expect(r["evidence"]=="indexed_only" and "source_commit" not in r, "unexpected row evidence")
            seen.add(path)
            rows.append({**r,"source_commit":commit})
    _expect(aggregate.hexdigest()==m["sha256"] and type(m["rows"]) is int and len(rows)==m["rows"],
            "aggregate receipt mismatch")
    return rows,{"source_commit":commit,"digest":m["sha256"],"coverage":"manifest-bound generated source metadata",
                 "fields":"all row values and JSON keys; path/title/declaration hints/other recorded fields"}


def _git(root, *args):
    return subprocess.check_output(["git","--no-replace-objects","-C",str(root),*args], timeout=60)


def load_tree(root, commit):
    """Credible scale fixture: from actual pinned Git path/mode/blob metadata; no hints."""
    _expect(HEX.fullmatch(commit) is not None,"tree commit must be pinned")
    _expect(_git(root,"rev-parse","--verify",commit+"^{commit}").decode().strip()==commit,"commit mismatch")
    blob=_git(root,"ls-tree","-r","-z","--full-tree",commit,"--",
              "research","packages/research","lean","docs/discovery/lean-bank")
    rows=[]
    for record in blob.split(b"\0")[:-1]:
        head,path=record.split(b"\t",1)
        mode,obj,oid=head.split()
        if mode not in (b"100644",b"100755") or obj!=b"blob":
            continue
        path=path.decode("utf-8")
        if path.endswith(".lean"):
            kind="lean_source"
        elif path.endswith((".md",".mdx")) and not path.startswith("docs/discovery/lean-bank/tools/"):
            kind="research_note"
        elif path.endswith((".receipt.json","-receipt.json","/receipt.json","/SHA256SUMS")):
            kind="receipt_locator"
        else:
            continue
        rows.append({"path":path,"git_blob":oid.decode(),"kind":kind,"source_commit":commit,"evidence":"indexed_only"})
    return rows,{"source_commit":commit,"digest":_sha(blob),"coverage":"pinned Git tree metadata only",
                 "fields":"path, blob ID, category, commit and evidence; no title/declaration/body tokens"}


def build(rows, meta, target):
    target=Path(target)
    tmp=target.with_name(target.name+".tmp-"+str(os.getpid()))
    _expect(not tmp.exists(),"temporary database already exists")
    try:
        with closing(sqlite3.connect(tmp)) as db, db:
            db.executescript('''
              CREATE TABLE meta (k TEXT PRIMARY KEY,v TEXT NOT NULL) WITHOUT ROWID;
              CREATE TABLE rowdata (id INTEGER PRIMARY KEY, json TEXT NOT NULL);
              CREATE TABLE posting (term TEXT NOT NULL,id INTEGER NOT NULL,PRIMARY KEY(term,id)) WITHOUT ROWID;
              CREATE TABLE freq (term TEXT PRIMARY KEY,count INTEGER NOT NULL) WITHOUT ROWID;
            ''')
            metadata={**meta,"schema":DB_SCHEMA,"tokenizer":TOKENIZER,"rows":len(rows),"evidence":"indexed_only"}
            db.executemany("INSERT INTO meta VALUES(?,?)",[(k,json.dumps(v)) for k,v in metadata.items()])
            db.executemany("INSERT INTO rowdata VALUES (?,?)",
                           ((j,json.dumps(r,ensure_ascii=False)) for j,r in enumerate(rows)))
            db.executemany("INSERT INTO posting VALUES(?,?)",
                           ((term,j) for j,r in enumerate(rows) for term in sorted(rowterms(r))))
            db.execute("INSERT INTO freq SELECT term,count(*) FROM posting GROUP BY term")
            stats=db.execute("SELECT count(*),(SELECT coalesce(sum(count),0) FROM freq) FROM freq").fetchone()
        tmp.replace(target)
    finally:
        if tmp.exists():
            tmp.unlink()
    return {**metadata,"unique_terms":stats[0],"postings":stats[1],"sqlite_bytes":target.stat().st_size}


def open_db(path):
    db=sqlite3.connect(Path(path).resolve().as_uri()+"?mode=ro",uri=True)
    meta={k:json.loads(v) for k,v in db.execute("SELECT k,v FROM meta")}
    _expect(meta.get("schema")==DB_SCHEMA and meta.get("tokenizer")==TOKENIZER and meta.get("evidence")=="indexed_only",
            "wrong cache schema, tokenizer or evidence")
    return db,meta


def matching_ids(db, query):
    ts = tokens(query)
    _expect(ts and len(ts)<=64,"query must contain 1..64 distinct exact tokens")
    counts = {t:(db.execute("SELECT count FROM freq WHERE term=?",(t,)).fetchone() or [0])[0] for t in ts}
    anchor = min(ts,key=lambda t:(counts[t],t))
    if not counts[anchor]:
        return []
    # Visit only the shortest posting list; membership checks use primary-key lookups.
    rest=sorted(ts-{anchor},key=lambda t:(counts[t],t))
    rhs = "".join(" AND EXISTS(SELECT 1 FROM posting q WHERE q.term=? AND q.id=p.id)" for _ in rest)
    return [row[0] for row in db.execute("SELECT p.id FROM posting p WHERE p.term=?"+rhs+" ORDER BY p.id",
                                       [anchor,*rest])]


def search(db,query,limit):
    ids=matching_ids(db,query)
    return {"matches":len(ids),"results":[json.loads(db.execute("SELECT json FROM rowdata WHERE id=?",(i,)).fetchone()[0])
                                           for i in ids[:limit]]}


def scan(rows,query):
    wanted=tokens(query)
    _expect(wanted and len(wanted)<=64,"query must contain 1..64 distinct exact tokens")
    return [i for i,r in enumerate(rows) if wanted <= rowterms(r)]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    s=p.add_subparsers(dest="op",required=True)
    b=s.add_parser("build-index"); b.add_argument("index"); b.add_argument("db")
    t=s.add_parser("build-tree"); t.add_argument("root"); t.add_argument("commit"); t.add_argument("db")
    q=s.add_parser("query"); q.add_argument("db"); q.add_argument("query"); q.add_argument("--limit",type=int,default=20)
    q.add_argument("--expect-commit"); q.add_argument("--expect-digest")
    a=p.parse_args()
    try:
        if a.op=="build-index":
            report=build(*load_generated(a.index),a.db)
        elif a.op=="build-tree":
            report=build(*load_tree(a.root,a.commit),a.db)
        else:
            _expect(1<=a.limit<=1000,"limit must be 1..1000")
            db,meta=open_db(a.db)
            try:
                _expect(not a.expect_commit or a.expect_commit==meta["source_commit"], "cache commit mismatch")
                _expect(not a.expect_digest or a.expect_digest==meta["digest"], "cache digest mismatch")
                report={**search(db,a.query,a.limit),"coverage":meta}
            finally:
                db.close()
        print(json.dumps(report,ensure_ascii=False,sort_keys=True))
        return 0
    except (OSError,ValueError,KeyError,TypeError,sqlite3.Error,subprocess.SubprocessError) as e:
        print(json.dumps({"error":str(e)}),file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())
