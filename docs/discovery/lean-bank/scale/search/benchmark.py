"""Measured local pinned metadata benchmark; no upstream access."""
import json, platform, statistics, sqlite3, sys, time
from pathlib import Path
from fanout import build, load_tree, matching_ids, open_db, rowterms, scan, tokens

here = Path(__file__).resolve().parent
root = here.parent/"pb-liveslot"/"repo"
db_path = here/"scale.sqlite"
ref = "45d7d79bcadb456174914ca80329d32c2158d727"
t=time.perf_counter(); rows,meta=load_tree(root,ref); load_sec=time.perf_counter()-t
t=time.perf_counter(); info=build(rows,meta,db_path); build_sec=time.perf_counter()-t
t=time.perf_counter(); db,_=open_db(db_path); cache_open_sec=time.perf_counter()-t
t=time.perf_counter(); precalculated=[rowterms(r) for r in rows]; prep_sec=time.perf_counter()-t
queries=["research","Lean","root obstruction","TriangleRun","Riemann","year impossibletoken98977",
         "receipt","Capped","Goldbach","source commit"]
metrics=[]
for q in queries:
    t=time.perf_counter(); expected=scan(rows,q); scan_ms=(time.perf_counter()-t)*1000
    terms=tokens(q)
    t=time.perf_counter(); assert [i for i,s in enumerate(precalculated) if terms <= s]==expected
    pretoken_ms=(time.perf_counter()-t)*1000
    samples=[]
    for _ in range(7):
        t=time.perf_counter(); got=matching_ids(db,q); samples.append((time.perf_counter()-t)*1000)
        assert got==expected, q
    metrics.append({"query":q,"matches":len(expected),"retokenizing_scan_ms":round(scan_ms,3),
                    "pretokenized_scan_ms":round(pretoken_ms,3),"warm_postings_ms":round(statistics.median(samples),3)})
db.close()
print(json.dumps({**info,"load_ms":round(load_sec*1000,3),"build_ms":round(build_sec*1000,3),
                  "open_ms":round(cache_open_sec*1000,3),"scan_prepare_ms":round(prep_sec*1000,3),
                  "python":platform.python_version(),"sqlite":sqlite3.sqlite_version,"timing_note":
                  "one local run; warm SQLite medians of seven; query times materialize all match IDs (no display-row fetch)",
                  "queries":metrics},indent=2,sort_keys=True))
