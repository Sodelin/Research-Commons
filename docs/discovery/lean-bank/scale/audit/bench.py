"""Local synthetic workload; no network, user data, imported modules or Lean."""
import hashlib, json, statistics, tempfile, time
from pathlib import Path

def bench(n=66015):
    groups=[bytearray() for _ in range(256)]
    paths=[]
    for i in range(n):
        path=f"research/packet-{i//100:04}/lean/M{i:06}.lean"
        key=int(hashlib.sha256(path.encode()).hexdigest()[:2],16)
        row={"path":path,"git_blob":hashlib.sha1(path.encode()).hexdigest(),
             "kind":"lean_source","title":f"M{i:06}.lean",
             "declaration_hints":[f"lemma_index_{i%3500}_part_{j}" for j in range(16)],
             "evidence":"indexed_only"}
        groups[key].extend((json.dumps(row,separators=(",",":"))+"\n").encode())
        paths.append((key,path))
    key,path=paths[n//2]
    hint="lemma_index_415_part_0"
    with tempfile.TemporaryDirectory() as t:
        files=[Path(t)/f"{i:02x}.jsonl" for i in range(256)]
        for f,x in zip(files,groups):f.write_bytes(x)
        def read(f):return (json.loads(x) for x in f.read_bytes().splitlines())
        def broad_lookup():
            return [r for f in files for r in read(f) if hint in r["declaration_hints"]]
        def exact_lookup():
            return [r for r in read(files[key]) if r["path"]==path]
        def build_posting():
            d={}
            for f in files:
                for r in read(f):
                    # Index representative one key per row; actual multi-term postings cost more.
                    d.setdefault(r["declaration_hints"][0],[]).append(r["path"])
            return d
        def measure(f,k):
            durations=[]
            for _ in range(k):
                now=time.perf_counter(); result=f(); durations.append((time.perf_counter()-now)*1000)
            return round(statistics.median(durations),6),result
        broad,hits=measure(broad_lookup,5)
        exact,match=measure(exact_lookup,31)
        build,post=measure(build_posting,3)
        warm,cached=measure(lambda:post.get(hint,[]),1001)
        assert len(match)==1 and [r["path"] for r in hits]==cached
        print(json.dumps({"kind":"synthetic local warmed workload, not production SLA","rows":n,
                          "all_shards_bytes":sum(map(len,groups)),"one_shard_bytes":len(groups[key]),"hits":len(hits),
                          "median_ms":{"broad_shard_scan":broad,"exact_one_shard":exact,
                                       "one_term_postings_build":build,"warm_one_term_lookup":warm}},indent=2))
if __name__=="__main__":bench()
