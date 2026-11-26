"""Prove the ordinary Discovery CLI sees known committed Lean sources via this index."""
import argparse,json,subprocess
from pathlib import Path

p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--index",type=Path,required=True)
a=p.parse_args()
m=json.loads((a.index/"receipt.json").read_text())
checks=[]
for query,decl,path in [
 ("TriangleRun","exact_component","research/2026-11-25-proofbridge-linear/capped-host/zero-run/TriangleRun.lean"),
 ("ThueMorsePhaseAliasing","prefix_aliases_with_cofinal_separation","docs/discovery/lean-bank/thue/ThueMorsePhaseAliasing.lean"),
]:
    report=json.loads(subprocess.check_output(["node","docs/discovery/tools/query.mjs","--lean-bank",query,"--layer","commons_git_source","--limit","200"],text=True,timeout=90))
    matches=[r for r in report["results"] if r["path"]==path and decl in r["declaration_hints"]]
    if len(matches)!=1 or matches[0]["source_commit"]!=m["source_commit"] or matches[0]["evidence"]!="indexed_only":
        raise SystemExit(f"wrong Discovery readback for {path}")
    checks.append({"query":query,"path":path,"decl_hint":decl,"git_blob":matches[0]["git_blob"]})
out={"schema":"commons.discovery.query-smoke.v1","source_commit":m["source_commit"],"index_sha256":m["sha256"],"checks":checks}
(a.index/"query-smoke.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))
