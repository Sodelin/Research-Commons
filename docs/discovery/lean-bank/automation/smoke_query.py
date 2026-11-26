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
    report=json.loads(subprocess.check_output(["node","docs/discovery/tools/query.mjs","--lean-bank",query,"--layer","commons_git_source","--limit","200","--generated-index",str(a.index)],text=True,timeout=90))
    matches=[r for r in report["results"] if r["path"]==path and decl in r["declaration_hints"]]
    if len(matches)!=1 or matches[0]["source_commit"]!=m["source_commit"] or matches[0]["evidence"]!="indexed_only":
        raise SystemExit(f"wrong Discovery readback for {path}")
    checks.append({"query":query,"path":path,"decl_hint":decl,"git_blob":matches[0]["git_blob"]})
out={"schema":"commons.discovery.query-smoke.v1","source_commit":m["source_commit"],"index_sha256":m["sha256"],"checks":checks}
provider_path=a.index/"provider-observation.json"
if provider_path.is_file():
    providers=json.loads(provider_path.read_text())["providers"]
    p0=providers.get("lean4_core_selected",{})
    layer="external_live_source" if p0.get("status")=="passed" else "external_source_only"
    data=json.loads(subprocess.check_output(["node","docs/discovery/tools/query.mjs","--lean-bank","Init Prelude","--layer",layer,"--limit","200","--generated-index",str(a.index)],text=True,timeout=90))
    entries=[r for r in data["results"] if r["repo"]=="leanprover/lean4" and r["path"]=="src/Init/Prelude.lean"]
    if len(entries)!=1 or entries[0]["commit"]!="819816b2e0a3bf405af45ae5c7af2491d8f5bee6" or entries[0]["evidence"]!="source_path_only":
        raise SystemExit("wrong approved provider Discovery readback")
    out["external_provider_smoke"]={"layer":layer,"repo":entries[0]["repo"],"commit":entries[0]["commit"],
        "path":entries[0]["path"],"git_blob":entries[0]["sha"],"evidence":"source_path_only"}
catalog=json.loads(Path("docs/discovery/lean-bank/external/providers.json").read_text())
if "lean4_init_std" in catalog:
    report=json.loads(subprocess.check_output(["node","docs/discovery/tools/query.mjs","--lean-bank","Array BinSearch","--layer","external_source_only","--limit","200","--generated-index",str(a.index)],text=True,timeout=90))
    rows=[x for x in report["results"] if x["repo"]=="leanprover/lean4"
           and x["commit"]=="819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
           and x["path"]=="src/Init/Data/Array/BinSearch.lean"]
    if len(rows)!=1 or rows[0]["sha"]!="17d037bc1004a9b0ad3026bf64acc34fb6224528" or rows[0]["evidence"]!="source_path_only":
        raise SystemExit("scaled provider snapshot search readback mismatch")
    out["external_prefix_smoke"]={"repo":rows[0]["repo"],"commit":rows[0]["commit"],"path":rows[0]["path"],
        "git_blob":rows[0]["sha"],"evidence":"source_path_only"}
if "mathlib_combinatorics_numbertheory" in catalog:
    report=json.loads(subprocess.check_output(["node","docs/discovery/tools/query.mjs","--lean-bank","SimpleGraph Connectivity Subgraph","--layer","external_source_only","--limit","200","--generated-index",str(a.index)],text=True,timeout=90))
    rows=[x for x in report["results"] if x["repo"]=="leanprover-community/mathlib4"
          and x["commit"]=="0df444a360eaa60ab8c11dca51a86af692955474"
          and x["path"]=="Mathlib/Combinatorics/SimpleGraph/Connectivity/Subgraph.lean"]
    if len(rows)!=1 or rows[0]["sha"]!="580506f2a193cf80ab180dae792de7cb9b5eb611" or rows[0]["evidence"]!="source_path_only":
        raise SystemExit("Mathlib scoped-provider search readback mismatch")
    out["mathlib_scope_smoke"]={"repo":rows[0]["repo"],"commit":rows[0]["commit"],"path":rows[0]["path"],
        "git_blob":rows[0]["sha"],"evidence":"source_path_only"}
(a.index/"query-smoke.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))
