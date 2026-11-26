#!/usr/bin/env python3
"""Replay against exact previously retrieved Thue–Morse files; no network."""
import argparse, json, tempfile
from pathlib import Path
from closure import git_blob, plan, sha256

REPO="Sodelin/Work-on-Samuel-Alexander-Research-"
COMMIT="19544a4d7608c8cc0d5a1205605c0f38631ca05f"
VERSION="thue-height-prefix-v1"
EXPECTED_LOCAL={
    "Reuse": "f14d6eed2e964c6e40fee9450d69585dcfec51aaa8046cf33a42191f0442ceba",
    "PrefixCount": "26b737bc20fc6c68d30218ea4fdd482cd79d1ded3c087080ef458a7408abc79b",
}

def replay(root, output):
    manifest = {}
    for row in (root/"PROVIDER-MANIFEST.tsv").read_text().splitlines():
        if row.startswith("#") or not row.strip():
            continue
        rel, blob, digest = row.split("\t")
        m = rel[:-5].replace("/",".")
        data = (root/rel).read_bytes()
        assert git_blob(data) == blob and sha256(data) == digest, m
        manifest[m] = (rel, blob, data)
    assert len(manifest) == 9
    cfg = {
        "schema":"commons.lean-source-planner.v1", "version":VERSION,
        "toolchain":"lean-v4.33.1", "toolchain_module_prefixes":["Init","Lean","Std"],
        "targets":["PrefixCount"],
        "local_sources":{m:{"path":m+".lean","sha256":sha} for m,sha in EXPECTED_LOCAL.items()},
        "repositories":[{"repo":REPO,"commit":COMMIT,"source_prefix":"lean",
                         "module_prefixes":["SamuelAlexanderResearch"],
                         "blobs":{m:row[1] for m,row in manifest.items()}}],
    }
    def save(name,data):
        if output is not None:
            (output/name).write_text(json.dumps(data,indent=2,sort_keys=True)+"\n")
    if output is not None:
        output.mkdir(parents=True,exist_ok=True)
    save("thue-fixture-config.json",cfg)
    with tempfile.TemporaryDirectory() as tmp:
        store=Path(tmp)
        i=0
        while True:
            result=plan(cfg,store,root)
            assert result["compilability"]=="not_checked"
            if i == 0:
                save("thue-first-plan.json",result)
                assert result["blocking_modules"]==["SamuelAlexanderResearch.FullHeight"]
            if result["package_source_closure"]=="present":
                save("thue-complete-plan.json",result)
                break
            assert result["fetch_requests"],result
            for pending in result["fetch_requests"]:
                m=pending["module"]
                rel, blob, data=manifest[m]
                assert pending["repo"]==REPO and pending["ref"]==COMMIT
                assert pending["expected_git_blob"]==blob and pending["path"]=="lean/"+rel
                out=store/pending["staging_path"]
                assert out.is_relative_to(store) and not out.exists()
                out.parent.mkdir(parents=True,exist_ok=True)
                out.write_bytes(data)
                i+=1
        assert i==9
        assert sum(e["status"]=="local_source_present" for e in result["entries"].values())==2
        assert not result["blocking_modules"] and not result["cycles"] and not result["fetch_requests"]
        order=result["dependency_first_source_order"]
        for m in order:
            for imp in result["entries"][m]["imports"]:
                if imp in order:
                    assert order.index(imp)<order.index(m)
    print("PASS: first round 1 scoped fetch; 9 exact staged repo sources, 2 exact local sources, dependency-first closure present")
    print("Unresolved toolchain modules:", ", ".join(m for m,e in result["entries"].items() if e["status"]=="toolchain_dependency_unverified"))
    print("Compilability: not_checked by planner; prior Lean replay is a distinct artifact.")

if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture_root",type=Path)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    replay(args.fixture_root,args.output)
