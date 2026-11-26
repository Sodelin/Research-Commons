"""Replay real prior SMT witnesses and join the exact typed Discovery rows."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import linear

HERE=Path(__file__).resolve().parent


def smoke(lean):
    smt=json.loads((HERE/"smt-rounded.receipt.json").read_bytes())["cases"]
    gold=linear.parse((HERE/"goldbach-budget.json").read_bytes())
    def wrap(c):
        return {"schema":"commons.proofbridge.rounded_batch_input.v1",
                "scale":c["verification"]["scale"],"certificate":c["candidate"]}
    entries={"budget":gold,"positive":wrap(smt["positive"]["exact"]),
             "signed":wrap(smt["signed"]["exact"]),
             "wrong":copy.deepcopy(wrap(smt["signed"]["exact"]))}
    entries["wrong"]["certificate"]["target"]["le"] -= 1
    def exec_(args,code=0):
        r=subprocess.run(args,text=True,capture_output=True,timeout=60)
        assert r.returncode==code,(args,r.stderr,r.stdout)
        return r
    with tempfile.TemporaryDirectory(prefix="pb_intake_test_") as dir:
        d=Path(dir)
        repo=d/"repo"
        repo.mkdir()
        def git(*a):
            return exec_(["git","-C",str(repo),*a]).stdout.strip()
        git("init","-q")
        rel="research/proofbridge-incoming/mixed.json"
        queue=repo/rel
        queue.parent.mkdir(parents=True)
        queue.write_text(json.dumps({"schema":"commons.proofbridge.certificate_records.v1",
                                    "records":[{"id":k,"certificate":v} for k,v in entries.items()]}))
        git("add",rel)
        git("-c","user.name=Replay Fixture","-c","user.email=replay@example.invalid","commit","-qm","Pinned typed fixtures")
        revision=git("rev-parse","HEAD")
        sources=d/"sources.json"
        sources.write_text(json.dumps({"schema":"commons.theorem_sources.v1","sources":[
            {"kind":"certificate_records","path":rel,"commit":revision,"blob":git("rev-parse",revision+":"+rel)}]}))
        intake=HERE/"theorem-intake.py"
        if not intake.is_file():
            intake=HERE.parents[1]/"docs/discovery/tools/theorem-intake.py"
        tool=[sys.executable,str(intake),"--repo",str(repo),"--sources",str(sources)]
        export=d/"export"
        exec_([*tool,"--export-ready",str(export)])
        files=sorted(p.name for p in (export/"inputs").iterdir())
        runner=[sys.executable,str(HERE/"manifest_runner.py")]
        manifest=d/"manifest.json"
        manifest.write_text(exec_([*runner,"make",str(export/"inputs"),*files]).stdout)
        pin=linear.sha(manifest.read_bytes())
        out=d/"run"
        exec_([*runner,"run",str(export/"inputs"),str(manifest),pin,str(out),"--lean",str(lean),
               "--rounded","--discovery-jsonl"],1)
        results=out/"discovery-results.jsonl"
        join=[*tool,"--export-index",str(export/"index.json"),"--checker-results"]
        rows={r["original_id"]:r for r in map(json.loads,exec_([*join,str(results)]).stdout.splitlines())}
        final={key:val["imported_replay"]["result"]["status"] for key,val in rows.items()}
        assert final=={"budget":"kernel-checked-conditional","positive":"kernel-checked-conditional",
                       "signed":"kernel-checked-conditional","wrong":"not-verified"}
        assert all(val["authored_formal_status"] is None for val in rows.values())
        record=rows["signed"]["imported_replay"]["result"]
        cases={"scale":{**record,"scale":3},
               "source":{**record,"source_sha256":"0"*64},
               "intermediate":{**record,"intermediate_target":{"coeffs":[2,0],"le":-2}},
               "axioms":{**record,"consumer_axioms":["sorryAx"]},
               "result_kind":{**record,"schema":rows["budget"]["imported_replay"]["result"]["schema"]}}
        rejected={}
        for k,v in cases.items():
            file=d/(k+".jsonl")
            file.write_text(json.dumps(v)+"\n")
            r=exec_([*join,str(file)],2)
            assert not r.stdout and ("scope or hash mismatch" in r.stderr or "wrong checker result schema" in r.stderr),r.stderr
            rejected[k]=r.stderr.strip()
        return {"schema":"commons.proofbridge.rounded_discovery_smoke.v1","manifest_sha256":pin,
                "statuses":final,"authored_status_unchanged":True,"rejected":rejected,
                "scope":"fixture Git pins and production checkout-equivalent scripts; no hosted trigger"}


if __name__=="__main__":
    print(json.dumps(smoke(Path(sys.argv[1]).resolve(strict=True)),indent=2))
