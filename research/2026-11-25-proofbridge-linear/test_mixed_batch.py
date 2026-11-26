"""Replay two existing SMT witnesses beside an unchanged legacy certificate."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import linear
import manifest_runner as runner


def smoke(lean):
    here = Path(__file__).resolve().parent
    old = (here/"goldbach-budget.json").read_bytes()
    assert linear.sha(old)=="98e115ecaa9245a6662048c78a15db5929be523f97f9b18f7fd22dc7d0ffff3e"
    smt = json.loads((here/"smt-rounded.receipt.json").read_bytes())["cases"]
    with tempfile.TemporaryDirectory(prefix="pb_mixed_") as tmp:
        d=Path(tmp)
        source=d/"inputs"
        source.mkdir()
        (source/"00-legacy.json").write_bytes(old)
        for index,key in enumerate(("positive","signed"),start=1):
            actual=smt[key]["exact"]
            obj={"schema":runner.ROUND_SCHEMA,"scale":actual["verification"]["scale"],
                 "certificate":actual["candidate"]}
            (source/f"0{index}-{key}.json").write_text(json.dumps(obj)+"\n")
            if key=="signed":
                obj["certificate"]["target"]["le"] -= 1
                (source/"03-overclaim.json").write_text(json.dumps(obj)+"\n")
        names=[p.name for p in source.glob("*.json")]
        manifest=runner.make(source,names)
        path=d/"manifest.json"
        raw=(json.dumps(manifest,indent=2,sort_keys=True)+"\n").encode("ascii")
        path.write_bytes(raw)
        pin=linear.sha(raw)
        def run(name, flags, expected_exit):
            call=[sys.executable,str(here/"manifest_runner.py"),"run",str(source),str(path),pin,
                  str(d/name),"--lean",str(lean),*flags]
            proc=subprocess.run(call,text=True,capture_output=True,timeout=60)
            assert proc.returncode==expected_exit,(proc.stderr,proc.stdout)
            return list(map(json.loads,proc.stdout.splitlines()))
        first=run("first",["--jobs","2","--rounded","--discovery-jsonl"],0)
        second=run("second",["--start",str(first[-1]["next_index"]),"--rounded","--discovery-jsonl"],1)
        opt_out=run("opt-out",["--start","1","--jobs","1"],1)
        assert not first[-1]["complete"] and second[-1]["complete"]
        assert first[0]["proof"]["conclusion"]["le"]==-187
        assert first[1]["proof"]["target"]["le"]==1 and second[0]["proof"]["target"]["le"]==-2
        assert second[1]["status"]=="not_verified" and "invalid linear combination" in second[1]["diagnostic"]
        assert opt_out[0]["status"]=="not_verified" and "requires --rounded" in opt_out[0]["diagnostic"]
        assert first[-1]["rounded_omitted_from_discovery"]==1 and second[-1]["rounded_omitted_from_discovery"]==2
        assert len((d/"first/discovery-results.jsonl").read_text().splitlines())==1
        assert not (d/"second/discovery-results.jsonl").exists()
        for name,row in [("first",first[1]),("second",second[0])]:
            mod=d/name/row["artifact_dir"]
            assert all(linear.sha((mod/f).read_bytes())==h for f,h in row["proof"]["files_sha256"].items())
        return {"schema":"commons.proofbridge.mixed_batch_smoke.v1","manifest_sha256":pin,
                "first":first,"resumed":second,"rounded_opt_out":opt_out,
                "artifact_hashes_rechecked":True,"solver_used_during_replay":False}


if __name__=="__main__":
    print(json.dumps(smoke(Path(sys.argv[1]).resolve(strict=True)),indent=2))
