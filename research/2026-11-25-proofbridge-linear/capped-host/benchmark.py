"""Compare clean rebuild of the exact crossing closure with checked import alone."""
from pathlib import Path
import argparse
import json, os, statistics, subprocess, tempfile, time

p=argparse.ArgumentParser()
p.add_argument("lean",type=Path)
p.add_argument("alex_deps",type=Path)
a=p.parse_args()
lean=a.lean.resolve(strict=True)
source=a.alex_deps.resolve(strict=True)
here=Path(__file__).resolve().parent
providers=["SamuelAlexanderResearch/"+n for n in ("BinaryAvoidance","PopulationCounting","InfiniteConservation")]
providers+=["CappedHostIntervals"]
consumer="CappedHostComponents.lean"
def run(dst, files):
    env=dict(os.environ,LEAN_PATH=str(dst))
    start=time.monotonic()
    for f in files:
        cmd=[str(lean),"-o",f+".olean",f+".lean"] if f!=consumer else [str(lean),f]
        subprocess.run(cmd,cwd=dst,env=env,capture_output=True,text=True,timeout=120,check=True)
    return time.monotonic()-start
cold=[]; warm=[]
for _ in range(3):
    with tempfile.TemporaryDirectory(prefix="pb_alex_microbench_") as work:
        d=Path(work)
        for f in [n+".lean" for n in providers]+[consumer]:
            dst=d/f
            dst.parent.mkdir(exist_ok=True)
            src=source/f
            dst.write_bytes(src.read_bytes())
        cold.append(run(d,[*providers,consumer]))
        warm.append(run(d,[consumer]))
detail=lambda t:{"seconds":[round(x,3) for x in t],"median_seconds":round(statistics.median(t),3)}
print(json.dumps({"schema":"commons.proofbridge.scoped_import_timing.v1","compiler":subprocess.check_output([str(lean),"--version"],text=True).strip(),"rebuild_and_consumer":detail(cold),"already_built_consumer":detail(warm),"median_ratio":round(statistics.median(cold)/statistics.median(warm),2),"limits":"seconds for this existing fixed closure only, not drafting, downloading dependencies, full-theorem proof search or queue wait"},indent=2))
