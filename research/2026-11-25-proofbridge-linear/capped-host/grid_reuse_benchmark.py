"""Pair fresh builds with warmed checked imports; exclude authoring time."""
import hashlib,json,os,statistics,subprocess,sys,tempfile,time
from pathlib import Path

lean=Path(sys.argv[1]).resolve(strict=True)
root=Path(__file__).resolve().parent
modules=["SamuelAlexanderResearch/"+s for s in ("BinaryAvoidance","PopulationCounting","InfiniteConservation")]
modules+=["CappedActualBags","CappedConnectedBags","CappedGridWalks"]
consumer="GridWalkConsumer.lean"
def run(cwd,args):
    env=dict(os.environ,LEAN_PATH=str(cwd))
    subprocess.run([str(lean),*args],cwd=cwd,env=env,check=True,capture_output=True,timeout=120)
cold=[]; reuse=[]
for _ in range(3):
    with tempfile.TemporaryDirectory(prefix="pb_grid_bench_") as t:
        d=Path(t)
        for name in [m+".lean" for m in modules]+[consumer]:
            p=d/name
            p.parent.mkdir(exist_ok=True)
            p.write_bytes((root/name).read_bytes())
        stamp=time.monotonic()
        for name in modules:
            run(d,["-o",name+".olean",name+".lean"])
        run(d,[consumer])
        cold.append(time.monotonic()-stamp)
        stamp=time.monotonic()
        run(d,[consumer])
        reuse.append(time.monotonic()-stamp)
def summary(arr):
    return {"seconds":[round(x,3) for x in arr],"median_seconds":round(statistics.median(arr),3)}
saved=statistics.median(cold)-statistics.median(reuse)
print(json.dumps({"schema":"commons.proofbridge.grid_reuse_timing.v1","compiler":
    subprocess.check_output([str(lean),"--version"],text=True).strip(),
    "providers":modules,"fresh_closure_and_consumer":summary(cold),"checked_import_only":summary(reuse),
    "median_rebuild_seconds_avoided_on_repeat":round(saved,3),
    "scope":"same Lean consumer and source bytes; excludes authoring, fetching, transfer and scheduling"},indent=2))
