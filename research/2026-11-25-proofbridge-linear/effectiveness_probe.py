"""Try new, parametrically varied exact integer targets off the original fixtures."""
import json
from pathlib import Path
import statistics
import sys
import tempfile
import time

import linear
import smt_rounded as route
import smt_witness

CASES=[(2,-10),(3,-2),(4,0),(5,1),(7,6),(11,20)]


def run(z3, lean):
    results=[]
    with tempfile.TemporaryDirectory(prefix="proofbridge_audit_") as path:
        d=Path(path)
        for g,b in CASES:
            def probe(bound, scale, label):
                goal={"schema":"commons.linear-int.goal.v1","variables":["x","y","z"],
                      "premises":[{"coeffs":[g,1,-2*g],"le":g*(b+1)-1},{"coeffs":[0,-1,0],"le":0}],
                      "target":{"coeffs":[1,0,-2],"le":bound}}
                raw=smt_witness.json_bytes(goal)
                p=d/f"{g}-{label}.json"
                p.write_bytes(raw)
                t=time.monotonic()
                r=route.run(p,linear.sha(raw),scale,z3,lean,d/f"{g}-{label}")
                return r,time.monotonic()-t
            no_scale,_=probe(b,g-1,"too_small_scale")
            valid,t=probe(b,g,"valid")
            false,_=probe(b-1,g*2,"false_claim")
            assert no_scale["status"]==false["status"]=="no_bounded_witness"
            assert valid["status"]=="kernel_checked_conditional"
            assert valid["verification"]["scale"]==g and valid["verification"]["target"]["le"]==b
            witness=[b,0,0]
            assert g*b <= g*(b+1)-1 and b > b-1
            results.append({"minimum_tested_scale":g,"target_bound":b,"status":valid["status"],
                            "scope":{"premises":valid["verification"]["premises"],"target":valid["verification"]["target"]},
                            "scale_cap_one_below":no_scale["status"],"stronger_claim":false["status"],
                            "exact_counterexample_to_stronger":witness,"solver_and_lean_seconds":round(t,3)})
    return {"schema":"commons.proofbridge.effectiveness_probe.v1","purpose":"new parametrically varied tests of the supported fragment, not a new mathematical proof or coverage estimate","results":results,
            "positive_replay_median_seconds":round(statistics.median(r["solver_and_lean_seconds"] for r in results),3)}


if __name__=="__main__":
    z,l=[Path(p).resolve(strict=True) for p in sys.argv[1:]]
    print(json.dumps(run(z,l),indent=2))
