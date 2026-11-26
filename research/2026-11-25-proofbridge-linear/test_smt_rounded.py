"""Run pinned Z3 > generated Lean > independent import checks on representative goals."""
import json
from pathlib import Path
import sys
import tempfile

import linear
import smt_rounded as route
import smt_witness


def goal(b, t):
    return {"schema":"commons.linear-int.goal.v1","variables":["x","y"],
            "premises":[{"coeffs":[2,1],"le":b},{"coeffs":[0,-1],"le":0}],
            "target":{"coeffs":[1,0],"le":t}}


def smoke(library, lean):
    with tempfile.TemporaryDirectory(prefix="pb_smt_scaled_") as tmp:
        root=Path(tmp)
        def run(name, g, scale):
            raw=smt_witness.json_bytes(g)
            path=root/(name+".json")
            path.write_bytes(raw)
            work=root/name
            ans=route.run(path,linear.sha(raw),scale,library,lean,work)
            assert work.exists() == (ans["status"]=="kernel_checked_conditional")
            return ans
        out={}
        for n,b,t in [("positive",3,1),("signed",-3,-2)]:
            unscaled=run(n+"_unscaled",goal(b,t),1)
            yes=run(n+"_checked",goal(b,t),2)
            no=run(n+"_overclaim",goal(b,t-1),8)
            assert yes["verification"]["scale"]==2 and yes["candidate"]["multipliers"]==[1,1]
            assert yes["verification"]["target"]==goal(b,t)["target"]
            assert unscaled["status"]==no["status"]=="no_bounded_witness"
            point=[t,0]
            assert 2*point[0]+point[1]<=b and -point[1]<=0 and point[0]>t-1
            out[n]={"unscaled":unscaled,"exact":yes,"overclaim":no,"counterexample":point}
        gold=Path(__file__).with_name("goldbach-budget.goal.json")
        b=gold.read_bytes()
        gold_pin="4732cd3b8e89c9d1c21f85d434ef86561fcc6d74ff7506c35a115557309fe963"
        # Source fixture bytes are independently pinned by the prior unscaled receipt.
        assert linear.sha(b)==gold_pin
        alt=route.run(gold,gold_pin,1,library,lean,root/"goldbach")
        assert alt["verification"]["scale"]==1 and alt["verification"]["target"]["le"]==-187
        out["goldbach_scale_one"]=alt
        return {"schema":"commons.proofbridge.smt_rounded_smoke.v1","cases":out}


if __name__=="__main__":
    print(json.dumps(smoke(*(Path(p).resolve(strict=True) for p in sys.argv[1:])),indent=2))
