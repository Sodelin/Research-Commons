"""Two unrestricted integer implications and exact counterexamples to stronger targets."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import assumption_relay
import linear
import import_reduced as importer
import rounded_witness as route


def fixture(b, target):
    return {"schema":linear.SCHEMA,"variables":["x","y"],
            "premises":[{"coeffs":[2,1],"le":b},{"coeffs":[0,-1],"le":0}],
            "target":{"coeffs":[1,0],"le":target},"multipliers":[1,1]}


def holds(row, x):
    return sum(a*v for a,v in zip(row["coeffs"],x)) <= row["le"]


def smoke(lean):
    cases=[]
    with tempfile.TemporaryDirectory(prefix="pb_round_fixture_") as d:
        root=Path(d)
        for i,(b,t) in enumerate([(3,1),(-3,-2)]):
            c=fixture(b,t)
            raw=assumption_relay.canonical(c)
            pin=linear.sha(raw)
            ok=route.checked(raw,pin,2,lean,root/f"case{i}")
            rejected={}
            try:
                route.checked(raw,pin,1,lean,root/f"unscaled{i}")
            except ValueError as e:
                assert "invalid linear combination" in str(e) and not (root/f"unscaled{i}").exists()
                rejected["unscaled"]="coefficient_mismatch"
            else:
                raise AssertionError("unscaled combination accepted")
            stronger=fixture(b,t-1)
            bad=assumption_relay.canonical(stronger)
            point=[t,0]
            assert all(holds(p,point) for p in stronger["premises"]) and not holds(stronger["target"],point)
            try:
                route.checked(bad,linear.sha(bad),2,lean,root/f"stronger{i}")
            except ValueError as e:
                assert "invalid linear combination" in str(e) and not (root/f"stronger{i}").exists()
                rejected["stronger"]={"status":"failed_weighted_bound","target":stronger["target"],"counterexample":point}
            else:
                raise AssertionError("false stronger target accepted")
            weaker = {**c,"target":{"coeffs":[2,0],"le":2*(t+1)}}
            wrong = root/f"weaker{i}"
            wrong.mkdir()
            actual = root/f"case{i}"
            provider = next(actual.glob("PB_*.lean"))
            (wrong/provider.name).write_text(importer.provider(provider.stem,weaker),encoding="ascii")
            consumer = wrong/"ReuseOriginal.lean"
            consumer.write_bytes((actual/consumer.name).read_bytes())
            weak_axioms=importer.axioms(importer.invoke(lean,wrong,"-o",provider.stem+".olean",provider.name))
            try:
                importer.invoke(lean,wrong,consumer.name)
            except ValueError as e:
                assert "omega could not prove the goal" in str(e),str(e)
                rejected["weaker_provider"]={"provider_axioms":weak_axioms,"status":"rejected_by_lean"}
            else:
                raise AssertionError("weaker provider accepted")
            cases.append({"source":c,"receipt":ok,"controls":rejected})
    return {"schema":"commons.proofbridge.rounded_witness_smoke.v1","cases":cases}


if __name__=="__main__":
    print(json.dumps(smoke(Path(sys.argv[1]).resolve(strict=True)),indent=2))
