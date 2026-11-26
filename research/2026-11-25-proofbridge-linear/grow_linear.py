"""Try dropping hypotheses and reconstruct replacements in bounded integer arithmetic."""
import argparse
import json
from pathlib import Path
import sys

import linear
import premise_handoff
import smt_rounded
import smt_witness


def grow(source, pin, library, lean, out, max_scale=4, budget=12):
    raw=premise_handoff.read(source,16384)
    linear.require(linear.sha(raw)==pin,"source certificate hash mismatch")
    c=linear.parse(raw)
    linear.require(1<=budget<=20 and 1<=max_scale<=8,"outside pilot limits")
    ids=[premise_handoff.identity(c,r) for r in c["premises"]]
    linear.require(len(ids)==len(set(ids)),"duplicate premise identities")
    linear.LEAN[:]=[str(lean.resolve(strict=True))]
    original=linear.checked(raw)
    out.mkdir(exist_ok=False)
    active=list(range(len(ids)))
    tried=[]
    checked=None
    while len(active)>1 and len(tried)<budget:
        changed=False
        for i in active:
            if len(tried)==budget:
                break
            keep=[j for j in active if j!=i]
            goal={**{k:c[k] for k in ("variables","target")},"schema":"commons.linear-int.goal.v1",
                  "premises":[c["premises"][j] for j in keep]}
            new=smt_witness.json_bytes(goal)
            p=out/f"attempt_{len(tried):03}.json"
            p.write_bytes(new)
            res=smt_rounded.run(p,linear.sha(new),max_scale,library,lean,p.with_suffix(""))
            tried.append({"dropped_id":ids[i],"retained_ids":[ids[j] for j in keep],"result":res})
            if res["status"]=="kernel_checked_conditional":
                v=res["verification"]
                linear.require(v["target"]==c["target"] and v["variables"]==c["variables"]
                               and v["premises"]==goal["premises"],"scope changed")
                active=keep
                checked=v
                changed=True
                break
        if not changed:
            break
    return {"schema":"commons.proofbridge.grow_linear.v1","source_sha256":pin,
            "original":original,"retained_ids":[ids[j] for j in active],
            "removed_ids":[ids[j] for j in range(len(ids)) if j not in active],
            "originally_nonzero_removed":[ids[j] for j,m in enumerate(c["multipliers"]) if m and j not in active],
            "stronger_checked":checked,"attempts":tried,"limitations":"greedy bounded search, not global logical minimality"}


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("certificate",type=Path);p.add_argument("sha256")
    for name in ("z3","lean","out"):
        p.add_argument(name,type=Path)
    a=p.parse_args()
    print(json.dumps(grow(a.certificate,a.sha256,a.z3,a.lean,a.out),indent=2))
