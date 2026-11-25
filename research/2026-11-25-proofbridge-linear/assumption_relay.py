"""Check a stronger implication after deleting unused premises from a supplied proof."""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import linear

def canonical(c):
    return (json.dumps(c,sort_keys=True,separators=(",",":"))+"\n").encode("ascii")

def probe(raw):
    c=linear.parse(raw)
    before=linear.checked(raw)
    keep=[i for i,m in enumerate(c["multipliers"]) if m != 0]
    drop=[i+1 for i,m in enumerate(c["multipliers"]) if m == 0]
    if not drop:
        return {"status":"no_zero_weight_premise","original":before,
                "note":"This proof uses every premise; it does not show every premise is necessary."}
    reduced=copy.deepcopy(c)
    for field in ("premises","multipliers"):
        reduced[field]=[c[field][i] for i in keep]
    after=linear.checked(canonical(reduced))
    linear.require(after["variables"]==before["variables"] and
                   after["conclusion"]==before["conclusion"],"claim changed")
    return {"status":"checked_under_fewer_premises","removed_premises_1_based":drop,
            "original":before,"reduced":after,"reduced_certificate":reduced,
            "note":"Lean checked the unchanged conclusion after deleting these premises together."}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("certificate",type=Path)
    a=ap.parse_args()
    with a.certificate.open("rb") as f:
        value=probe(f.read(16385))
    print(json.dumps(value,indent=2))
    return 0

if __name__=="__main__":
    try:
        sys.exit(main())
    except (OSError,ValueError,subprocess.SubprocessError) as exc:
        sys.exit(str(exc))
