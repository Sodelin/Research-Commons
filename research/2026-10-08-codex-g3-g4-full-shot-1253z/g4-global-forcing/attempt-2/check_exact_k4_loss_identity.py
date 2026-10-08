"""Authenticate the original diagonal against an independent K4 expansion.

Fixed strict rational controls only.  No parameter search, target solver,
physical mixture, old-source import/pycache, or compiler activity.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import datetime
import hashlib
import json

SOURCE = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py"
SOURCE_SHA = "a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b"


def k4_subset_expansion(x, y, g):
    edges = tuple(combinations(range(4), 2))
    value = F(0)
    for bits in product((0, 1), repeat=6):
        term = F(0)
        for routes in product((0, 1), repeat=4):
            weight = g ** sum(routes) * (1-g) ** (4-sum(routes))
            for include, (a, b) in zip(bits, edges):
                if include:
                    weight *= (1-x if routes[a] else 1-y) if routes[a] == routes[b] else 0
            term += weight
        value += (-1) ** sum(bits) * term
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit("refusing to overwrite existing output")
    path = args.root / SOURCE
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise SystemExit("original source hash mismatch")
    scope = {"__name__": "captured_k4_control_eppf", "__file__": str(path)}
    exec(compile(raw, str(path), "exec"), scope)
    # Interior; finite minority arm; very rare arm; opposite heavy arm;
    # and explicit both-large-loss cases of the physical bound.
    fixtures = [(F(1,2), F(3,4), F(2,5)),
                (F(1,4), F(1)-F(3,8)*F(1,1000)/F(999,1000), F(1,1000)),
                (F(1,4), F(99999,100000), F(1,100000)),
                (F(99999,100000), F(1,4), F(99999,100000)),
                (F(1,100), F(999999,1000000), F(1,100)),
                (F(999999,1000000), F(1,100), F(99,100))]
    rows = []
    for x,y,g in fixtures:
        assert 0 < x < 1 and 0 < y < 1 and 0 < g < 1
        q=1-g; u=g*(1-x); v=q*(1-y); d=g*u+q*v
        b2,b3,b4 = [scope["diag"](n,x,y,g) for n in (2,3,4)]
        delta=b3-b2**3
        J=g*u**3+q*v**3-d**3
        polyF=u**4*(15-6*u/g+(u/g)**2)+v**4*(15-6*v/q+(v/q)**2)
        K=15*d**4-6*d**5+d**6
        subset = k4_subset_expansion(x,y,g)
        assert subset == b4
        assert b4-b2**6-4*delta == -16*J+polyF-K
        assert 0 <= polyF <= 15*J+122880*d**4
        assert 0 < K <= 15*d**4
        rows.append({"cell":[str(x),str(y),str(g)],"pair_loss":str(d),
                     "k4_subset_matches_original":True,"identity_matches":True,
                     "physical_bound_control":True,"J":str(J),
                     "large_loss_case": "u>8d" if u>8*d else "v>8d" if v>8*d else "both<=8d"})
    report={"schema":"g6-k4-exact-source-identity-controls-v1",
            "timestamp_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "source":{"path":SOURCE,"sha256":SOURCE_SHA},
            "arithmetic":"exact Fraction; 64 edge subsets x16 original route assignments per fixture",
            "rows":rows,"exact_controls":4*len(fixtures),
            "limits":"Fixed rational source controls; universal inequality is a separate hand proof. No ordinary word or full G4 forcing claim."}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open("x") as f:
        json.dump(report,f,indent=2); f.write("\n")
    print(json.dumps({"path":str(args.output),"sha256":hashlib.sha256(args.output.read_bytes()).hexdigest(),"exact_controls":report["exact_controls"],"cases":[r["large_loss_case"] for r in rows]}))


if __name__ == "__main__":
    main()
