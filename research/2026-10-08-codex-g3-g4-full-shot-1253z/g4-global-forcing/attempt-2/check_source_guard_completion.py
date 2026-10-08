"""Exact source countercontrols to one proposed signed-cost completion.

Actual rational cells; exact rational bounds on each natural logarithm.
No approximate zero, parameter optimization, inherited-source mutation,
compiler or assertion of a complete ordinary return.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import sys
import types

SOURCE = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py"
SOURCE_SHA = "a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b"
JET_SHA = "bb4619b5d37cb272e812eef0d00835f01308fa21b37e81e4d1e859595b90e787"


def captured_module(path, expected, name):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit("source hash mismatch: " + str(path))
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(raw, str(path), "exec"), module.__dict__)
    return module


def log_bounds(value, count=8):
    """atanh expansion, two-sided exact rational tail bound."""
    if value <= 0:
        raise ValueError("log argument must be strictly positive")
    w = (value-1)/(value+1)
    partial = 2*sum((w**(2*k+1)/F(2*k+1) for k in range(count)), F(0))
    remainder = 2*abs(w)**(2*count+1)/(F(2*count+1)*(1-w*w))
    return partial-remainder, partial+remainder


def scaled_sum(bounds, coefficients):
    lower = upper = F(0)
    for (lo,hi), c in zip(bounds, coefficients):
        lower += c*(lo if c >= 0 else hi)
        upper += c*(hi if c >= 0 else lo)
    return lower,upper


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise SystemExit("refusing to overwrite existing output")
    source = captured_module(args.root/SOURCE, SOURCE_SHA, "source_guard_original_eppf")
    helper = captured_module(Path(__file__).with_name("exact_boundary_coin_jet.py"),
                             JET_SHA, "source_guard_frozen_jet")
    rows=[]
    for z,expected in [(F(1,4),F(-11499,20480)),(F(1),F(14421,20480))]:
        t=helper.Jet.variable(); x=helper.Jet.scalar(F(1,4)); g=t; y=1-z*t/(1-t)
        bs={n:source.diag(n,x,y,g) for n in (2,3,4)}
        f,_,_=source.scalars(x,y,g)
        G=(F(29,45)*bs[4].log()-F(20,9)*bs[3].log()
           +F(14,5)*bs[2].log()+F(16,3)*bs[2]**-36*f)
        assert G.coefficients[3] == 0
        assert G.coefficients[4] == expected
        # The polynomial family is only a derivation aid.  This is a literal
        # actual source tuple, with both arms and the coin strictly natural.
        small=F(1,1000); cell=(F(1,4),1-z*small/(1-small),small)
        assert all(0<p<1 for p in cell)
        b2,b3,b4=[source.diag(n,*cell) for n in (2,3,4)]
        f9,_,_=source.scalars(*cell)
        # G=(29D4+16D3)/45+(16/3)b2^-36 f9.
        logs=[log_bounds(p) for p in (b4,b3,b2)]
        lo,hi=scaled_sum(logs,(F(29,45),F(-20,9),F(14,5)))
        correction=F(16,3)*f9/b2**36
        lo+=correction; hi+=correction
        sign="POSITIVE" if lo>0 else "NEGATIVE" if hi<0 else "UNKNOWN"
        assert sign == ("POSITIVE" if expected>0 else "NEGATIVE")
        rows.append({"z":str(z),"strict_cell_x_y_g":[str(p) for p in cell],
                     "shared_tuple_all_arities":True,"mode":"INDEPENDENT current roots",
                     "G_jet_order_0_through_4":helper.wire(G),
                     "source_b2_b3_b4":[str(p) for p in (b2,b3,b4)],"source_f9":str(f9),
                     "log_bound_terms_per_argument":8,
                     "G_rational_interval":[str(lo),str(hi)],"certified_sign":sign})
    report={"schema":"actual-source-completed-diagonal-guard-countercontrols-v1",
            "timestamp_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "source":{"path":SOURCE,"sha256":SOURCE_SHA},"jet_sha256":JET_SHA,
            "formula":"G=(29D4+16D3)/45+(16/3)b2^(-36)f9",
            "arithmetic":"Fraction jets Q[t]/t^5 and exact Fraction two-sided atanh log bounds",
            "rows":rows,"exact_controls":8,
            "limits":"Refutes only a one-cell universal negative sign for this proposed completion. G is not additive in full words. These cells do not satisfy complete target equations; full G4 remains open."}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open("x") as f:
        json.dump(report,f,indent=2); f.write("\n")
    print(json.dumps({"path":str(args.output),"sha256":hashlib.sha256(args.output.read_bytes()).hexdigest(),
                      "signs":[r["certified_sign"] for r in rows],"exact_controls":report["exact_controls"]}))


if __name__ == "__main__":
    main()
