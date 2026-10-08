"""Exact two rational cubic-zero branches; no physical-zero/root claim.

Pins the saved truncated ring and inherited EPPF source.  No imports or
mutations in inherited paths; output is created exclusively.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
from fractions import Fraction as F

JET_SHA = "bb4619b5d37cb272e812eef0d00835f01308fa21b37e81e4d1e859595b90e787"
SOURCE_SHA = "a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b"
SOURCE = "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py"


def captured_module(path, expected):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit("captured module hash mismatch: " + str(path))
    scope = {"__name__": "captured_" + path.stem, "__file__": str(path)}
    # dataclasses resolves its own module via sys.modules.  Execute a real
    # isolated module, never importing the provider or creating its pycache.
    import types, sys
    module = types.ModuleType(scope["__name__"])
    module.__dict__.update(scope)
    sys.modules[module.__name__] = module
    exec(compile(raw, str(path), "exec"), module.__dict__)
    return module.__dict__


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[4])
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    if a.output.exists():
        raise SystemExit("refusing to overwrite existing output")
    helper = captured_module(Path(__file__).with_name("exact_boundary_coin_jet.py"), JET_SHA)
    source = captured_module(a.root / SOURCE, SOURCE_SHA)
    J, wire = helper["Jet"], helper["wire"]
    t = J.variable()
    rows = []
    for z in (F(3, 8), F(9, 8)):
        x, g, q = J.scalar(F(1, 4)), t, 1-t
        y = 1-z*t/q
        b = {n:source["diag"](n,x,y,g) for n in (2,3,4,6,7,9)}
        f,h,e = source["scalars"](x,y,g)
        X = b[2]**-36*f
        T = b[2]**-15*h
        U = b[2]**-21*(-h+2*e)
        D3 = b[3].log()-3*b[2].log()
        D4 = b[4].log()-4*b[3].log()+6*b[2].log()
        guard = F(29,45)*(b[4]/b[2]**6-1)-F(20,9)*(b[3]/b[2]**3-1)
        assert X.coefficients[3] == D3.coefficients[3] == 0
        rows.append({"z":str(z),"source":"x=1/4, g=t, y=1-z*t/(1-t)",
                     "strict_domain":"0<t<1/(1+z)",
                     "coefficients_order_0_through_4":{
                         "D3":wire(D3),"D4":wire(D4),"X":wire(X),"T":wire(T),"U":wire(U),
                         "T_minus_5_over_3_X":wire(T-F(5,3)*X),
                         "U_plus_5_over_3_X":wire(U+F(5,3)*X),
                         "inherited_diagonal_guard_J":wire(guard)}})
    report={"schema":"actual-rare-two-cubic-zero-jet-v1",
            "timestamp_utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "producer_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "jet_source_sha256":JET_SHA,"eppf_source":{"path":SOURCE,"sha256":SOURCE_SHA},
            "arithmetic":"exact Fraction ring Q[t]/(t^5)","rows":rows,
            "exact_controls":4,
            "claim_limits":"One cell per row, cubic coefficient zero only; full word and exact f-zero IFT are not executed or proved here. No G4 resolution."}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open("x") as stream:
        json.dump(report,stream,indent=2); stream.write("\n")
    print(json.dumps({"output":str(a.output),"sha256":hashlib.sha256(a.output.read_bytes()).hexdigest(),"rows":rows}))


if __name__ == "__main__":
    main()
