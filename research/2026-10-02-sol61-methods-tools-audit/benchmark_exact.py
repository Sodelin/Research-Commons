"""Synthetic benchmark only. Run in fresh processes for each SymPy ground type."""
import hashlib, json, os, random, resource, statistics, sys, time
from pathlib import Path
import sympy as sp
from sympy.polys.matrices import DomainMatrix

root = Path(__file__).resolve().parent
rng = random.Random(20261002)
rows = [[rng.randrange(-10**8, 10**8) for _ in range(35)] for _ in range(35)]
manifest = json.dumps(rows, separators=(",", ":"))
M = sp.Matrix(rows)
D = DomainMatrix.from_Matrix(M).convert_to(sp.ZZ)
results = {"input_class": "synthetic 35x35 integer matrix", "input_sha256": hashlib.sha256(manifest.encode()).hexdigest(),
           "sympy_version": sp.__version__, "ground_types": os.environ.get("SYMPY_GROUND_TYPES"),
           "internal_type": type(D.rep).__name__}
for name, fn in [("Matrix_bareiss", lambda: M.det(method="bareiss")), ("DomainMatrix_det", D.det)]:
    times=[]; values=[]
    for _ in range(3):
        t=time.perf_counter(); val=fn(); times.append(time.perf_counter()-t); values.append(str(val))
    assert len(set(values))==1
    results[name]={"seconds":times, "median_seconds":statistics.median(times), "determinant_sha256":hashlib.sha256(values[0].encode()).hexdigest(), "determinant_digits":len(values[0])}
assert results["Matrix_bareiss"]["determinant_sha256"] == results["DomainMatrix_det"]["determinant_sha256"]
results["process_maxrss_kib"]=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
if os.environ.get("SYMPY_GROUND_TYPES")=="flint":
    import flint
    from flint import arb, ctx, fmpq
    ctx.prec=128
    ball=arb(2).sqrt(); lo=fmpq(141421356,100000000); hi=fmpq(141421357,100000000)
    results["flint_version"]=flint.__version__
    results["arb_smoke"]={"sqrt2_ball":str(ball),"bits":ctx.prec,"lower":"141421356/100000000","upper":"141421357/100000000", "exact_lower_square_less_than_2":lo*lo<2,"exact_upper_square_greater_than_2":hi*hi>2,"oracle_status":"Arb interval and rational calculations are external; separate Lean validates the rational bracket without trusting them"}
(root / ("benchmark-"+os.environ.get("SYMPY_GROUND_TYPES","default")+".json")).write_text(json.dumps(results,indent=2)+"\n")
print(json.dumps(results,indent=2))
