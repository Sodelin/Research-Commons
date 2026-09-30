#!/usr/bin/env python3
"""Exact finite-grid transfer witnesses; SciPy is an optional proposal source.

Probability inputs/budgets are integers or rational strings, never JSON floats.
The checker certifies arithmetic, not the supplied cover/moduli/IID assumptions.
"""
from __future__ import annotations

import argparse
import copy
import json
import math
from fractions import Fraction as F
from pathlib import Path


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (int, str, F)):
        raise ValueError("Use integers or rational strings, not floats/bools")
    return F(value)


def matrix(rows, nrows=None, ncols=None, probability=False):
    if not isinstance(rows, list) or not rows:
        raise ValueError("Matrix must be a nonempty list")
    out = [[rational(x) for x in row] for row in rows]
    width = len(out[0])
    if not width or any(len(row) != width for row in out):
        raise ValueError("Empty/ragged matrix")
    if nrows is not None and len(out) != nrows:
        raise ValueError("Wrong row count")
    if ncols is not None and width != ncols:
        raise ValueError("Wrong column count")
    if probability and any(any(x < 0 for x in row) or sum(row) != 1 for row in out):
        raise ValueError("Probability rows must be nonnegative and sum exactly to one")
    return out


def laws(spec):
    p = matrix(spec["P"], probability=True)
    q = matrix(spec["Q"], nrows=len(p), probability=True)
    return p, q


def string_matrix(rows):
    return [[str(x) for x in row] for row in rows]


def sampling_bounds(m, nx, ny, sampling):
    """Rational upper bound for the Hoeffding log/sqrt radius, no float proof."""
    n, denom = sampling["N"], sampling.get("radius_denominator", 10**6)
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError("N must be a positive integer fixed before sampling")
    if isinstance(denom, bool) or not isinstance(denom, int) or denom < 1:
        raise ValueError("radius_denominator must be a positive integer")
    alpha = rational(sampling["alpha"])
    if not 0 < alpha < 1:
        raise ValueError("alpha must be strictly between zero and one")
    j = m * (nx + ny)
    ratio, c = 2 * j / alpha, 0
    while F(2**c) < ratio:
        c += 1
    # ceil(denom * sqrt(c/(2*n))), with only integer/rational comparisons.
    radicand = F(c * denom * denom, 2 * n)
    bnum = math.isqrt(radicand.numerator // radicand.denominator)
    if F(bnum * bnum) < radicand:
        bnum += 1
    b = F(bnum, denom)
    return {
        "N": n, "alpha": str(alpha), "confidence": str(1-alpha), "J": j,
        "power_of_two_exponent": c, "radius_denominator": denom,
        "coordinate_radius": str(b),
        "rho_P": str(min(F(1), F(nx, 2) * b)),
        "rho_Q": str(min(F(1), F(ny, 2) * b)),
    }


def budgets(spec, p, q):
    sampling = None
    if "sampling" in spec:
        if "rho_P" in spec or "rho_Q" in spec:
            raise ValueError("Use certified errors OR sampling-derived errors")
        sampling = sampling_bounds(len(p), len(p[0]), len(q[0]), spec["sampling"])
        n = sampling["N"]
        if any((n*x).denominator != 1 for row in p+q for x in row):
            raise ValueError("Sampling mode requires empirical probabilities with denominator dividing N")
        rp, rq = rational(sampling["rho_P"]), rational(sampling["rho_Q"])
    else:
        rp, rq = rational(spec.get("rho_P", 0)), rational(spec.get("rho_Q", 0))
    wp, wq = rational(spec.get("omega_P_r", 0)), rational(spec.get("omega_Q_r", 0))
    radius = rational(spec.get("radius", 0))
    if min(rp, rq, wp, wq, radius) < 0:
        raise ValueError("Errors, modulus envelopes and radius must be nonnegative")
    return rp, rq, wp, wq, sampling


def evaluate(spec, kernel, lam, v):
    p, q = laws(spec)
    m, nx, ny = len(p), len(p[0]), len(q[0])
    k = matrix(kernel, nrows=nx, ncols=ny, probability=True)
    ll = [rational(x) for x in lam]
    vv = matrix(v, nrows=m, ncols=ny)
    if len(ll) != m or min(ll) < 0 or sum(ll) != 1:
        raise ValueError("Dual lambda must be a simplex vector")
    if any(not 0 <= vv[i][y] <= ll[i] for i in range(m) for y in range(ny)):
        raise ValueError("Dual must satisfy 0 <= v[i,y] <= lambda[i] exactly")
    primal_rows = [sum(abs(sum(p[i][x]*k[x][y] for x in range(nx))-q[i][y])
                       for y in range(ny))/2 for i in range(m)]
    u = max(primal_rows)
    objective = sum(vv[i][y]*q[i][y] for i in range(m) for y in range(ny))
    objective -= sum(max(sum(p[i][x]*vv[i][y] for i in range(m))
                         for y in range(ny)) for x in range(nx))
    l = max(F(0), objective)
    if l > u:
        raise AssertionError("Feasible weak duality failed")
    rp, rq, wp, wq, sampling = budgets(spec, p, q)
    rho = rp+rq
    low, high = max(F(0), l-rho), min(F(1), u+rho+wp+wq)
    return {
        "grid_lower": str(l), "grid_upper": str(u), "grid_gap": str(u-l),
        "dual_objective": str(objective), "primal_row_errors": [str(z) for z in primal_rows],
        "rho_P": str(rp), "rho_Q": str(rq), "rho": str(rho),
        "omega_P_r": str(wp), "omega_Q_r": str(wq),
        "global_lower": str(low), "global_upper": str(high),
        "returned_kernel_uniform_TV_upper": str(high), "sampling": sampling,
    }


def rounded_simplex(values, max_denominator):
    entries = [F(str(float(x))).limit_denominator(max_denominator)
               if math.isfinite(float(x)) and x > 0 else F(0) for x in values]
    total = sum(entries)
    return [x/total for x in entries] if total else [F(1, len(entries))]*len(entries)


def proposals(p, q, max_denominator, use_scipy=True):
    """Return repaired feasible witnesses, never the solver's objective value."""
    m, nx, ny = len(p), len(p[0]), len(q[0])
    k = [[F(1, ny)]*ny for _ in range(nx)]
    lam, v = [F(1, m)]*m, [[F(0)]*ny for _ in range(m)]
    status = {"primal": "default", "dual": "default"}
    if not use_scipy:
        return k, lam, v, status
    try:
        from scipy.optimize import linprog
        nk, nt = nx*ny, m*ny
        size, dindex = nk+nt+1, nk+nt
        c = [0.0]*size
        c[dindex] = 1.0
        aub, bub = [], []
        for i in range(m):
            for y in range(ny):
                for sign in (1, -1):
                    row = [0.0]*size
                    for x in range(nx):
                        row[x*ny+y] = sign*float(p[i][x])
                    row[nk+i*ny+y] = -1.0
                    aub.append(row)
                    bub.append(sign*float(q[i][y]))
            row = [0.0]*size
            for y in range(ny):
                row[nk+i*ny+y] = 0.5
            row[dindex] = -1.0
            aub.append(row)
            bub.append(0.0)
        aeq = []
        for x in range(nx):
            row = [0.0]*size
            for y in range(ny):
                row[x*ny+y] = 1.0
            aeq.append(row)
        res = linprog(c, A_ub=aub, b_ub=bub, A_eq=aeq, b_eq=[1.0]*nx,
                      bounds=[(0, None)]*dindex+[(0, 1)], method="highs")
        if res.success and res.x is not None:
            k = [rounded_simplex(res.x[x*ny:(x+1)*ny], max_denominator) for x in range(nx)]
            status["primal"] = "scipy-proposal-rationally-repaired"
        # Separate dual LP: z[x] >= sum_i p[i,x]*v[i,y], v[i,y] <= lambda[i].
        zoffset, size = m+m*ny, m+m*ny+nx
        c = [0.0]*size
        for i in range(m):
            for y in range(ny):
                c[m+i*ny+y] = -float(q[i][y])
        for x in range(nx):
            c[zoffset+x] = 1.0
        aub, bub = [], []
        for i in range(m):
            for y in range(ny):
                row = [0.0]*size
                row[m+i*ny+y], row[i] = 1.0, -1.0
                aub.append(row)
                bub.append(0.0)
        for x in range(nx):
            for y in range(ny):
                row = [0.0]*size
                for i in range(m):
                    row[m+i*ny+y] = float(p[i][x])
                row[zoffset+x] = -1.0
                aub.append(row)
                bub.append(0.0)
        res = linprog(c, A_ub=aub, b_ub=bub, A_eq=[[1.0]*m+[0.0]*(size-m)],
                      b_eq=[1.0], bounds=(0, None), method="highs")
        if res.success and res.x is not None:
            lam = rounded_simplex(res.x[:m], max_denominator)
            v = []
            for i in range(m):
                row = []
                for y in range(ny):
                    ratio = float(res.x[m+i*ny+y]/res.x[i]) if res.x[i] > 0 else 0.0
                    ratio = min(1.0, max(0.0, ratio)) if math.isfinite(ratio) else 0.0
                    row.append(lam[i]*F(str(ratio)).limit_denominator(max_denominator))
                v.append(row)
            status["dual"] = "scipy-proposal-rationally-repaired"
    except Exception as exc:
        status["proposal_error"] = type(exc).__name__
    return k, lam, v, status


def make_certificate(spec, use_scipy=True, max_denominator=10**6, witness=None):
    if isinstance(max_denominator, bool) or not isinstance(max_denominator, int) or max_denominator < 1:
        raise ValueError("max_denominator must be a positive integer")
    p, q = laws(spec)
    budgets(spec, p, q)  # Validate declared bounds even if proposal generation fails.
    if witness is None:
        k, lam, v, status = proposals(p, q, max_denominator, use_scipy)
    else:
        k, lam, v = witness
        status = {"primal": "supplied-witness", "dual": "supplied-witness"}
    result = {
        "format": "compact-transfer-certificate-v1", "input": copy.deepcopy(spec),
        "kernel": string_matrix(k), "dual": {"lambda": [str(x) for x in lam], "v": string_matrix(v)},
        "proposal_status": status,
        "certificate": evaluate(spec, k, lam, v),
        "unverified_premises": ["declared finite grid r-covers the entire parameter class",
                                "supplied TV modulus envelopes hold for every distance <= r",
                                "certified law-error bounds or fixed-stage within-law IID sampling"],
    }
    verify_certificate(result)
    return result


def verify_certificate(record):
    if record.get("format") != "compact-transfer-certificate-v1":
        raise ValueError("Unknown certificate format")
    checked = evaluate(record["input"], record["kernel"], record["dual"]["lambda"], record["dual"]["v"])
    if checked != record["certificate"]:
        raise ValueError("Claimed certificate differs from exact recomputation")
    return checked


def fixture_run(use_scipy=True):
    identity = {"P": [[1, 0], [0, 1]], "Q": [[1, 0], [0, 1]],
                "scope": {"Theta": "{0,1}, discrete metric", "grid": [0, 1], "radius": "0",
                          "true_laws": "Supplied tables are exact; source and target both reveal theta.",
                          "validation_reference": "compact-certificate.md section 5: identity control"}}
    opposing = {"P": [[1], [1]], "Q": [[1, 0], [0, 1]],
                "scope": {"Theta": "{0,1}, discrete metric", "grid": [0, 1], "radius": "0",
                          "true_laws": "Supplied tables are exact; source is uninformative, target reveals theta.",
                          "validation_reference": "compact-certificate.md section 5: opposing-target control"}}
    approximate = {"P": [[1], [1]], "Q": [["3/8", "5/8"], ["5/8", "3/8"]],
                   "rho_P": 0, "rho_Q": "1/8", "omega_P_r": 0,
                   "omega_Q_r": "1/4", "radius": "1/4",
                   "scope": {"Theta": "[0,1] with ordinary distance", "grid": ["1/4", "3/4"],
                             "true_P_theta": "(1)", "true_Q_theta": "(theta,1-theta)",
                             "cover_proof": "Each point of [0,1] is within 1/4 of a grid point.",
                             "modulus_proof": "TV(Q_theta,Q_phi)=abs(theta-phi); source TV is zero.",
                             "law_error_proof": "Each estimated target differs from its grid law by TV 1/8.",
                             "validation_reference": "compact-certificate.md section 5: continuous-cover control"}}
    joint_errors = {"P": [["5/8", "3/8"], ["3/8", "5/8"]],
                   "Q": [["7/8", "1/8"], ["1/8", "7/8"]], "rho_P": "1/8", "rho_Q": "1/8",
                   "scope": {"Theta": "{0,1}, discrete metric", "grid": [0, 1], "radius": "0",
                             "true_P": [["1/2", "1/2"], ["1/2", "1/2"]],
                             "true_Q": [[1, 0], [0, 1]],
                             "law_error_proof": "Each source and each target law has exact TV error 1/8.",
                             "validation_reference": "compact-certificate.md section 5: both-law-error control"}}
    cases = [
        ("identity", identity, ([[1, 0], [0, 1]], [F(1, 2)]*2, [[0, 0], [0, 0]]), ("0", "0")),
        ("uninformative-opposing", opposing, ([[F(1, 2)]*2], [F(1, 2)]*2,
          [[F(1, 2), 0], [0, F(1, 2)]]), ("1/2", "1/2")),
        ("sampling-error-and-continuous-cover", approximate, ([[F(1, 2)]*2], [F(1, 2)]*2,
          [[0, F(1, 2)], [F(1, 2), 0]]), ("0", "1/2")),
        ("both-law-errors-sharp", joint_errors, ([[1, 0], [0, 1]], [F(1, 2)]*2,
          [[F(1, 2), 0], [0, F(1, 2)]]), ("0", "1/2")),
    ]
    results = []
    for name, spec, witness, expected in cases:
        exact = make_certificate(spec, witness=witness)
        interval = exact["certificate"]
        assert (interval["global_lower"], interval["global_upper"]) == expected
        automatic = make_certificate(spec, use_scipy=use_scipy)
        if use_scipy and all(automatic["proposal_status"].get(z, "").startswith("scipy") for z in ("primal", "dual")):
            assert automatic["certificate"]["grid_gap"] == "0", name
        results.append({"name": name, "exact_witness": exact, "automatic": automatic})
    sampling = copy.deepcopy(opposing)
    sampling["sampling"] = {"N": 10**6, "alpha": "1/20", "radius_denominator": 10**6}
    sampling["scope"]["sampling_status"] = "Arithmetic control of declared empirical rows; no sampler was run. Confidence interpretation requires the stated within-law IID premise."
    confidence = make_certificate(sampling, witness=cases[1][2])
    cb = confidence["certificate"]["sampling"]
    assert (cb["J"], cb["power_of_two_exponent"], cb["coordinate_radius"]) == (6, 8, "1/500")
    assert (confidence["certificate"]["global_lower"], confidence["certificate"]["global_upper"]) == ("497/1000", "503/1000")
    results.append({"name": "exact-rational-confidence-budget", "exact_witness": confidence})
    rejected = []
    for name, field, value in [
        ("nonstochastic-kernel", "kernel", [["1/3", "1/3"]]),
        ("invalid-dual-simplex", "lambda", ["1/3", "1/3"]),
        ("dual-exceeds-lambda", "v", [[1, 0], [0, 1]]),
        ("forged-zero-upper", "global_upper", "0"),
    ]:
        corrupt = copy.deepcopy(results[1]["exact_witness"])
        if field == "kernel":
            corrupt[field] = value
        elif field in ("lambda", "v"):
            corrupt["dual"][field] = value
        else:
            corrupt["certificate"][field] = value
        try:
            verify_certificate(corrupt)
        except (ValueError, AssertionError):
            rejected.append(name)
        else:
            raise AssertionError("Accepted malformed certificate: "+name)
    return {"status": "passed", "fixtures": results, "rejected_corruptions": rejected,
            "interpretation": "Analytic exact controls and exact witness checks; not an IID sampling experiment or empirical-domain validation."}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("input", nargs="?", help="JSON law/budget input or certificate with --verify")
    ap.add_argument("--verify", action="store_true")
    ap.add_argument("--fixtures", action="store_true")
    ap.add_argument("--no-scipy", action="store_true")
    ap.add_argument("--max-denominator", type=int, default=10**6)
    ap.add_argument("--output")
    args = ap.parse_args()
    if args.fixtures:
        out = fixture_run(not args.no_scipy)
    elif args.input:
        spec = json.loads(Path(args.input).read_text())
        out = {"status": "verified", "certificate": verify_certificate(spec)} if args.verify else make_certificate(spec, not args.no_scipy, args.max_denominator)
    else:
        ap.error("Supply input or --fixtures")
    payload = json.dumps(out, indent=2)+"\n"
    if args.output:
        Path(args.output).write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
