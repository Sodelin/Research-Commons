"""Exact labelled-forest test of an actual positive rare-source jet.

Captured inherited source buffers are authenticated before execution.  No
inherited files or pycache are touched.  This is a leading-order test, not an
exact positive return or a G4 counterexample.  Existing output is never replaced.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from functools import lru_cache
from math import comb
import argparse
import json
import sys
import time
import types
import sympy as sp

ROOT = Path(__file__).resolve().parents[4]
PROVIDERS = [
    ("forest", "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py",
     "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884"),
    ("eppf", "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-stopping/two-insertion/exact_source_defects.py",
     "a0c6b0aa8220cdbc246d2189d7c6f6e9aec7c0b6a5647dd071a27d7a1102e47b"),
    ("jet", "research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-global-forcing/attempt-2/exact_boundary_coin_jet.py",
     "bb4619b5d37cb272e812eef0d00835f01308fa21b37e81e4d1e859595b90e787"),
]


def captured(label, path, pin):
    raw = (ROOT / path).read_bytes()
    assert sha256(raw).hexdigest() == pin, path
    module = types.ModuleType("captured_rare_full_" + label)
    module.__file__ = str(ROOT / path)
    sys.modules[module.__name__] = module
    exec(compile(raw, str(ROOT / path), "exec"), module.__dict__)
    return module, {"path": path, "sha256": pin, "bytes": len(raw)}


def wire(value):
    return str(value)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cap", type=int, choices=(4, 5, 6), default=5)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), "refusing to overwrite evidence"
    started = time.monotonic()
    loaded = [captured(*p) for p in PROVIDERS]
    fa, ep, jp = [m for m, _ in loaded]
    Jet = jp.Jet
    t = Jet.variable()
    alg = fa.ForestAlgebra(args.cap)

    @lru_cache(None)
    def topology_factor(tree):
        labels = fa.leaves(tree)
        numbered = fa.relabel(tree, dict(zip(labels, range(len(labels)))))
        return fa.embedded_merger_law(len(labels), 1)[(numbered,)]

    def full_bare(x, y, g):
        result = []
        for n, forest in alg.coords:
            sizes = tuple(len(fa.leaves(tree)) for tree in forest)
            factor = F(1)
            for tree in forest:
                factor *= topology_factor(tree)
            result.append(ep.bare_partition(sizes, x, y, g) * factor)
        return tuple(result)

    def full_edge(x):
        return tuple(sum((c*x**e for e, c in fa.edge_polynomials(n)[forest].items()), F(0))
                     for n, forest in alg.coords)

    def mul(left, right):
        # The actual original graft table is used without quotient reduction.
        answer = [F(0)] * alg.dim
        for i, j, k in alg.table:
            if left[i] != 0 and right[j] != 0:
                answer[k] += left[i] * right[j]
        return tuple(answer)

    def body(a, x, y, g, r):
        return mul(mul(full_edge(a), full_bare(x, y, g)), full_edge(r))

    def coords(vector):
        singleton = lambda n: vector[alg.index[n, tuple(range(n))]]
        pairpair = fa.forest((fa.tree(0, 1), fa.tree(2, 3)))
        triple = fa.forest((fa.tree(fa.tree(0, 1), 2), 3))
        balanced = (fa.tree(fa.tree(0, 1), fa.tree(2, 3)),)
        combtree = (fa.tree(fa.tree(fa.tree(0, 1), 2), 3),)
        return (singleton(2), singleton(3), singleton(4),
                vector[alg.index[4, pairpair]] - 2*vector[alg.index[4, triple]],
                vector[alg.index[4, balanced]] - 2*vector[alg.index[4, combtree]])

    target = (F(3, 4), F(1, 2), F(1, 2), F(2, 3), F(1, 2))
    controls = 0
    for x, y, g in ((F(1, 2), F(1, 2), F(2, 3)),
                    (F(1, 4), F(5, 6), F(1, 5))):
        eppf_kernel = full_bare(x, y, g)
        original_kernel = alg.bigon(x, y, g, "independent")
        assert eppf_kernel == original_kernel
        controls += alg.dim
    target_kernel = body(*target)
    assert target_kernel == alg.mul(alg.mul(alg.edge(target[0]), alg.bigon(*target[1:4], "independent")), alg.edge(target[4]))
    controls += alg.dim

    a, x, y, g, r = sp.symbols("a x y g r")
    vv = lambda z: (2-3*z+z**3)/6
    b = [sum(sp.binomial(n,j)*g**j*(1-g)**(n-j)*x**comb(j,2)*y**comb(n-j,2)
             for j in range(n+1)) for n in (2,3,4)]
    c = 2*(g**2*(1-g)**2*(1-x)*(1-y)-g**3*(1-g)*vv(x)-g*(1-g)**3*vv(y))
    closed = sp.Matrix([a*r*b[0], a**3*r**3*b[1], a**6*r**6*b[2], a**6*r*c, a**6*(1-r)*c])
    subs = dict(zip((a,x,y,g,r), (sp.Rational(v.numerator,v.denominator) for v in target)))
    target_coords = coords(target_kernel)
    assert tuple(F(v) for v in closed.subs(subs)) == target_coords
    jac = closed.jacobian((a,x,y,g,r)).subs(subs)
    full_derivatives = []
    for parameter in range(5):
        parameters = list(target)
        parameters[parameter] = Jet.scalar(parameters[parameter]) + t
        derivative = tuple(Jet.cast(v).coefficients[1] for v in body(*parameters))
        full_derivatives.append(derivative)
        assert tuple(F(v) for v in jac[:, parameter]) == coords(derivative)
        controls += 5
    assert jac.det() != 0

    # One source tuple at all arities: 493 positive-Q4 cells and 19 negative-Q4
    # cells. Retuning z of the former cancels the C(n,3) fourth jet too.
    s = F(-4695, 31552)
    rare_jets = []
    cell_records = []
    for count, z0, slope in ((493, F(3,8), s), (19, F(9,8), F(0))):
        z = z0 + slope*t
        xx, gg, yy = F(1,4), t, 1-z*t/(1-t)
        beta = ep.diag(2, xx, yy, gg)
        bare = full_bare(xx, yy, gg)
        ordinary = full_edge(beta)
        difference = tuple(Jet.cast(v-w) for v,w in zip(bare,ordinary))
        assert all(all(v.coefficients[k] == 0 for k in range(4)) for v in difference)
        rare_jets.append(tuple(v.coefficients[4] for v in difference))
        controls += alg.dim*4
        cell_records.append({"count":count, "x":"1/4", "g":"t", "z0":str(z0),
                             "z_slope":str(slope), "y":"1-(z0+z_slope*t)*t/(1-t)",
                             "pair_beta_coefficients":[str(v) for v in beta.coefficients]})
    leading = tuple(493*v+19*w for v,w in zip(*rare_jets))
    assert all(leading[alg.index[n,tuple(range(n))]] == 0 for n in range(args.cap+1))
    # No third-order nonordinary term exists in either cell. Chronological
    # products of deviations start at degree eight; O(t) ordinary separators
    # affect this fourth-order coefficient only at degree five or above.
    perturbation = mul(mul(mul(full_edge(target[0]), leading), full_bare(*target[1:4])), full_edge(target[4]))
    delta_matrix = -jac.inv()*sp.Matrix(coords(perturbation))
    delta = tuple(F(v) for v in delta_matrix)
    correction = tuple(sum((delta[j]*full_derivatives[j][i] for j in range(5)),F(0))
                       for i in range(alg.dim))
    residual = tuple(v+w for v,w in zip(perturbation,correction))
    cap4_residual = [(n,repr(forest),str(v)) for (n,forest),v in zip(alg.coords,residual) if n<=4 and v]
    assert not cap4_residual, cap4_residual
    witnesses = [{"arity":n,"forest":repr(forest),"coefficient":str(v)}
                 for (n,forest),v in zip(alg.coords,residual) if v]
    report = {
        "status":"PASS", "scope":"Exact positive 512-cell rare-source fourth jet, full-cap4 local retuning, and actual labelled higher-forest residual",
        "own_source_sha256":sha256(Path(__file__).read_bytes()).hexdigest(),
        "executed_provider_bytes":[p for _,p in loaded],
        "arithmetic":"Fraction and captured exact Q[t]/(t^5) source ring; exact SymPy linear inverse",
        "sympy_version":sp.__version__, "cap":args.cap, "forest_coordinates":alg.dim,
        "source_binding_controls":controls,
        "target_parameters":[str(v) for v in target], "target_cap4_coords":[str(v) for v in target_coords],
        "actual_five_coord_jacobian":[[str(v) for v in jac.row(i)] for i in range(5)],
        "actual_five_coord_jacobian_det":str(jac.det()),
        "rare_source_cells":cell_records,
        "formal_source_admission":"Each cell and intervening E(1-t) is strict for sufficiently small positive t; finite 512-cell word; physical leading pad retuned to preserve target pair survival. Only a leading jet is tested.",
        "all_degree_diagonal_cancellation":"Cubic zero individually; fourth C(n,3) and C(n,4) coefficients cancel exactly with these counts/slopes; all-degree formula independently controlled in tangent V3 receipt",
        "full_cap4_retuning_coefficients_a_x_y_g_r":[str(v) for v in delta],
        "full_cap4_all_labelled_residuals_exactly_zero":True,
        "higher_labelled_nonzero_count":len(witnesses), "higher_labelled_witnesses":witnesses,
        "full_fourth_residual":[{"arity":n,"forest":repr(forest),"value":str(v)} for (n,forest),v in zip(alg.coords,residual)],
        "runtime_seconds":time.monotonic()-started,
        "claim_limits":["A nonzero fourth residual rules out the analytic local body-retuning branch for this declared prototype", "No exact return constructed", "No arbitrary source fibre obstruction", "No original rich-menu G4 resolution"]}
    with args.output.open("x") as stream:
        json.dump(report,stream,indent=2);stream.write("\n")
    print(json.dumps({k:report[k] for k in ("status","cap","forest_coordinates","source_binding_controls","actual_five_coord_jacobian_det","full_cap4_retuning_coefficients_a_x_y_g_r","higher_labelled_nonzero_count","runtime_seconds")},indent=2))


if __name__ == "__main__":
    main()
