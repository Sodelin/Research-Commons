"""Bounded exact source control for the fixed nonordinary target.

This is a cap-three arithmetic control, not an all-cap source search.
The authenticated original source is evaluated from its captured bytes.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import factorial
from pathlib import Path
import json
import types

ROOT = Path(__file__).resolve().parents[3]
SOURCE = "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py"
SOURCE_SHA = "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884"

def main():
    path = ROOT / SOURCE
    captured = path.read_bytes()
    actual = sha256(captured).hexdigest()
    assert actual == SOURCE_SHA
    fa = types.ModuleType("authenticated_original_forest_algebra")
    fa.__file__ = str(path)
    exec(compile(captured, str(path), "exec"), fa.__dict__)
    alg = fa.ForestAlgebra(3)
    a, x, y, g, r = F(3, 4), F(1, 2), F(1, 2), F(2, 3), F(1, 2)
    target = alg.mul(alg.mul(alg.edge(a), alg.bigon(x, y, g, "independent")), alg.edge(r))
    q = target[alg.index[(2, (0, 1))]]
    b3 = target[alg.index[(3, (0, 1, 2))]]
    assert q == F(13, 48)
    assert b3 == F(81, 4096)
    ordinary = alg.edge(q)
    rows = []
    row_tv = []
    for k in range(4):
        indices = [i for i, (arity, _) in enumerate(alg.coords) if arity == k]
        assert sum((target[i] for i in indices), F(0)) == 1
        assert min(target[i] for i in indices) >= 0
        tv = sum((abs(target[i] - ordinary[i]) for i in indices), F(0)) / 2
        row_tv.append(tv)
        rows.append({"arity": k, "row_tv_from_pair_matched_ordinary": str(tv),
                     "full_labelled_row": [{"forest": repr(alg.coords[i][1]),
                                           "target": str(target[i]),
                                           "ordinary": str(ordinary[i]),
                                           "difference": str(target[i] - ordinary[i])}
                                          for i in indices]})
    e3 = max(row_tv)
    assert e3 == F(5, 36864)
    assert e3 == F(3, 2) * abs(b3 - q**3)
    # Positive Taylor terms prove exp(4/3)>48/13 and hence H=-log(q)<4/3.
    lower_exp = sum((F(4, 3)**j / factorial(j) for j in range(5)), F(0))
    assert lower_exp > 1 / q
    D3 = F(9)
    eta_lower = (e3 / (D3 * F(4, 3)))**2
    assert eta_lower == F(25, 195689447424)
    receipt = {
        "status": "PASS", "scope": "Exact cap-three arithmetic only; no higher-cap pumping witness",
        "executed_source": {"path": SOURCE, "sha256": actual, "bytes": len(captured),
                            "loader": "captured-byte sha256/compile/exec, no pyc"},
        "own_source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "fixed_target": {"leading": str(a), "arm0": str(x), "arm1": str(y),
                         "gamma_arm0": str(g), "trailing": str(r)},
        "pair_survival": str(q), "three_root_survival": str(b3),
        "ordinary_three_root_survival": str(q**3), "full_cap_three_tv": str(e3),
        "exp_4_over_3_positive_partial_sum": str(lower_exp),
        "comparison_48_over_13": str(1/q), "hazard_upper_bound": "4/3",
        "inherited_D3": str(D3), "forced_strong_bare_cell_pair_loss_lower_bound": str(eta_lower),
        "rows": rows,
        "not_established": ["Exact witness at arbitrary cap", "Exact skeleton compression",
                            "Finite determination against unbounded rival sizes", "G4 master closure"]}
    print(json.dumps(receipt, indent=2) + "\n", end="")

if __name__ == "__main__":
    main()
