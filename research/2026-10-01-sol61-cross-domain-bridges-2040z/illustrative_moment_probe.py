"""Exact source-model illustrations, not model fitting or an empirical experiment.

Source: Eriksson, Cownden & Strimling (2017), equations 1--5.
The emission/probe assumptions are additional and are stated in REPORT.md.
Only standard-library rational arithmetic is used. No original author code.
"""
from fractions import Fraction as F
from itertools import product
import hashlib
import json
from pathlib import Path


def update(x, observed, kind, gamma=F(1, 2)):
    def inc(y):
        if kind == "C":
            return gamma * y * (1-y)
        if kind == "N":
            return gamma * (1-y)
        if kind == "A":
            return gamma * (1-y)**2
        raise ValueError(kind)
    return x + inc(x) if observed else x-inc(1-x)


def mean_after(distribution, word, kind, gamma=F(1, 2)):
    out = F(0)
    for initial, weight in distribution:
        x = initial
        for observed in word:
            x = update(x, observed, kind, gamma)
        out += weight*x
    return out


def moment(distribution, degree):
    return sum((weight*x**degree for x, weight in distribution), F(0))


def frozen_emission_law(distribution, count):
    """Joint conditionally iid Bernoulli emissions with x not updated."""
    return {
        bits: sum((weight*x**sum(bits)*(1-x)**(count-sum(bits))
                   for x, weight in distribution), F(0))
        for bits in product((0, 1), repeat=count)
    }


def add(a, b):
    c = [F(0)]*max(len(a), len(b))
    for i, value in enumerate(a):
        c[i] += value
    for i, value in enumerate(b):
        c[i] += value
    return trim(c)


def trim(c):
    while len(c)>1 and c[-1]==0:
        c.pop()
    return c


def mult(a, b):
    c = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i+j] += x*y
    return trim(c)


def scale(a, f):
    return trim([f*x for x in a])


def update_poly(p, observed, kind, gamma):
    one_minus = add([F(1)], scale(p, -1))
    if kind == "C":
        inc = scale(mult(p, one_minus), gamma)
        return add(p, inc if observed else scale(inc, -1))
    if kind == "N":
        return add(p, scale(one_minus, gamma)) if observed else scale(p, 1-gamma)
    if kind == "A":
        return add(p, scale(mult(one_minus, one_minus), gamma)) if observed else add(p, scale(mult(p, p), -gamma))
    raise ValueError(kind)


def evaluate_poly(p, x):
    return sum((c*x**i for i, c in enumerate(p)), F(0))


def run():
    hom = [(F(1, 2), F(1))]
    het = [(F(1, 4), F(1, 2)), (F(3, 4), F(1, 2))]
    assert frozen_emission_law(hom, 1) == frozen_emission_law(het, 1)
    assert moment(hom, 1) == moment(het, 1) == F(1, 2)
    assert moment(hom, 2) == F(1, 4)
    assert moment(het, 2) == F(5, 16)
    assert frozen_emission_law(hom, 2) != frozen_emission_law(het, 2)
    expected = {"C":(F(5,8),F(19,32)), "N":(F(3,4),F(3,4)), "A":(F(5,8),F(21,32))}
    for kind, pair in expected.items():
        assert (mean_after(hom, (1,), kind), mean_after(het, (1,), kind)) == pair
    for distribution in (hom, het):
        mu, m2 = moment(distribution, 1), moment(distribution, 2)
        g = F(1, 2)
        formulas = {
            ("C",1):mu+g*(mu-m2), ("C",0):mu-g*(mu-m2),
            ("N",1):mu+g*(1-mu), ("N",0):(1-g)*mu,
            ("A",1):mu+g*(1-2*mu+m2), ("A",0):mu-g*m2,
        }
        for (kind, observed), prediction in formulas.items():
            assert mean_after(distribution, (observed,), kind) == prediction
    assert mean_after(hom,(1,),"C") == mean_after(hom,(1,),"A") == F(5,8)
    assert mean_after(hom,(0,),"C") == mean_after(hom,(0,),"A") == F(3,8)
    assert mean_after(hom,(1,1),"C") == F(95,128)
    assert mean_after(hom,(1,1),"A") == F(89,128)
    assert mean_after(hom,(1,1),"C")-mean_after(hom,(1,1),"A") == F(3,64)
    # Full enumeration only corroborates the algebraic composition argument.
    checked = 0
    for g in (F(1,4),F(1,2),F(3,4),F(1)):
        for h in range(1,5):
            for word in product((0,1), repeat=h):
                for kind in ("C","N","A"):
                    p = [F(0), F(1)]
                    for observed in word:
                        p = update_poly(p, observed, kind, g)
                    assert len(p)-1 == 2**h if kind != "N" else len(p)-1 <= 1
                    for x in (F(1,8),F(1,4),F(1,2),F(3,4),F(7,8)):
                        y = x
                        for observed in word:
                            y = update(y, observed, kind, g)
                        assert evaluate_poly(p,x)==y
                        assert 0<=y<=1
                        checked += 1
    return {
        "status":"PASS", "author":"GPT-6.1 Sol", "source":"10.1038/s41598-017-17826-9 equations 1--5",
        "scope":"Exact illustrative rational arithmetic; additional frozen-emission assumptions; no empirical validation, historical novelty, or full inference engine",
        "baseline_single_emission":"Both distributions are Bernoulli(1/2)",
        "latent_distributions":{"homogeneous":[["1/2","1"]],"heterogeneous":[["1/4","1/2"],["3/4","1/2"]]},
        "one_B_predictions":{k:list(map(str,v)) for k,v in expected.items()},
        "two_B_C_vs_A_homogeneous":["95/128","89/128"],
        "frozen_second_moments":["1/4","5/16"],
        "polynomial_point_checks":checked,
        "tested_horizons":[1,2,3,4],
        "tested_gamma":["1/4","1/2","3/4","1"],
        "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


if __name__ == "__main__":
    result=run()
    Path(__file__).with_name("illustrative-checks.json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
