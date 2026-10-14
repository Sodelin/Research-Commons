#!/usr/bin/env python3
"""Own exact data check. Does not execute Lean or a native genealogy program."""
import argparse
import hashlib
import json
from fractions import Fraction
from math import comb, factorial, prod
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument("fixture_json", type=Path)
args = p.parse_args()
body = args.fixture_json.read_bytes()
assert hashlib.sha256(body).hexdigest() == \
    "7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba"
fixture = json.loads(body)
edges = {e["index"]: e for e in fixture["edges"]}
h = fixture["hybrids"][0]
assert [h["parent_0_edge"], h["parent_1_edge"]] == [3, 4]
assert Fraction(h["original_parent_1_probability"]) == Fraction(1, 3)
gamma = Fraction(h["original_parent_1_probability"])

def verify_path(path, leaf):
    node = fixture["root"]
    for e in path:
        assert edges[e]["source"] == node
        node = edges[e]["target"]
    assert node == fixture["leaves"][leaf]

atoms = []
for bit in [False, True]:
    arm = h["parent_1_edge"] if bit else h["parent_0_edge"]
    a = [0, 2, arm, 5]
    b = [0, 6]
    verify_path(a, "A")
    verify_path(b, "B")
    for e in a + b:
        if edges[e]["target"] == h["vertex"]:
            assert e == arm
    delta = [e for e in a if e not in b]
    assert delta == [2, arm, 5]
    survival = prod(Fraction(edges[e]["survival"]) for e in delta)
    assert survival == Fraction(1, 2)
    atoms.append((gamma if bit else 1 - gamma, survival))
assert sum(w for w, _ in atoms) == 1
print("PASS both original bits select their literal original arm; exact A/B paths and edge difference")
print("PASS bankwise whole-edge product is 1/2 under the unchanged physical fixture")

for k, expected, raw_expected in [(1, Fraction(1), Fraction(1)),
                                 (2, Fraction(1, 2), Fraction(1, 6)),
                                 (3, Fraction(1, 8), Fraction(1, 144))]:
    moment = sum(w * a ** comb(k, 2) for w, a in atoms)
    coefficient = Fraction(2**k, factorial(k + 1) * factorial(k))
    raw = coefficient * moment
    assert moment == expected and raw == raw_expected
    print(f"PASS k={k}; padded copies={4+k+1}; moment={moment}; raw={raw}")
print("DATA ONLY: no Lean elaboration, kernel/axiom audit, native full-table run or parser refinement")
