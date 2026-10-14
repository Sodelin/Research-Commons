"""Exact diagnostic checks, NOT a physical G4 solver or master proof.
Standard-library rational arithmetic; no network, compiler, or repository access.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, factorial
import json

def trim(a: list[F]) -> list[F]:
    a = list(a)
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a

def mul(a: list[F], b: list[F]) -> list[F]:
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)

def remainder(a: list[F], b: list[F]) -> list[F]:
    if not b or not b[-1]:
        raise ValueError("The divisor must have nonzero leading coefficient.")
    a = trim(a)
    while len(a) >= len(b) and a != [F(0)]:
        offset = len(a) - len(b)
        c = a[-1] / b[-1]
        for j, x in enumerate(b):
            a[j+offset] -= c*x
        a = trim(a)
    return a

def integrate(a: list[F]) -> F:
    return sum((x/F(i+1) for i, x in enumerate(a)), F(0))

def monic_shifted_legendre(n: int) -> list[F]:
    if n < 1:
        raise ValueError("n must be positive.")
    return [
        F((-1)**(n+k)*comb(n,k)*comb(n+k,k), comb(2*n,n))
        for k in range(n+1)
    ]

def bigon_diagonal(n: int, x: F, y: F, g: F) -> F:
    if n < 0 or not all(0 < v < 1 for v in (x,y,g)):
        raise ValueError("Require n >= 0 and strict survival/coin parameters.")
    lam = lambda k: k*(k-1)//2
    return sum((
        F(comb(n,k))*g**k*(1-g)**(n-k)*x**lam(k)*y**lam(n-k)
        for k in range(n+1)
    ), F(0))

def main() -> None:
    examples = []
    for n in range(1,7):
        p = monic_shifted_legendre(n)
        for j in range(2*n):
            h = [F(0)]*j + [F(1)]
            assert integrate(remainder(h,p)) == F(1,j+1)
        square = mul(p,p)
        assert remainder(square,p) == [F(0)]
        norm = integrate(square)
        assert norm == F(1,(2*n+1)*comb(2*n,n)**2)
        examples.append({
            "quadrature_nodes":n,
            "all_monomials_checked_through_degree":2*n-1,
            "positive_squared_polynomial_integral":str(norm),
        })
    p2 = monic_shifted_legendre(2)
    patterns = 0
    for m in range(1,4):
        for bits in product((0,1), repeat=m):
            h = [F(1)]
            for bit in bits:
                h = mul(h, [F(0),F(1)] if bit else [F(1),-F(1)])
            count = sum(bits)
            exact = F(factorial(count)*factorial(m-count),factorial(m+1))
            assert integrate(remainder(h,p2)) == exact
            patterns += 1
    fourth = integrate(remainder([F(0)]*4+[F(1)],p2))
    assert fourth == F(7,36)
    assert F(1,5)-fourth == F(1,180)
    b2 = bigon_diagonal(2,F(1,2),F(1,2),F(1,2))
    b3 = bigon_diagonal(3,F(1,2),F(1,2),F(1,2))
    assert b2 == F(3,4) and b3 == F(13,32)
    assert b3/b2**3 == F(26,27)
    print(json.dumps({
        "scope":"finite exact checks of a NON-G4 comparison model and one physical insertion calculation",
        "quadrature_examples":examples,
        "all_labelled_Bernoulli_patterns_checked_through_3":patterns,
        "uniform_fourth_moment":"1/5",
        "two_node_fourth_moment":str(fourth),
        "fourth_moment_gap":"1/180",
        "physical_fair_cell":{"b2":str(b2),"b3":str(b3),"pair_retuned_triple_ratio":str(b3/b2**3)},
        "full_quantifiers_checked_by_computation":False,
        "physical_quadrature_realizer_produced":False,
        "G4_master_proved_or_disproved":False,
        "Lean_or_Rust_executed":False,
    },indent=2,sort_keys=True))

if __name__ == "__main__":
    main()
