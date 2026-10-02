"""Bounded modular coprimality certificate over Q(r), 2r^2=1.

The good-place/degree-preservation lifting and source consequences are hand
proofs recorded separately. This computes the finite-field witness only.
"""
from pathlib import Path
import json
import resource
import time
import sympy as S

resource.setrlimit(resource.RLIMIT_AS, (600*1024**2, 600*1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (20, 20))
started = time.monotonic()
modulus = 1009
lam = [1, 3, 6, 10, 15, 21]


def solve_mod(matrix, target):
    n = len(matrix)
    a = [[value % modulus for value in row] + [target[i] % modulus]
         for i, row in enumerate(matrix)]
    determinant = 1
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            raise ValueError("singular modular normal system")
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            determinant = -determinant
        value = a[k][k]
        determinant = determinant*value % modulus
        inv = pow(value, -1, modulus)
        a[k] = [(value*inv) % modulus for value in a[k]]
        for i in range(n):
            if i != k:
                scale = a[i][k]
                a[i] = [(u-scale*v) % modulus for u, v in zip(a[i], a[k])]
    return determinant % modulus, [row[-1] for row in a]


roots = S.sqrt_mod(pow(2, -1, modulus), modulus, all_roots=True)
for root in roots:
    rmod = int(root)
    squared = rmod*rmod % modulus
    matrix = [[1]*6, [v % modulus for v in lam]]
    for node in [rmod, squared]:
        matrix.append([(1-pow(node, v, modulus)) % modulus for v in lam])
        matrix.append([(v*pow(node, v-1, modulus)) % modulus for v in lam])
    try:
        det, c = solve_mod(matrix, [1, 0, 0, 0, 0, 0])
    except ValueError:
        continue
    if all(c):
        break
else:
    raise AssertionError("no good selected place at this fixed prime")
assert 2*rmod*rmod % modulus == 1 and det != 0 and c[0] != 0
assert all(sum(a*b for a, b in zip(row, c)) % modulus == value
           for row, value in zip(matrix, [1, 0, 0, 0, 0, 0]))
bp, q = S.symbols("p q")
f = [1-bp+bp*q**v for v in lam]
other = [S.prod(f[j] for j in range(6) if j != i) for i in range(6)]
P = S.Poly(sum(c[i]*(1-q**lam[i])*other[i] for i in range(6)), bp, q, modulus=modulus)
Q = S.Poly(sum(c[i]*lam[i]*q**(lam[i]-1)*other[i] for i in range(6)), bp, q, modulus=modulus)
Pr = P.exquo(S.Poly((q-1)**2, bp, q, modulus=modulus))
Qr = Q.exquo(S.Poly((1-bp)*(q-1), bp, q, modulus=modulus))
assert Pr.total_degree() == 59 and Qr.total_degree() == 57
assert int(Pr.coeff_monomial(bp**5*q**54)) % modulus == modulus-1
assert int(Qr.coeff_monomial(bp**4*q**53)) % modulus == -c[0] % modulus
gcd = S.gcd(Pr, Qr)
assert gcd.total_degree() == 0
record = {
    "status": "PASS finite-field good-place coprimality witness",
    "field": "Q(r), 2*r^2-1=0; positive real embedding for source",
    "modulus": modulus, "r_mod": rmod,
    "minimal_polynomial_reduces_to_zero": True,
    "normal_matrix_mod": matrix, "normal_matrix_determinant_mod": det,
    "normal_mod": c,
    "removed_P_factor": "(q-1)^2", "removed_Q_factor": "(1-p)*(q-1)",
    "P_total_degree": int(Pr.total_degree()), "Q_total_degree": int(Qr.total_degree()),
    "P_leading_degree_witness": [5, 54, modulus-1],
    "Q_leading_degree_witness": [4, 53, (-c[0]) % modulus],
    "gcd_mod": str(gcd.as_expr()),
    "P_terms_mod": [[*mon, int(coeff) % modulus] for mon, coeff in Pr.terms()],
    "Q_terms_mod": [[*mon, int(coeff) % modulus] for mon, coeff in Qr.terms()],
    "seconds": time.monotonic()-started, "sympy": S.__version__,
    "scope": "Exact modular algebra. Degree-preservation/good-place lift, Baker rationality and actual-source interior transfer are separate hand proofs; no real critical roots or loss floor are computed."
}
Path(__file__).with_name("irrational-residue-modular-critical-check.json").write_text(json.dumps(record, indent=2)+"\n")
print(json.dumps({k: record[k] for k in ["status","modulus","r_mod","normal_matrix_determinant_mod","normal_mod","P_total_degree","Q_total_degree","gcd_mod","seconds"]}))
