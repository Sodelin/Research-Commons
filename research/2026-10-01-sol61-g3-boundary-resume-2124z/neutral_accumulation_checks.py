"""New exact finite controls for the all-cap hand proof; no limit proof."""
import json
import platform
from pathlib import Path
import sympy as S

p = S.symbols('p')
kappa = p
rows = []
for k in range(1, 17):
    derivative = S.diff(kappa, p)
    gcd = S.Poly(S.gcd(kappa, derivative), p).monic().as_expr()
    assert gcd == 1
    if k >= 2:
        assert S.degree(kappa, p) == k
        assert kappa.subs(p, 0) == kappa.subs(p, 1) == 0
        assert derivative.subs(p, 0) != 0 and derivative.subs(p, 1) != 0
        interior = S.cancel(kappa / (p * (1-p)))
        nroots = S.Poly(interior, p).count_roots(0, 1) if k > 2 else 0
        assert nroots == k-2
    else:
        nroots = 0
    rows.append({'order': k, 'polynomial': str(kappa),
                 'gcd_with_derivative': str(gcd),
                 'strict_interior_roots': int(nroots)})
    kappa = S.expand(p * (1-p) * derivative)

vandermonde = []
for cap in range(2, 15):
    lam = [j*(j-1)//2 for j in range(2, cap+1)]
    matrix = S.Matrix([[l**n for l in lam] for n in range(1, cap)])
    det = matrix.det(method='domain-ge')
    formula = S.prod(lam) * S.prod(lam[j]-lam[i]
                 for i in range(len(lam)) for j in range(i+1, len(lam)))
    assert det == formula and det != 0
    vandermonde.append({'cap': cap, 'determinant': str(det)})

out = {'python': platform.python_version(), 'sympy': S.__version__,
       'cumulant_controls': rows, 'sparse_vandermonde_controls': vandermonde,
       'scope': 'Finite exact checks only; uniform analytic remainder, curve selection, and all-cap conclusions are hand arguments.'}
Path(__file__).with_name('neutral-accumulation-checks.json').write_text(
    json.dumps(out, indent=2)+'\n')
print(json.dumps({'status': 'PASS', 'cumulant_orders': len(rows),
                  'sparse_vandermonde_caps': len(vandermonde)}))
