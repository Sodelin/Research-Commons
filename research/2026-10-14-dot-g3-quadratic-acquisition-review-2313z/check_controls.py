"""Small independent exact controls, not QE or physical source synthesis."""
import json
from pathlib import Path
import sympy as S

L = [1, 3, 6, 10, 15, 21]
r = S.Rational(1, 2)
D = lambda x: S.Matrix([1-x**n for n in L])
Dp = lambda x: S.Matrix([-n*x**(n-1) for n in L])
V = S.Matrix.hstack(S.Matrix(L), D(r), Dp(r), D(r*r), Dp(r*r))
d = D(r**3)
nu = S.Matrix([6548201697807, -44625849584225, 322432296415950,
               -1841737514410080, 2686046822645760, -1127647220334592])
a = (nu.T*d)[0]
C = sum(abs(nu[i])*d[i]**2 for i in range(6))
g = a/(8*(C+a))
checks = {
    'rankV': V.rank(), 'rankVd': V.row_join(d).rank(),
    'det': str(V.row_join(d).det()),
    'normal_zero': list(V.T*nu) == [0]*5,
    'a_positive': bool(a > 0), 'g_bounds': bool(0 < g < S.Rational(1, 8)),
    'd0_bound': bool(S.Rational(1, 1024)**2 < g/2),
    'B_positive': bool(sum(nu[i]*d[i]/(1-g*d[i]) for i in range(6)) > 0),
    'error_bound': bool(2*g*C < a/4),
    'taylor_integral_factor': str(S.integrate((1-S.Symbol('x'))**5,
                                  (S.Symbol('x'), 0, 1))/S.factorial(5)),
}
s,k,w,v,eta,m,aa,bb,c,J,H,K = S.symbols('s k w v eta m aa bb c J H K')
u = s**3*(w+k*v)+s**6*eta
dm = s**6*aa+s**8*bb
P = J*u+H*u*u/2+K*u*dm+c*dm
# Only the kernel-killed linear term is removed; all mixed terms remain.
P = S.expand(P-J*s**3*(w+k*v))
checks['orders_below_six_zero'] = all(P.coeff(s,i) == 0 for i in range(6))
checks['sixth_coefficient_correct'] = S.expand(P.coeff(s,6)-(J*eta+H*(w+k*v)**2/2+c*aa)) == 0
print(json.dumps(checks, indent=2))
assert checks['rankV'] == 5 and checks['rankVd'] == 6
assert checks['det'] == '-2118985083947862963746960823315/664613997892457936451903530140172288'
assert checks['taylor_integral_factor'] == '1/720'
assert all(value for value in checks.values() if isinstance(value, bool))
