"""Independent exact check from the COMMON factor formula, not a source compiler."""
import hashlib
import json
from pathlib import Path
import sympy as s

EXP = (1, 3, 6, 10, 15, 21)
C = (
    104595575837253277969423829052,
    -423080502595653001501725715375,
    2643239715767546013063327710250,
    -15159867147530683078171448846250,
    22206412057344123925161397190265,
    -9342490559405266592740508682662,
)
q = s.Symbol('q')
columns = [
    [s.Integer(n) for n in EXP],
    [2*(1-s.Rational(1,2)**n)/(1+s.Rational(1,2)**n) for n in EXP],
    [-n*s.Rational(1,2)**(n-1)/(1+s.Rational(1,2)**n) for n in EXP],
    [2*(1-s.Rational(1,3)**n)/(1+s.Rational(1,3)**n) for n in EXP],
    [-n*s.Rational(1,3)**(n-1)/(1+s.Rational(1,3)**n) for n in EXP],
]
J = s.Matrix.hstack(*(s.Matrix(column) for column in columns))
assert J.rank() == 5
assert s.Matrix(1, 6, C)*J == s.zeros(1,5)
F = s.Poly(sum(c*(1-q**n) for c,n in zip(C,EXP)), q)
G, rem = s.div(F, s.Poly((1-q)**2,q))
assert rem.is_zero
assert G.eval(0) > 0 and G.eval(1) > 0
assert G.count_roots(0,1) == 0

exponents = (0,1,3,6,10,15,21,28)
rows = [[s.Integer(1)]*len(exponents)]
for x in (s.Rational(1,2),s.Rational(1,3),s.Rational(1,6)):
    rows.append([x**n for n in exponents])
    rows.append([n*x**(n-1) if n else 0 for n in exponents])
E = s.Matrix(rows)
assert E.rank() == 7
v = E.nullspace()[0]
assert v[0] != 0
P = sum(a*q**n for a,n in zip(v,exponents))
assert s.diff(P,q).subs(q,1) != 0
for x in (s.Rational(1,2),s.Rational(1,3),s.Rational(1,6)):
    assert s.diff(P,q,2).subs(q,x) != 0

result = {
    'status':'PASS: independent exact rational derivatives and polynomial root audit',
    'contributor':'root independent reviewer',
    'strong_word_jacobian_rank':5,
    'integer_normal_annihilates_every_actual_derivative':True,
    'rare_polynomial_divisible_by_one_minus_q_squared':True,
    'remaining_polynomial_degree':G.degree(),
    'remaining_polynomial_roots_closed_unit_interval':0,
    'remaining_polynomial_at_zero':str(G.eval(0)),
    'remaining_polynomial_at_one':str(G.eval(1)),
    'endpoint_exposure_rank':7,
    'endpoint_root_simple_and_three_interior_roots_exactly_double':True,
    'source':'h_lambda=a lambda - log(1-p1+p1 r1^lambda) - log(1-p2+p2 r2^lambda)',
    'verification_limit':'Mathematical source formula algebra; not genealogy compiler, nonlinear whole-fibre proof, Lean or biological validation',
    'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
out = Path(__file__).with_name('INDEPENDENT-BOUNDARY-NORMAL-EXACT-RECEIPT.json')
with out.open('x') as f:
    json.dump(result,f,indent=2); f.write('\n')
print(json.dumps(result))
