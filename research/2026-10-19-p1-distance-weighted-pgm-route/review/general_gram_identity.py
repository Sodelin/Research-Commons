import sympy as s
u, v, d = s.symbols('u v d', real=True)
H = s.Matrix([[1+v, s.sqrt(2)*u], [s.sqrt(2)*u, 1]])
res = (H+d*s.eye(2))**2 - (2+v+2*d)*H
assert s.simplify(res-(d*d-(1+v-2*u*u))*s.eye(2)) == s.zeros(2)
print('PASS: exact general symmetric Gram-block square-root identity after d^2=det(H); positivity and support limits are hand obligations.')
