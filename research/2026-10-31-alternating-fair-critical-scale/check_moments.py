import sympy as s
N=s.symbols('N', positive=True)
x=1-s.Rational(1,2)/N
y2=1/(3*N)
cubic=s.factor(x*x+3*y2-1)
quartic=s.factor(x**4+6*x*x*y2+y2**2-x)
assert s.simplify(cubic-1/(4*N**2))==0
assert s.simplify(quartic-(1/(2*N)-s.Rational(7,18)/N**2+1/(16*N**4)))==0
print('Cubic normalized residual:',cubic)
print('Quartic normalized residual:',quartic)
print('PASS: exact scalar moment matching only; no source engine or matrix bank executed.')
