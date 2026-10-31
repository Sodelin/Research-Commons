import sympy as s
t=s.symbols('t',positive=True)
e6=s.exp(-6*t);e3=s.exp(-3*t);e1=s.exp(-t)
p43=(e3-e6)/3;p32=(e1-e3)/2;p42=e1/10-e3/6+e6/15
ER=s.Rational(1,2)*e6-s.Rational(3,2)*p43
RE=12*p42-3*p32+s.Rational(1,2)*e1
assert s.simplify(ER-RE-(e6-e1)/5)==0
print('PASS exact selected-entry scalar algebra:',s.simplify(ER-RE))
print('Only supplied legal path coefficients checked; no source engine or full matrix bank executed.')
