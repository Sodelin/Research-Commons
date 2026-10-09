import sympy as s
p,q=s.symbols('p q')
R=[1+2*p*(q**-1-1),1+3*p*(q**-2-1),1-4*p+2*p**2+4*p*(1-2*p)*q**-3+6*p**2*q**-4]
# Clear each row's log denominator and all q powers before expansion.
M=s.Matrix([[s.expand(-q**5*s.diff(r,q)),s.expand(q**4*s.diff(r,p)),s.expand(q**4*n*(n-1)*r)] for n,r in zip(range(2,5),R)])
d=s.factor(M.det(method='domain-ge'))/(q**12*s.prod(R))
claimed=24*p*q*(2*p+q)*(4*p-1)*(q-1)**4/((2*p*q-2*p-q)*(3*p*q**2-3*p-q**2)*(2*p**2*q**4-8*p**2*q+6*p**2-4*p*q**4+4*p*q+q**4))
assert s.cancel(d-claimed)==0
print('PASS exact determinant identity after row-denominator clearing')
print(s.factor(d))
