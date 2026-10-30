import sympy as s
import json
z1,z2=s.symbols('z1 z2',positive=True)
a,c,b,d,e,f,g,h,i=s.symbols('a c b d e f g h i')
A=s.Matrix([[a,c],[0,b]]);M=s.Matrix([[d,e],[0,f]]);B=s.Matrix([[g,h],[0,i]])
for r in [4,5]:
 L=lambda n:n*(n-1)//2
 E=lambda z:s.diag(z**L(r),z**L(r-2))
 diff=(E(1/(z1*z2))*A*E(z1)*M*E(z2)*B-A*M*B)[0,1]
 expected=c*f*i*((z1*z2)**(-(2*r-3))-1)+a*e*i*(z2**(-(2*r-3))-1)
 assert s.simplify(diff-expected)==0
print(json.dumps(dict(status='PASS',identity='exact entire endpoint change under two gap transfers',arities=[4,5],scope='Generic algebra check; no new source witness or target membership'),indent=2))
