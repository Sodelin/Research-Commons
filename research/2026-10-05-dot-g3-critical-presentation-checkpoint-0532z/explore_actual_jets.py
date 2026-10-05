import sympy as S
s,u,v,a=S.symbols('s u v a', real=True)
x=s+u;y=s-u;g=S.Rational(1,2)+v
b=[]
for n in (2,3,4):b.append(S.expand(sum(S.binomial(n,j)*g**j*(1-g)**(n-j)*x**(j*(j-1)//2)*y**((n-j)*(n-j-1)//2) for j in range(n+1))))
V=lambda z:(2-3*z+z**3)/6
C=2*(g*g*(1-g)**2*(1-x)*(1-y)-g**3*(1-g)*V(x)-g*(1-g)**3*V(y))
f=S.Matrix([a*b[0],a**3*b[1],a**6*b[2],a**6*C])
base={u:0,v:0,s:S.Rational(1,2),a:S.Rational(3,4)}
J=f.jacobian([a,s,u,v]).subs(base)
print('rank',J.rank(),'J',J)
print('left annihilators')
for w in J.T.nullspace():
 q=S.expand((w.T*f)[0]);h=S.hessian(q,[u,v]).subs(base)/2
 print('w',list(w),'quadratic matrix',h,'det',S.factor(h.det()))
# Cap three normal projection at the symmetric physical cell
ell=b[1]-S.Rational(3,2)*(s*s+1)*b[0]
H=S.simplify(S.hessian(ell,[u,v]).subs({u:0,v:0})/2)
print('cap3normal',H,'det',S.factor(H.det()))
for vals in [{a:S.Rational(3,4),s:S.Rational(1,2),u:S.Rational(1,8),v:S.Rational(1,6)}, {a:S.Rational(3,4),s:S.Rational(1,2),u:0,v:S.Rational(1,6)}]:
 jj=f.jacobian([a,s,u,v]).subs(vals)
 print('generic rank',jj.rank(),'det',jj.det())
a2,a4,s2,s4=S.symbols('a2 a4 s2 s4')
subv={u:0,a:S.Rational(3,4)+a2*v**2+a4*v**4,s:S.Rational(1,2)+s2*v**2+s4*v**4}
ser=[S.series(ff.subs(subv)-ff.subs(base),v,0,5).removeO().expand() for ff in f]
sol2=S.solve([ss.coeff(v,2) for ss in ser[:2]],[a2,s2]);print('sol2',sol2)
sol4=S.solve([ss.subs(sol2).coeff(v,4) for ss in ser[:2]],[a4,s4]);print('sol4',sol4)
res=[S.factor(ss.subs(sol2).subs(sol4).coeff(v,4)) for ss in ser];print('res4',res)
w1,w2=J.T.nullspace();c=S.Rational(6561,524288);d=S.Rational(729,131072)
w=w1/c+2*w2/d
print('normalw',list(w),'v4',sum(w[i]*res[i] for i in range(4)))

# Acceptance guards on the exact symbolic transcription.
assert J.rank()==2
assert sol2=={a2:S.Integer(3),s2:S.Integer(-4)}
assert sol4=={a4:S.Integer(30),s4:S.Integer(-20)}
assert res==[0,0,-S.Rational(729,8192),-S.Rational(11421,32768)]
assert list(w)==[-S.Rational(152,3),S.Rational(2048,81),S.Rational(524288,6561),S.Rational(262144,729)]
assert sum(w[i]*res[i] for i in range(4))==-S.Rational(1192,9)
assert S.simplify((w.T*f)[0].diff(u,2).subs(base)/2)==-1
assert S.simplify((w.T*f)[0].diff(u,v).subs(base))==0
assert S.simplify((w.T*f)[0].diff(v,2).subs(base))==0
print('EXACT_JET_CONTROLS_PASS; SymPy',S.__version__)
