"""Independent sparse-polynomial/monomial-interval check of a contraction certificate.
This does not import the author's AD interval implementation or numerical solver.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib, json, sys, importlib.util
import sympy as s
BASE=Path(__file__).resolve().parents[1]
STAGE=BASE/'graph-g3-critical-tail-20261004-1930z'
CERT=STAGE/'THREE-CELL-EXACT-CERTIFICATE.json'
assert hashlib.sha256(CERT.read_bytes()).hexdigest()=='3122ecd988e0685108b9617c3daec3932eef2f8d85fc23aa7c699387c0c1cac4'
c=json.loads(CERT.read_text());assert c['pivot_indices']==[4,5,6,7]
fixed=[Q(x) for x in c['fixed_parameters']]
center=[Q(x) for x in c['center']];radius=Q(c['radius'])
A=[[Q(x) for x in row] for row in c['preconditioner']]
assert len(A)==4 and all(len(r)==4 for r in A)
assert all(0<x<1 for x in fixed)
x,y,z,w=s.symbols('x y z w');vs=(x,y,z,w)
def S(q):return s.Rational(q.numerator,q.denominator)
def bare(x,y):
 return ((2+x+y)/4,(x**3+y**3+3*x+3*y)/8,
 (x**6+y**6+4*x**3+4*y**3+6*x*y)/16,
 ((1-x)**3+(1-y)**3)/24-(x-y)**2/8)
b1=bare(*map(S,fixed[:2]));b2=bare(*map(S,fixed[2:4]));b3=bare(x,y)
pair=b1[0]*b2[0]*b3[0]*z*w
trip=b1[1]*b2[1]*b3[1]*(z*w)**3
quad=b1[2]*b2[2]*b3[2]*(z*w)**6
C12=z*b2[0]*b1[3]+b1[2]*z**6*b2[3]
H12=(1-z*b2[0])*b1[3]
C=b3[0]*w*C12+b1[2]*b2[2]*(z*w)**6*b3[3]
H=H12+(1-w*b3[0])*C12
forms=[pair,trip,quad,C,H]
F=[trip-pair**3,quad-pair**6,C,H]
def poly(expr):return [(tuple(int(i) for i in m),Q(q)) for m,q in s.Poly(expr,*vs).terms()]
PF=list(map(poly,F));PJ=[[poly(s.diff(e,v)) for v in vs] for e in F]
def value(p,pt):
 return sum((coeff*product(t**n for t,n in zip(pt,ex)) for ex,coeff in p),Q())
def product(items):
 r=Q(1)
 for t in items:r*=t
 return r
def interval(p,lo,hi):
 # All variables positive; monomial powers are monotone. Coefficient signs
 # determine whether a monomial's low/high bounds are exchanged.
 lower=upper=Q()
 for ex,coeff in p:
  a=product(t**n for t,n in zip(lo,ex));b=product(t**n for t,n in zip(hi,ex))
  lower+=coeff*(a if coeff>=0 else b);upper+=coeff*(b if coeff>=0 else a)
 return lower,upper
def verify(pt,preconditioner):
 lo=[t-radius for t in pt];hi=[t+radius for t in pt]
 assert all(0<a<b<1 for a,b in zip(lo,hi))
 J=[[interval(p,lo,hi) for p in row] for row in PJ]
 row_norms=[]
 for i in range(4):
  norm=Q()
  for j in range(4):
   lower=upper=Q(int(i==j))
   for k in range(4):
    q=-preconditioner[i][k];a,b=J[k][j]
    lower+=q*(a if q>=0 else b);upper+=q*(b if q>=0 else a)
   norm+=max(abs(lower),abs(upper))
  row_norms.append(norm)
 eta=max(row_norms);fv=[value(p,pt) for p in PF]
 eps=max(abs(sum(preconditioner[i][k]*fv[k] for k in range(4))) for i in range(4))
 return eta,eps,interval(poly(pair),lo,hi)
eta,eps,bounds=verify(center,A)
assert eta<Q(1,2) and eps+eta*radius<radius and Q(1,8)<bounds[0]<bounds[1]<1
zero=verify(center,[[Q()]*4 for _ in range(4)])
assert zero[0]==1
bad=center[:];bad[0]+=Q(1,10000);wrong=verify(bad,A)
assert not(wrong[0]<Q(1,2) and wrong[1]+wrong[0]*radius<radius)
# Independent inherited full labelled-forest compiler confirms the quotient
# representation on a rational near-center control and a different rational word.
provider=BASE/'solver-recovery-20261004-1724z/exact/practical-solver-g3-algebra-20261004/checkpoint-polynomial-v1/upstream/forest_algebra.py'
spec=importlib.util.spec_from_file_location('forest_provider',provider);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
alg=m.ForestAlgebra(4)
def fullword(v):
 out=alg.bigon(v[0],v[1],Q(1,2),'independent')
 for factor in (alg.edge(v[6]),alg.bigon(v[2],v[3],Q(1,2),'independent'),alg.edge(v[7]),alg.bigon(v[4],v[5],Q(1,2),'independent')):
  out=alg.mul(out,factor)
 return out
def quotient(v):
 B=[bare(S(v[i]),S(v[i+1])) for i in (0,2,4)]
 q=[Q(B[0][j]*B[1][j]*B[2][j]*S(v[6]*v[7])**d) for j,d in enumerate((1,3,6))]
 c12=v[6]*Q(B[1][0])*Q(B[0][3])+Q(B[0][2])*v[6]**6*Q(B[1][3])
 h12=(1-v[6]*Q(B[1][0]))*Q(B[0][3])
 return q+[Q(B[2][0])*v[7]*c12+Q(B[0][2]*B[1][2])*(v[6]*v[7])**6*Q(B[2][3]),h12+(1-v[7]*Q(B[2][0]))*c12]
def reconstruct(k,f,q):
 s2,s3,s4,C,H=q
 if k==0 or k==1:return Q(1)
 if k==2:return s2 if len(f)==2 else 1-s2
 if k==3:
  return s3 if len(f)==3 else (s2-s3)/2 if len(f)==2 else (1-3*s2/2+s3/2)/3
 p3=2*(s3-s4);p1=1-Q(9,5)*s2+s3-s4/5+Q(3,10)*C;p2=1-p1-p3-s4;t=p2/3+C;balanced=p1/3+H
 if len(f)==4:return s4
 if len(f)==3:return p3/6
 if len(f)==2:return t/3 if sorted(len(m.leaves(t)) for t in f)==[2,2] else (p2-t)/12
 return balanced/3 if sorted(len(m.leaves(t)) for t in f[0])==[2,2] else (p1-balanced)/12
near=fixed[:]
for j,v in zip((4,5,6,7),center):near[j]=Q(v.numerator*10**6//v.denominator,10**6)
controls=[near,[Q(1,3),Q(2,5),Q(3,7),Q(4,9),Q(5,11),Q(6,13),Q(7,15),Q(8,17)]]
for v in controls:
 out=fullword(v);q=quotient(v)
 assert all(out[i]==reconstruct(k,f,q) for i,(k,f) in enumerate(alg.coords))
result={'status':'PASS','certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'method':'independently simplified source polynomials; symbolic differentiation; signed positive-monomial Fraction intervals; no author AD or numerical root finder',
'eta_upper_display':float(eta),'eps_upper_display':float(eps),'exact_contraction_and_invariance':True,
'strict_parameter_and_pair_floor_checks':True,'negative_controls':2,
'full_labelled_forest_control_coordinates':2*47,
'forest_provider_sha256':hashlib.sha256(provider.read_bytes()).hexdigest(),
'full_forest_control_scope':'two exact rational controls; uniform quotient identity separately reviewed from its source derivation',
'scope':'one exact cap-four three-cell ordinary return and rank certificate, not all-cap or G3/G4 closure'}
(Path(__file__).parent/'INDEPENDENT-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))

