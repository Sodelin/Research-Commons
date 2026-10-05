"""Exact transcription controls for the separate uniform hand proof.
The quantified n theorem is proved by its labelled-case and Taylor arguments.
"""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib,sys,json
import sympy as S
provider=Path(__file__).resolve().parent/'source'
assert hashlib.sha256((provider/'forest_algebra_pinned.py').read_bytes()).hexdigest()=='850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884'
sys.path.insert(0,str(provider));import forest_algebra_pinned as F
def pair(j):return F.forest([F.tree(0,1)]+list(range(2,j)))
def triple(j):return F.forest([F.tree(F.tree(0,1),2)]+list(range(3,j)))
def two(j):return F.forest([F.tree(0,1),F.tree(2,3)]+list(range(4,j)))
def lam(j):return j*(j-1)/2
def lamq(j):return j*(j-1)//2
def U(j,x):return F.edge_law(j,x).get(pair(j),Q(0))
def V(j,x):return F.edge_law(j,x).get(triple(j),Q(0))
def C(n,law):return law.get(two(n),Q(0))-2*law.get(triple(n),Q(0))
def formula(n,x,y,g):
 return 2*sum((Q(comb(n-4,j))*(
   g**(j+2)*(1-g)**(n-j-2)*U(j+2,x)*U(n-j-2,y)
  -g**(j+3)*(1-g)**(n-j-3)*V(j+3,x)*y**lamq(n-j-3)
  -g**(j+1)*(1-g)**(n-j-1)*x**lamq(j+1)*V(n-j-1,y)) for j in range(n-3)),Q(0))
n,r,z=S.symbols('n r z')
u3=(r-r**3)/2;v3=S.Rational(1,3)-r/2+r**3/6;v4=r/10-r**3/6+r**6/15
P=r**3+6*r*z-3*r+3*z**2-6*z+2
H=2*((1-r)*(-(n-2)*z-(n-3)**2*z**2/2)+(n-4)*u3*z+v3*(n-3+lam(n-3)*z)-(n-4)*v4+(n-1)*z**2/2+(lam(n-1)+lam(n-2)+lam(n-3))*z**3/6-(n-4)*r*z**2/2)
records=[]
for Z,W,h_expected,cn,cn2 in [
 (S.Rational(3,8),9*(17*n+49)/2560,-27*(17*n+52)/10240,S.Rational(459,10240),-S.Rational(459,10240)),
 (S.Rational(9,8),9*(143*n+71)/2560,27*(143*n+108)/10240,-S.Rational(3861,10240),S.Rational(3861,10240))]:
 sub={r:S.Rational(1,4),z:Z}
 assert S.factor(P.subs(sub))==0
 assert S.factor(H.subs(sub)-h_expected)==0
 adj=S.diff(P,z).subs(sub)*(W+Z**2/2)/3
 assert S.factor(H.subs(sub)-adj-cn)==0
 assert S.factor(H.subs(n,n+2).subs(sub)-adj-cn2)==0
 records.append({'Z':str(Z),'W_n':str(W),'C_n_quartic':str(cn),'C_n_plus_2_quartic':str(cn2)})
cell_checks=0
for N in [4,5,6]:
 for x,y,g in [(Q(1,3),Q(2,3),Q(1,3)),(Q(1,4),Q(3,5),Q(2,5))]:
  law=F.bigon_law(N,x,y,g,'independent')
  assert C(N,law)==formula(N,x,y,g);cell_checks+=1
 # The ordinary rank-history cancellation is checked in every labelled row.
 assert C(N,F.edge_law(N,Q(2,3)))==0
a=F.ForestAlgebra(6)
K=a.bigon(Q(1,3),Q(2,3),Q(1,3),'independent')
L=a.mul(a.edge(Q(3,4)),a.bigon(Q(1,4),Q(3,5),Q(2,5),'independent'))
KL=a.mul(K,L)
def cv(n,v):return v[a.index[n,two(n)]]-2*v[a.index[n,triple(n)]]
def bv(n,v):return v[a.index[n,tuple(range(n))]]
for N in [4,5,6]:assert cv(N,KL)==cv(N,K)*bv(N-2,L)+bv(N,K)*cv(N,L)
out={'status':'EXACT_CONTROLS_PASS','uniform_symbolic_variable':'n','uniform_families':records,'labelled_bare_formula_controls':cell_checks,'labelled_ordinary_controls':3,'labelled_serial_controls':3,'labelled_coordinates_through_six':a.dim,'scope':'Uniform identities in n plus small exact transcription controls. The hand proof supplies all-arity/all-word quantifiers. No deterministic return or master conclusion.'}
Path(__file__).with_name('UNIFORM-WEAK-CONTRAST-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
