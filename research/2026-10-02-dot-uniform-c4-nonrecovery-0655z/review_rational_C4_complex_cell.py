"""Independent exact algebraic controls for the all-cap RATIONAL adapter proof.
This finite check is supplementary: the all-n diagonal nonvanishing bound and
algebraic-group continuation/regularity are HAND proofs, not checked by enumeration.
Contributor: dot / continue_lean_proofs_two, 2026-10-02.
"""
from pathlib import Path
from math import comb
import sympy as S
import hashlib,json,time
p=Path(__file__).parent;t=time.monotonic();u=S.Symbol('u');f=S.Poly(u**4+6*u**2+1,u)
assert f.is_irreducible
x,y,g=S.symbols('x y g');h=1-g
eta=g**4*x**4+h**4*y**4+4*g**3*h*x*x+4*g*h**3*y*y+4*g*g*h*h*x*y+2*g*g*h*h
assert S.expand(eta.subs({x:u,y:u,g:S.Rational(1,2)})-f.as_expr()/8)==0
# Powers in Q[u]/(u^4+6u^2+1). Independent integer recurrence, no approximate roots.
N=64;maxexp=comb(N,2);powers=[(1,0,0,0)]
for k in range(maxexp):
 a,b,c,d=powers[-1];powers.append((-d,a,b-6*d,c))
controls=[]
for n in range(N+1):
 v=[0,0,0,0]
 for j in range(n+1):
  e=comb(j,2)+comb(n-j,2)
  for a in range(4):v[a]+=comb(n,j)*powers[e][a]
 assert any(v)
 # Check the centered exponent identities used in the all-n hand argument.
 if n%2==0:
  m=n//2
  assert all(comb(j,2)+comb(n-j,2)==m*(m-1)+(j-m)**2 for j in range(n+1))
 else:
  m=(n-1)//2
  assert all(comb(m-d,2)+comb(n-(m-d),2)==m*m+d*(d+1) for d in range(m+1))
 controls.append({'n':n,'nonzero_remainder':True,'remainder_sha256':hashlib.sha256(str(tuple(v)).encode()).hexdigest()})
# Exact rational dominance enclosure: r=sqrt(2)-1 <1/2 hence
# r^2/(1-r^2)<1/3. Strict rational sqrt(2)<3/2 because 2<9/4.
assert S.Rational(2)<S.Rational(9,4)
result={'status':'PASS_EXACT_ALGEBRAIC_CONTROLS','scope':'Controls n=0..64 support an ALL-n hand parity/dominance proof; no all-n inference from finite enumeration, no Lean/group-theorem verification','quartic':'u^4+6*u^2+1','quartic_irreducible_over_Q':True,'symmetric_C4_equals_quartic_over_8':True,'controls':controls,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'seconds':time.monotonic()-t}
(p/'rational-C4-independent-complex-cell-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='controls'},indent=2))
