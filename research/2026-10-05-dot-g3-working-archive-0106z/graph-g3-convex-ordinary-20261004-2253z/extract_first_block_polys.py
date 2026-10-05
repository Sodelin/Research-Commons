"""Exact exploratory Peirce block polynomials; no sign theorem."""
from pathlib import Path
import pickle,json,sys
import sympy as S
from fractions import Fraction as Q
from probe_first_composable_blocks import Algebra,F
p=Path(__file__).parent
cache=pickle.loads((p/'first-composable-working-cache.pkl').read_bytes())
a=Algebra(6);assert a.coords==cache['coords']
mons=sorted(set().union(*(set(q) for q in cache['polys'])))
coeff=[tuple(q.get(mon,Q(0)) for q in cache['polys']) for mon in mons]
x,y,g,z,e=S.symbols('x y g z e')
def poly(vs,basis):
 mat=S.Matrix.hstack(*[S.Matrix(b) for b in basis]); piv=mat.T.rref()[1];sq=mat[list(piv),:];inv=sq.inv()
 cols=[]
 for v in vs:cols.append(inv*S.Matrix([v[j] for j in piv]))
 out=[]
 for i in range(len(basis)):
  out.append(S.factor(sum(v[i]*x**mon[0]*y**mon[1]*g**mon[2] for mon,v in zip(mons,cols))))
 return out
b42=cache['bases'][4,2][0];b64=cache['bases'][6,4][0];prod=a.mul(b64,b42);sp=F.Span(a.d);sp.add(prod)
for b in cache['bases'][6,2]:sp.add(b)
assert len(sp)==3
blocks={}
for pair,bas in [((4,2),[b42]),((6,4),[b64]),((6,2),sp.original)]:
 vs=[a.block(c,*pair) for c in coeff]
 pp=poly(vs,bas);blocks[str(pair)]=[str(q) for q in pp]
 print(pair,flush=True)
 for q in pp:print(S.factor(q),flush=True)
 # Exact coefficient extraction for g=e, y=exp(-z*e), with x fixed.
 for i,q in enumerate(pp):
  pq=S.Poly(q,x,y,g); cs=[]
  for k in range(2,8):
   c=S.factor(sum(cc*x**a*(-z*b)**(k-c)/S.factorial(k-c) for (a,b,c),cc in pq.terms() if c<=k))
   if c!=0:cs.append((k,str(c)))
  print('jets',i,cs[:3],flush=True)
Path(__file__).with_name('FIRST-BLOCK-POLYNOMIALS-WORKING.json').write_text(json.dumps({'blocks':blocks,'scope':'Exact source polynomial expressions only; basis selected from pinned per-labelled forest graft algebra. No sign/attainment claim.'},indent=2)+'\n')
