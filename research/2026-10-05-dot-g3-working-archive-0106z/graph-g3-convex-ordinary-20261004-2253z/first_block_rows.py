from pathlib import Path
import pickle,json
import sympy as S
from fractions import Fraction as Q
from probe_first_composable_blocks import Algebra,F
p=Path(__file__).parent;c=pickle.loads((p/'first-composable-working-cache.pkl').read_bytes());a=Algebra(6)
b42=c['bases'][4,2][0];b64=c['bases'][6,4][0];pr=a.mul(b64,b42);sp=F.Span(a.d);sp.add(pr)
for v in c['bases'][6,2]:sp.add(v)
mat=S.Matrix.hstack(*map(S.Matrix,sp.original));piv=mat.T.rref()[1]; inv=mat[list(piv),:].inv()
def dual(pair,basis=None):
 if basis:
  i=next(i for i,x in enumerate(basis) if x); get=lambda v:Q(v[i])/basis[i]
 else:
  get=lambda v:sum(inv[0,j]*v[i] for j,i in enumerate(piv))
 out=[]
 for j in range(a.d):
  v=[Q(0)]*a.d;v[j]=Q(1);out.append(get(a.block(v,*pair)))
 return out
rows={'a64':dual((6,4),b64),'b42':dual((4,2),b42),'c62':dual((6,2))}
result={}
for name,row in rows.items():
 result[name]=[[str(coef),k,s] for coef,(k,s) in zip(row,a.coords) if coef]
 print(name,result[name],flush=True)
result['bases']={name:[str(q) for q in v] for name,v in [('A64',b64),('B42',b42),('P62',pr)]}
result['allword_recurrence']='a(KL)=b6(K)a(L)+a(K)b4(L); b(KL)=b4(K)b(L)+b(K)b2(L); c(KL)=b6(K)c(L)+c(K)b2(L)+a(K)b(L)'
result['bare_cell_identity']='c(B)=3*a(B)/4; E has a=b=c=0'
result['status']='WORKING_EXACT_QUOTIENT_IDENTITIES; requires independent verification before theorem use; no sign obstruction or attainment claim'
(p/'FIRST-BLOCK-ROWS-WORKING.json').write_text(json.dumps(result,indent=2)+'\n')
