"""Independent exact review of the supplied cap-eight source certificate.
Reads the preserved proposal only; writes this lane's independent receipt.
Contributor: dot / continue_lean_proofs_two, 2026-10-02.
"""
from pathlib import Path
import json,itertools,math,hashlib,time
from fractions import Fraction
import sympy as sp
SRC=Path(__file__).parent;OUT=Path(__file__).parent;t=time.monotonic()
data=(SRC/'both-active-cubic-result.json').read_bytes();j=json.loads(data)
lam=(1,3,6,10,15,21,28)
assert tuple(j['normal']['lambda'])==lam
B=[list(map(int,reversed(row))) for row in j['normal']['B_coefficients_descending']]

def add(a,b):
 out=[0]*max(len(a),len(b))
 for k,c in enumerate(a):out[k]+=c
 for k,c in enumerate(b):out[k]+=c
 while len(out)>1 and out[-1]==0:out.pop()
 return out

def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for k,c in enumerate(a):
  for n,d in enumerate(b):out[k+n]+=c*d
 while len(out)>1 and out[-1]==0:out.pop()
 return out

def shift(a,n,c=1):return [0]*n+[c*x for x in a]

# Fresh ascending integer polynomial normal checks.
rows=[]
rows.append([([1],b) for b in B]);rows.append([([l],b) for l,b in zip(lam,B)])
for k in (1,2):
 rows.append([([1]+[0]*(k*l-1)+[-1],b) for l,b in zip(lam,B)])
 rows.append([(shift([l],k*l-k),b) for l,b in zip(lam,B)])
for row in rows:
 total=[0]
 for a,b in row:total=add(total,mul(a,b))
 assert total==[0]
assert all(any(b) for b in B)

# Source product coefficients via elementary symmetric subset sums, not the
# author's convolution code. The determinant is the coefficient map
# (A,B)->A*P+B*Q, converted to the proposal's descending row convention.
checks=[]
for rec in j['slices']:
 q=rec['q_slice'];assert q in (3,5)
 a=[q**l-1 for l in lam]
 basis=[]
 for omitted in range(7):
  others=[a[i] for i in range(7) if i!=omitted]
  basis.append([sum(math.prod(others[i] for i in inds) for inds in itertools.combinations(range(6),k)) for k in range(7)])
 def source_det(free):
  last=Fraction(sum((21-l)*u for l,u in zip(lam,free)),7)
  weights=list(map(Fraction,free))+[-sum(free)-last,last]
  assert all(v.denominator==1 and v for v in weights)
  weights=[int(v) for v in weights]
  assert sum(weights)==sum(l*w for l,w in zip(lam,weights))==0
  p=[sum(weights[i]*(-a[i])*basis[i][k] for i in range(7)) for k in range(7)]
  q0=[sum(weights[i]*lam[i]*q**(lam[i]-1)*basis[i][k] for i in range(7)) for k in range(7)]
  assert p[6]==0 and sum(q0)==0
  red=[sum(q0[:k+1]) for k in range(6)]
  assert q0[6]==-red[-1]
  cols=[]
  for poly in (p[:6],red):
   for k in range(5):cols.append([0]*k+poly+[0]*(4-k))
  M=sp.Matrix(10,10,lambda row,col:cols[col][row])
  canonical=-int(M.det(method='domain-ge'))
  return canonical,math.prod(weights)
 terms=[(tuple(ex),Fraction(c)) for ex,c in rec['residual_terms']]
 assert len(terms)==35 and len(set(ex for ex,c in terms))==35 and all(sum(ex)==3 and len(ex)==5 for ex,c in terms)
 simplex=[(7*(1+a0),7*(1+a1),7*(1+a2),7*(1+a3),7) for a0,a1,a2,a3 in itertools.product(range(4),repeat=4) if a0+a1+a2+a3<=3]
 # Five new signed generic controls and five new positive generic controls.
 extra=[]
 for k in range(1,6):
  extra.append((7*(k+1),7*(k+4),7*(2*k+3),7*(3*k+1),7*(k+6)))
  extra.append((7*(k+2),-7*(k+3),7*(2*k+7),-7*(3*k+4),7*(k+9)))
 for free in simplex+extra:
  det,product=source_det(free)
  rv=sum((c*math.prod(Fraction(x)**e for x,e in zip(free,ex)) for ex,c in terms),Fraction(0))
  assert rv*product==det
 # Independently rebuild the actual normal substitution in ascending Fraction
 # lists and normalize it to a primitive integer coefficient vector.
 poly=[Fraction(0)]
 for ex,c in terms:
  term=[c]
  for b,n in zip(B,ex):
   for _ in range(n):term=mul(term,b)
  poly=add(poly,term)
 den=math.lcm(*(c.denominator for c in poly));ints=[int(c*den) for c in poly]
 content=math.gcd(*ints);ints=[c//content for c in ints]
 proposed=list(map(int,reversed(rec['specialized_primitive_coefficients_descending'])))
 if ints[-1]<0:ints=[-v for v in ints]
 if proposed[-1]<0:proposed=[-v for v in proposed]
 assert ints==proposed and len(ints)-1==231
 checks.append({'slice':q,'unisolvent_nodes':len(simplex),'new_extra_controls':len(extra),'actual_source_degree_reductions':True,'full_normal_substitution_matches':True,'residual_degree':231})

# Independent explicit modular Bezout identity verification (no gcd call).
bz=json.loads((SRC/'modular-bezout.json').read_text());prime=bz['prime'];assert prime==1009
F=[list(map(int,reversed(rec['specialized_primitive_coefficients_descending']))) for rec in j['slices']]
assert all(len(f)==232 and f[-1]%prime for f in F)
s=list(reversed(bz['s_coefficients_descending']));tt=list(reversed(bz['t_coefficients_descending']))
bez=add(mul(s,F[0]),mul(tt,F[1]));assert bez[0]%prime==1 and all(c%prime==0 for c in bez[1:])
result={'status':'PASS_INDEPENDENT_EXACT_REPLAY','context_utc':'2026-10-02T05:09:00Z','proposal_sha256':hashlib.sha256(data).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'normal_identities':6,'source_coefficient_construction':'elementary symmetric subset sums','source_determinant':'exact SymPy domain-ge of ascending coefficient linear map, checked descending convention','slice_checks':checks,'explicit_modular_bezout_identity':True,'prime':prime,'both_input_degrees_preserved':True,'elapsed_seconds':time.monotonic()-t,'scope':'Exact certificate replay plus separate hand proof review; not Lean, whole G3 recognition, or sampled residual extrapolation.'}
(OUT/'portable-independent-replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
