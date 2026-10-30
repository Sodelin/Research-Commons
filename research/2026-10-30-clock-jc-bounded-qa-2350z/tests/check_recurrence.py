"""Own exact-rational regression checks, not a Lean proof or source-law audit."""
from fractions import Fraction as Q
from itertools import product
import hashlib,json,pathlib,random,datetime
rng=random.Random(20261030)
checks={'single_term_annihilator':0,'sum_annihilator':0,'monic_zero_prefix':0,'coordinate_annihilator':0,'empty_dimension':0}
bases=[Q(0),Q(1),Q(-1),Q(1,2),Q(2)]
def annihilate(bs, f, n):
    vals=[f(n+i) for i in range(len(bs)+1)]
    for b in reversed(bs): vals=[vals[j+1]-b*vals[j] for j in range(len(vals)-1)]
    return vals[0]
def poly(cs,n):return sum(c*Q(n)**j for j,c in enumerate(cs))
for r in range(1,5):
 for b in bases:
  for _ in range(8):
   cs=[Q(rng.randint(-4,4)) for j in range(r)]
   f=lambda n:b**n*poly(cs,n)
   for n in range(6):
    assert annihilate([b]*r,f,n)==0
    checks['single_term_annihilator']+=1
 for size in range(4):
  for _ in range(8):
   terms=[(rng.choice(bases),[Q(rng.randint(-3,3)) for j in range(r)]) for i in range(size)]
   bs=[b for b,_ in terms for j in range(r)]
   f=lambda n:sum(b**n*poly(cs,n) for b,cs in terms)
   assert len(bs)==size*r
   for n in range(4):
    assert annihilate(bs,f,n)==0
    checks['sum_annihilator']+=1
for length in range(9):
 for _ in range(10):
  bs=[rng.choice(bases) for j in range(length)]
  v=Q(rng.randint(-8,8));n=rng.randint(0,6)
  f=lambda k:v if k==n+length else Q(0)
  assert annihilate(bs,f,n)==v
  checks['monic_zero_prefix']+=1
for r in range(1,4):
 for size in range(4):
  exps=list(product(range(r),repeat=2))
  terms=[([rng.choice(bases) for _ in range(2)],{e:Q(rng.randint(-3,3)) for e in exps}) for _ in range(size)]
  def value(v):
   return sum(sum(c*Q(v[0])**e[0]*Q(v[1])**e[1] for e,c in cs.items())*b[0]**v[0]*b[1]**v[1] for b,cs in terms)
  for i in range(2):
   bs=[b[i] for b,cs in terms for _ in range(r)]
   for other in range(5):
    f=lambda n:value((n,other) if i==0 else (other,n))
    for n in range(4):
     assert annihilate(bs,f,n)==0
     checks['coordinate_annihilator']+=1
# A=0 has one empty count vector, no coordinates; its cube condition already
# asserts the value at that sole vector. It does not imply an arbitrary scalar is zero.
assert list(product(range(0),repeat=0))==[()]
checks['empty_dimension']+=1
root=pathlib.Path(__file__).resolve().parent.parent/'evidence'
sources=[(pathlib.Path(__file__).resolve().parent.parent/'candidate-inputs')/n for n in ['JC69ExponentialPolynomial.lean','JC69CountVectorGrid.lean']]
result={'status':'PASS_EXACT_RATIONAL_REGRESSION_ONLY','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'seed':20261030,'counts':checks,'total':sum(checks.values()),'source_hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'limits':'Finite regression, not kernel proof, exhaustive universal validation, scientific likelihood representation, finite-window completion or novelty claim. Zero/repeated/negative bases exercised; the application may use a narrower base domain.'}
(root/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
