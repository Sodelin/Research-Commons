"""One complete source-block membership test for the ordered cubic area."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import types,hashlib,json
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'g4-rare-route-fixed-functional-20261006-0204z/check_rare.py'
PIN='d462babef7afd0b5f6fa6c74328a6df9b2d31576e50e4832caef3c63fe137788'
SAVED=BASE.parent/'g4-lossless-resonance-20261005-2042z/attempt1/RESULT.json'
SAVED_PIN='a5ea76994a5b70668e604fa879cfc5281f0b3e6b38c20a8972e8c374e0430244'
def authenticated(path,pin):
 raw=path.read_bytes()
 if path.is_symlink() or hashlib.sha256(raw).hexdigest()!=pin:raise ValueError('provider identity')
 return raw
c=types.ModuleType('_rare_exact');c.__file__=str(PROVIDER);exec(compile(authenticated(PROVIDER,PIN),str(PROVIDER),'exec'),c.__dict__)
h=c.h;m=h.m
ETA={(0,2):F(3,2),(0,1):F(-3),(1,1):F(3),(3,0):F(1,2),(1,0):F(-3,2),(0,0):F(1)}
def product_poly(p,q):
 out={}
 for (r,z),a in p.items():
  for (s,w),b in q.items():c.add(out,(r+s,z+w),a*b)
 return out

def decide(vectors,target):
 basis=[];indices=[]
 for i,row in enumerate(vectors):
  if m.rank(basis+[row])>len(basis):basis.append(row);indices.append(i)
 relation=m.relation(basis,target) if basis else ([] if not any(target) else None)
 if relation is not None:
  if [sum(v*b[i] for v,b in zip(relation,basis)) for i in range(len(target))]!=target:raise ValueError('membership reconstruction')
  return {'decision':'AREA_TEST_FAILS_MEMBERSHIP','span_rank':len(basis),'rank_with_V6':len(basis),'basis_indices':indices,'membership_coefficients':list(map(str,relation)),'strict_area_obstruction_proved':False}
 cols=list(zip(*(basis+[target])));rhs=[F(0)]*len(basis)+[F(1)];weights=m.relation([list(v) for v in cols],rhs)
 if weights is None or any(sum(w*x for w,x in zip(weights,row)) for row in vectors) or sum(w*x for w,x in zip(weights,target))!=1:raise ValueError('annihilator verification')
 return {'decision':'DIRECT_SOURCE_ANNIHILATOR_FOUND','span_rank':len(basis),'rank_with_V6':len(basis)+1,'basis_indices':indices,'covector':list(map(str,weights)),'value_on_V6':'1','strict_area_obstruction_proved':False,'hand_transfer_review_required':True}

def run():
 saved=json.loads(authenticated(SAVED,SAVED_PIN));ctx=h.Quotient(9,4);top=[i for i,f in enumerate(ctx.states) if len(f)==4];coords=[(9,4,ctx.states[i],m.orbit_size(ctx.states[i]),0) for i in top]
 left=ctx.project(ctx.e,9);Rleft=m.apply(left,ctx.r);D=ctx.project(Rleft,4)
 products={k:ctx.project(m.apply(ctx.project(Rleft,k),ctx.r),4) for k in range(4,10)}
 if products[4]!=[8*x for x in D] or products[9]!=[168*x for x in D] or any(products[5]) or any(products[8]) or not any(products[6]):raise ValueError('accepted chain identities')
 for k,row in products.items():
  old={tuple(saved['orbits'][v['orbit_index']]['shape']):F(v['coefficient_per_labelled_forest']) for v in saved['all_intermediate_products'][str(k)]}
  if any(row[i]/m.orbit_size(ctx.states[i])!=old.get(ctx.states[i],F(0)) for i in top):raise ValueError('saved full-block mismatch')
 raw=c.coefficients(ctx,coords,6);terms={d:{} for d in (3,4,5,6)}
 for j,p in enumerate(raw):
  if any(e<3 for e,r,z in p):raise ValueError('lower calibration')
  for (e,r,z),v in p.items():
   if (r,z) not in terms[e]:terms[e][r,z]=[F(0)]*len(top)
   terms[e][r,z][j]=v
 dvec=[D[i]/m.orbit_size(ctx.states[i]) for i in top]
 expected={key:[a*x for x in dvec] for key,a in ETA.items() if any(dvec)}
 if terms[3]!=expected:raise ValueError('complete cubic polynomial')
 r2=ctx.project(m.apply(Rleft,ctx.r),4);r2=[r2[i]/m.orbit_size(ctx.states[i]) for i in top]
 g6={key:list(v) for key,v in terms[6].items()}
 for key,a in product_poly(ETA,ETA).items():
  row=g6.setdefault(key,[F(0)]*len(top));g6[key]=[x-a*y/2 for x,y in zip(row,r2)]
 g6={key:v for key,v in g6.items() if any(v)}
 labels=[];vectors=[]
 for family,polys in [('C3',terms[3]),('C4',terms[4]),('C5',terms[5]),('g6',g6)]:
  for key,row in sorted(polys.items()):
   if any(row):labels.append({'family':family,'rho_degree':key[0],'z_degree':key[1]});vectors.append(row)
 v6=[products[6][i]/m.orbit_size(ctx.states[i]) for i in top]
 out={'schema':'sixth-chronological-source-test-v1','provider_sha256':PIN,'saved_lossless_result_sha256':SAVED_PIN,'coordinates':[{'shape':list(f),'multiplicity':mult} for n,j,f,mult,w in coords],'lower_and_direct_log_labels':labels,'lower_and_direct_log_arrays':[list(map(str,v)) for v in vectors],'raw_C6':[{'rho_degree':key[0],'z_degree':key[1],'values':list(map(str,v))} for key,v in sorted(terms[6].items())],'intermediate_products':{str(k):[str(row[i]/m.orbit_size(ctx.states[i])) for i in top] for k,row in products.items()},'full_source_or_master_return_proved':False,'original_G4_closed':False,'other_blocks_or_caps_examined':False}
 out.update(decide(vectors,v6));return out
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
