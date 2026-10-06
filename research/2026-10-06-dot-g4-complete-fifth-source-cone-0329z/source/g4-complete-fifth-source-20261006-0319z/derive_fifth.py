"""Complete natural fifth coefficient; no source-parameter or cap search."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import comb,factorial
import hashlib,types,json
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'g4-rare-route-fixed-functional-20261006-0204z/check_rare.py'
PIN='d462babef7afd0b5f6fa6c74328a6df9b2d31576e50e4832caef3c63fe137788'
raw=PROVIDER.read_bytes()
if PROVIDER.is_symlink() or hashlib.sha256(raw).hexdigest()!=PIN:raise ValueError('provider identity')
c=types.ModuleType('_rare_provider');c.__file__=str(PROVIDER);exec(compile(raw,str(PROVIDER),'exec'),c.__dict__)
h=c.h;m=h.m

def addrow(dst,key,row,factor=F(1)):
 if not factor or not any(row):return
 if key not in dst:dst[key]=[F(0)]*len(row)
 dst[key]=[x+factor*y for x,y in zip(dst[key],row)]
 if not any(dst[key]):del dst[key]

def source(ctx,cap):
 split=c.split_coeffs(ctx,ctx.e,cap);rates=tuple(sorted({comb(k,2) for k in range(cap+1)}));B={}
 for a,start in enumerate(split):
  if not any(start):continue
  recovered=[F(0)]*len(start)
  for rate in rates:
   row=c.rare_project(start,ctx.ql,rate,rates);recovered=[x+y for x,y in zip(recovered,row)]
   for p in range(cap-a+1):
    merged=[F(0)]*len(ctx.states)
    for value,(rare,common) in zip(row,ctx.colours):merged[ctx.ids[tuple(sorted(rare+common))]]+=value
    addrow(B,(a+p,rate,p),merged,F(1,factorial(p)))
    if p<cap-a:row=m.apply(row,ctx.qr)
  if recovered!=start:raise ValueError('spectral completeness')
 b=c.pair_series(cap);c.add(b,(0,0,0),F(-1));power={(0,0,0):F(1)};C={}
 for l in range(cap+1):
  for (e,r,z),row in B.items():
   if e+l>cap:continue
   normalized=h.h.positive_binomial(row,ctx.q,l)
   for (f,s,w),v in power.items():
    if e+f<=cap:addrow(C,(e+f,r+s,z+w),normalized,v)
  power=c.mul(power,b,cap)
 return C

def z_operator(ctx):
 out=[]
 for f in ctx.states:
  row={}
  def addff(parts,rest,value):
   ff=tuple(sorted(parts+rest));ix=ctx.ids[ff];row[ix]=row.get(ix,F(0))+value
  for ids in combinations(range(len(f)),4):
   roots=[f[i] for i in ids];rest=[f[i] for i in range(len(f)) if i not in ids]
   for lone in range(4):
    triple=[i for i in range(4) if i!=lone]
    for pair in combinations(triple,2):
     other=next(i for i in triple if i not in pair)
     addff([m.tree(m.tree(roots[pair[0]],roots[pair[1]]),roots[other]),roots[lone]],rest,F(-6))
   for pairs in (((0,1),(2,3)),((0,2),(1,3)),((0,3),(1,2))):
    a=m.tree(roots[pairs[0][0]],roots[pairs[0][1]]);b=m.tree(roots[pairs[1][0]],roots[pairs[1][1]])
    addff([a,b],rest,F(18));addff([m.tree(a,b)],rest,F(2))
   for pair in combinations(range(4),2):
    remaining=[i for i in range(4) if i not in pair]
    for third,last in (remaining,remaining[::-1]):addff([m.tree(m.tree(m.tree(roots[pair[0]],roots[pair[1]]),roots[third]),roots[last])],rest,F(1))
  if sum(row.values()):raise ValueError('Z row sum')
  out.append({i:v for i,v in row.items() if v})
 return out

def lower_rows(ctx):
 q,r=ctx.q,ctx.r;v=ctx.e;Z=z_operator(ctx)
 qv=m.apply(v,q);rv=m.apply(v,r);zv=m.apply(v,Z)
 def diff(a,b):return [x-y for x,y in zip(a,b)]
 ar=diff(m.apply(qv,r),m.apply(rv,q))
 aar=[x-2*y+z for x,y,z in zip(m.apply(m.apply(qv,q),r),m.apply(m.apply(qv,r),q),m.apply(m.apply(rv,q),q))]
 az=diff(m.apply(qv,Z),m.apply(zv,q))
 return {'R':rv,'T':[x+y for x,y in zip(m.apply(qv,q),qv)],'Z':zv,'adR':ar,'ad2R':aar,'adZ':az}

ETA={(0,2):F(3,2),(0,1):F(-3),(1,1):F(3),(3,0):F(1,2),(1,0):F(-3,2),(0,0):F(1)}
def run():
 coords=[];lower={name:[] for name in ('R','T','Z','adR','ad2R','adZ')};blocks=[];monomials=set()
 for n in range(1,6):
  ctx=h.Quotient(n,1);C=source(ctx,5);L=lower_rows(ctx)
  if C.get((0,0,0))!=ctx.e or any(e in (1,2) for e,r,z in C):raise ValueError('lower calibration')
  expected={}
  for (r,z),v in ETA.items():addrow(expected,(3,r,z),L['R'],v)
  if {key:row for key,row in C.items() if key[0]==3}!=expected:raise ValueError('complete cubic identity')
  fifth={(r,z):row for (e,r,z),row in C.items() if e==5};monomials.update(fifth)
  blocks.append((ctx,fifth))
  for i,f in enumerate(ctx.states):
   mult=m.orbit_size(f);coords.append({'arity':n,'shape':list(f),'labelled_multiplicity':mult})
   for name,row in L.items():lower[name].append(row[i]/mult)
 columns={key:[] for key in sorted(monomials)}
 for ctx,fifth in blocks:
  for key in columns:
   row=fifth.get(key,[F(0)]*len(ctx.states));columns[key].extend(v/m.orbit_size(f) for v,f in zip(row,ctx.states))
 basis=[];labels=[]
 for name,row in lower.items():
  if m.rank(basis+[row])>len(basis):basis.append(row);labels.append({'lower_operator':name})
 lower_rank=len(basis)
 for key,row in columns.items():
  if m.rank(basis+[row])>len(basis):basis.append(row);labels.append({'fifth_monomial':list(key)})
 quotient=[];relations=[]
 for key,row in columns.items():
  rel=m.relation(basis,row)
  if rel is None or [sum(v*b[i] for v,b in zip(rel,basis)) for i in range(len(row))]!=row:raise ValueError('exact quotient reconstruction')
  relations.append({'rho_degree':key[0],'z_degree':key[1],'basis_coefficients':list(map(str,rel))})
  if any(rel[lower_rank:]):quotient.append({'rho_degree':key[0],'z_degree':key[1],'quotient_coefficients':list(map(str,rel[lower_rank:]))})
 return {'schema':'complete-natural-fifth-v1','provider_sha256':PIN,'empty_arity_fifth_and_lower_operators_zero':True,'complete_coordinates':coords,'lower_operators':{k:list(map(str,v)) for k,v in lower.items()},'fifth_coefficient_arrays':[{'rho_degree':k[0],'z_degree':k[1],'values':list(map(str,v))} for k,v in columns.items()],'basis_labels':labels,'lower_rank':lower_rank,'total_rank':len(basis),'quotient_dimension':len(basis)-lower_rank,'all_exact_relations':relations,'actual_source_quotient_polynomial':quotient,'cone_decided':False,'fifth_order_balance_proved':False,'original_G4_closed':False,'parameter_search_performed':False}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
