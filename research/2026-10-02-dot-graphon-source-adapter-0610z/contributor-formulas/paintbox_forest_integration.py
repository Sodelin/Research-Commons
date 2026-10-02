#!/usr/bin/env python3
"""Exact implementation of Shapira--Tyomkyn finite construction and literal
club-to-completed-Kingman-arm adapter. The adapter is a RELAXATION, not admitted.
Author: GPT-6.1 Sol / continue_g_research, 2026-10-02.
"""
from pathlib import Path
from fractions import Fraction
from itertools import product,combinations
from collections import defaultdict
from functools import lru_cache
from math import comb,factorial
import hashlib,json,time,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
root=Path(__file__).parent;start=time.monotonic();p,z=S.symbols('p z');c=S.symbols('c0:4')
# Fresh pair-merger recursion, retaining current trees/opaque subtrees.
def leafset(t):return (t,) if isinstance(t,int) else tuple(sorted(leafset(t[0])+leafset(t[1])))
def tree(a,b):return (a,b) if min(leafset(a))<min(leafset(b)) else (b,a)
def forest(ts):return tuple(sorted(ts,key=lambda t:min(leafset(t))))
@lru_cache(None)
def completed(labels):
 if not labels:return {():S.Integer(1)}
 law={tuple(labels):S.Integer(1)}
 for n in range(len(labels),1,-1):
  out=defaultdict(lambda:S.Integer(0))
  for f,m in law.items():
   for i,j in combinations(range(n),2):
    ff=forest([t for k,t in enumerate(f) if k not in (i,j)]+[tree(f[i],f[j])]);out[ff]+=m/S.Integer(comb(n,2))
  law=dict(out)
 return law

def paintbox(n,weights):
 law=defaultdict(lambda:S.Integer(0));R=len(weights)
 for assignment in product(range(R),repeat=n):
  bins=[tuple(i for i in range(n) if assignment[i]==j) for j in range(R)]
  mass=S.prod(weights[j]**len(bins[j]) for j in range(R))
  arms=[completed(labels) for labels in bins]
  for outcomes in product(*(tuple(arm.items()) for arm in arms)):
   f=forest(t for (ff,_) in outcomes for t in ff)
   law[f]+=mass*S.prod(m for _,m in outcomes)
 return {f:S.Poly(S.expand(v),*weights) for f,v in law.items()}

L=paintbox(4,c);mass=lambda pred:S.expand(sum(v.as_expr() for f,v in L.items() if pred(f)))
P1=mass(lambda f:len(f)==1);P2=mass(lambda f:len(f)==2)
T=mass(lambda f:len(f)==2 and all(len(leafset(t))==2 for t in f))
W=mass(lambda f:len(f)==1 and len(leafset(f[0][0]))==len(leafset(f[0][1]))==2)
Sj=lambda j:sum(x**j for x in c)
assert S.expand(P1-Sj(4))==0
assert S.expand(T-3*(Sj(2)**2-Sj(4)))==0
assert S.expand(P2-3*Sj(2)**2-4*Sj(1)*Sj(3)+7*Sj(4))==0
C=S.expand(T-P2/3);H=S.expand(W-P1/3)
assert S.expand(C-2*Sj(2)**2+S.Rational(4,3)*Sj(1)*Sj(3)+S.Rational(2,3)*Sj(4))==0
assert H==0
assert S.expand(mass(lambda f:True)-Sj(1)**4)==0
# Full labelled balanced-tree coordinate also checked from raw merger histories.
balanced=(tree(tree(0,1),tree(2,3)),)
assert S.expand(L[balanced].as_expr()-Sj(4)/9)==0

# Fresh actual graphon C4/clique calculations on the SAME color weights.
cycle=S.expand(sum(S.prod(c[i] for i in aa) for aa in product(range(4),repeat=4)
                if all(aa[i]!=aa[(i+1)%4] for i in range(4))))
assert S.expand(cycle-(Sj(1)**4-4*Sj(1)**2*Sj(2)+4*Sj(1)*Sj(3)+2*Sj(2)**2-3*Sj(4)))==0
for n in (2,3,4):
 law=paintbox(n,c) if n!=4 else L
 no_merger=law[tuple(range(n))].as_expr()
 en=sum(S.prod(c[i] for i in aa) for aa in combinations(range(4),n))
 assert S.expand(no_merger-factorial(n)*en)==0
# Newton identities of the paper, exact symbolic target clique constraints.
e={0:S.Integer(1),1:S.Integer(1)}
for j in (2,3,4):e[j]=p**comb(j,2)/S.Integer(factorial(j))
power={1:S.Integer(1)}
for n in (2,3,4):
 power[n]=S.expand(sum((-1)**(j-1)*e[j]*power[n-j] for j in range(1,n))+(-1)**(n-1)*n*e[n])
Ctarget=S.factor(2*power[2]**2-S.Rational(4,3)*power[3]-S.Rational(2,3)*power[4])
assert S.expand(Ctarget-p*(p-1)**3*(p*p+3*p+6)/9)==0
cycle_target=S.factor(1-4*power[2]+4*power[3]+2*power[2]**2-3*power[4])
assert S.expand(cycle_target-(p*p+p**6)/2)==0
cycle_gap=S.factor(cycle_target-p**4);assert cycle_gap==p**2*(p-1)**2*(p+1)**2/2
ordinaryP1=1-S.Rational(9,5)*p+p**3-p**6/5
assert S.expand((power[4]-ordinaryP1)*S.Rational(10,3)-Ctarget)==0
# Through three inputs full forest orbit totals coincide after target constraints.
assert S.expand(power[2]-(1-p))==0
assert S.expand(power[3]-(1-S.Rational(3,2)*p+p**3/2))==0

# Exact finite root construction p=1/10,k=4, with rational isolating intervals.
p0=S.Rational(1,10);k=4
poly=S.Poly(sum(p0**comb(j,2)*z**j/S.Integer(factorial(j)) for j in range(k+1)),z)
assert poly.count_roots(-S.oo,0)==k
assert poly.count_roots(0,S.oo)==0
intervals=poly.intervals(eps=S.Rational(1,10**22));assert len(intervals)==k
boxes=[]
for (a,b),mult in intervals:
 assert mult==1 and a<b<0 and poly.count_roots(a,b)==1
 clo,chi=-1/a,-1/b
 assert 0<clo<chi<1
 boxes.append({'root_interval':[str(a),str(b)],'weight_interval':[str(clo),str(chi)],'weight_mid_orientation':float((clo+chi)/2)})
boxes.sort(key=lambda x:x['weight_mid_orientation'],reverse=True)
# All-clique identities follow from exact factorization/Vieta, not decimal roots.
coefficients=[str(poly.nth(j)) for j in range(k+1)]
for j in range(1,k):assert poly.nth(j)**2>4*poly.nth(j-1)*poly.nth(j+1)
rec={'status':'PASS_EXACT_ADAPTER_DIAGNOSTIC','source_paper':'https://arxiv.org/abs/2101.08173v2',
 'scope':'literal categorical completed-Kingman-arm paintbox is NOT an admitted positive private binary source; fails full forest at cap4',
 'fresh_complete_labelled_forest_coordinates':len(L),'symbolic_source_identities':['P1=S4','T=3(S2^2-S4)','P2=3S2^2+4S1S3-7S4','H=0','C=2S2^2-4S1S3/3-2S4/3','one_labelled_balanced_probability=S4/9'],
 'target_power_sums':{str(n):str(power[n]) for n in range(1,5)},'full_forest_C':str(Ctarget),
 'C_strict_negative_for_0_p_1':True,'full_labelled_balanced_gap':str(S.factor(Ctarget/30)),
 'graphon_C4_density':str(cycle_target),'graphon_C4_gap_from_constant':str(cycle_gap),
 'finite_fixture':{'p':str(p0),'k':k,'polynomial_coefficients_ascending':coefficients,'negative_simple_root_boxes':boxes,
 'clique_probability_equalities':'j! e_j(c)=p^(j choose2), j=1..4, exact Vieta identity',
 'forest_C':str(Ctarget.subs(p,p0)),'ordinary_P1':str(ordinaryP1.subs(p,p0)),'paintbox_P1':str(power[4].subs(p,p0)),
 'graphon_C4_gap':str(cycle_gap.subs(p,p0))},
 'seconds':time.monotonic()-start,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'sympy':S.__version__}
(root/'paintbox-forest-integration.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2))
