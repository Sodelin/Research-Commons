"""Independent exact Shapira--Tyomkyn finite-construction integration check.
The categorical infinite-arm model is a DELIBERATE non-admitted relaxation.
The ordinary comparison uses actual finite-time uniform Kingman pair rates.
Contributor: dot / continue_lean_proofs_two, 2026-10-02.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
from collections import defaultdict,Counter
import math,json,time,hashlib
import sympy as S
P=Path(__file__).parent;t=time.monotonic();p=S.symbols('p');fixture=S.Rational(1,10)

def canon(items):return tuple(sorted(items,key=repr))
def merge(forest,i,j):return canon([tree for k,tree in enumerate(forest) if k not in (i,j)]+[canon([forest[i],forest[j]])])
def partitions(items):
 items=list(items)
 if not items:yield ();return
 for sub in partitions(items[1:]):
  yield ((items[0],),)+sub
  for k in range(len(sub)):yield sub[:k]+((items[0],)+sub[k],)+sub[k+1:]

def ordinary(labels):
 """Exact ODE solution by distinct-count exponential coefficients.
 Off-diagonal rates are ONE per unordered current-root pair; no fitted table.
 """
 n=len(labels);start=canon(labels);layers={n:{start}};pred=defaultdict(Counter)
 for r in range(n,1,-1):
  nxt=set()
  for state in layers[r]:
   for i,j in combinations(range(r),2):
    after=merge(state,i,j);nxt.add(after);pred[after][state]+=1
  layers[r-1]=nxt
 coeff={start:{math.comb(n,2):F(1)}}
 for r in range(n-1,0,-1):
  lam=math.comb(r,2)
  for state in layers[r]:
   incoming=defaultdict(F)
   for before,multiplicity in pred[state].items():
    for exponent,c in coeff[before].items():incoming[exponent]+=multiplicity*c
   solved={exponent:c/F(lam-exponent) for exponent,c in incoming.items() if c}
   solved[lam]=-sum(solved.values(),F(0));coeff[state]=solved
 law={state:S.expand(sum(S.Rational(c.numerator,c.denominator)*p**exponent for exponent,c in cs.items())) for state,cs in coeff.items()}
 assert S.expand(sum(law.values()))==1
 return law

# Independent Newton power sums from required clique coordinates, not the
# researcher's closed formula for C.
e={0:S.Integer(1)}
for j in range(1,5):e[j]=p**math.comb(j,2)/S.factorial(j)
powers={}
for j in range(1,5):
 powers[j]=S.expand(sum((-1)**(i-1)*e[i]*powers[j-i] for i in range(1,j))+(-1)**(j-1)*j*e[j])

def injective_color_mass(sizes):
 """Möbius inversion of distinct club choices via equality partitions.
 Thus no numeric root weights or hand aggregate formulas are used.
 """
 total=0
 for sigma in partitions(range(len(sizes))):
  mobius=math.prod((-1)**(len(block)-1)*math.factorial(len(block)-1) for block in sigma)
  total+=mobius*math.prod(powers[sum(sizes[i] for i in block)] for block in sigma)
 return S.expand(total)

def relaxed_club_law(labels):
 law=defaultdict(lambda:S.Integer(0))
 for occupied in partitions(labels):
  mass=injective_color_mass([len(block) for block in occupied])
  trees=[]
  for block in occupied:
   final={state[0]:expr.subs(p,0) for state,expr in ordinary(block).items() if len(state)==1}
   assert sum(final.values())==1
   trees.append(list(final.items()))
  for selections in product(*trees):
   forest=canon(tree for tree,weight in selections)
   law[forest]+=mass*math.prod(weight for tree,weight in selections)
 law={state:S.expand(expr) for state,expr in law.items()};assert S.expand(sum(law.values()))==1
 return law

def leaves(tree):
 if isinstance(tree,int):return (tree,)
 return leaves(tree[0])+leaves(tree[1])
def two_cherries(state):return len(state)==2 and all(len(leaves(tree))==2 for tree in state)
def balanced(state):return len(state)==1 and isinstance(state[0],tuple) and all(len(leaves(child))==2 for child in state[0])

prefix=[]
for n in range(1,5):
 a=ordinary(tuple(range(n)));b=relaxed_club_law(tuple(range(n)));assert a.keys()==b.keys()
 assert all(expr.subs(p,fixture)>=0 for expr in a.values()) and all(expr.subs(p,fixture)>=0 for expr in b.values())
 noA=a[canon(range(n))];noB=b[canon(range(n))];assert S.expand(noA-noB)==0
 mismatches=[repr(state) for state in a if S.expand(a[state]-b[state])!=0]
 prefix.append({'n':n,'full_labelled_forests':len(a),'exact_no_merger_matches':True,'full_forest_mismatches':len(mismatches)})
 if n<=3:assert not mismatches
 else:
  def aggregate(law,pred):return S.expand(sum(expr for state,expr in law.items() if pred(state)))
  P1=aggregate(b,lambda f:len(f)==1);P2=aggregate(b,lambda f:len(f)==2);T=aggregate(b,two_cherries);W=aggregate(b,balanced)
  C=S.factor(T-P2/3);H=S.factor(W-P1/3)
  assert C==p*(p-1)**3*(p*p+3*p+6)/9 and H==0
  assert S.factor(aggregate(a,two_cherries)-aggregate(a,lambda f:len(f)==2)/3)==0
  tv=S.Rational(1,2)*sum(abs((a[state]-b[state]).subs(p,fixture)) for state in a)
  assert tv==(-S.Rational(6,5)*C).subs(p,fixture)
  full=[{'forest':repr(state),'ordinary':str(a[state].subs(p,fixture)),'relaxed_club':str(b[state].subs(p,fixture))} for state in sorted(a,key=repr)]

# Exact finite paper polynomial root certificates. These prove legitimate
# weighted k-partite GRAPHON weights, not finite positive population arms.
z=S.symbols('z');roots=[]
for k in range(2,9):
 poly=S.Poly(sum(fixture**math.comb(j,2)*z**j/S.factorial(j) for j in range(k+1)),z)
 assert poly.count_roots(-S.oo,0)==k and S.gcd(poly,poly.diff()).degree()==0
 rec={'k':k,'polynomial_coefficients_descending':list(map(str,poly.all_coeffs())),'strict_negative_real_roots':k,'all_roots_simple':True,'exact_clique_coordinates':[str(fixture**math.comb(j,2)) for j in range(1,k+1)],'next_clique_coordinate':0}
 if k==4:
  intervals=poly.intervals(eps=S.Rational(1,10**16));assert all(mult==1 and lo<hi<0 for (lo,hi),mult in intervals)
  rec['exact_part_weight_isolators']=[{'lower':str(-1/lo),'upper':str(-1/hi)} for (lo,hi),mult in intervals]
 roots.append(rec)

# Four two-bit product probabilities satisfy e1^2*e4=e3^2:
# pair them so that w00*w11=w01*w10=v. Then e3=v*e1, e4=v^2.
weight_obstruction=S.factor(e[1]**2*e[4]-e[3]**2);assert weight_obstruction==p**6/72
result={'status':'PASS_INDEPENDENT_EXACT_CHECKS','context_utc':'2026-10-02T06:02:00Z','model_scope':'Categorical clubs with infinite within-club coalescence are NON-ADMITTED; ordinary comparison is finite positive Kingman E(p).','fixture_p':str(fixture),'prefix_full_forest_checks':prefix,'newton_power_sums':{str(k):str(v) for k,v in powers.items()},'relaxed_full_forest_C':str(C),'relaxed_full_forest_H':str(H),'C_at_fixture':str(C.subs(p,fixture)),'full_four_forest_TV':str(tv),'full_four_forest_coordinates':full,'finite_graphon_root_checks':roots,'four_part_product_weight_obstruction':str(weight_obstruction),'weight_obstruction_at_fixture':str(weight_obstruction.subs(p,fixture)),'strict_source_graphon_entry_lower_bound':'Z times product_i min(x_i,y_i)>0; forbids positive-measure zero blocks','serial_graphon_rank':'2^L for L finite strict binary bigons; arbitrary graphon part counts/weights are not free','not_claimed':['finite positive biological realization of paper graphons','full-forest all-prefix replica','unrestricted G4 stopping obstruction','whole G3 recognition','Lean verification'],'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-t}
(P/'independent-graphon-forest-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['full_four_forest_coordinates','finite_graphon_root_checks']},indent=2))
