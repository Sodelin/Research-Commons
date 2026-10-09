"""Bounded exact regression tests. No full graph-admission/compiler claim."""
from dataclasses import replace
from fractions import Fraction as Q
from itertools import product
from natural_cell_feasibility import *
from rational_affine_feasibility import ResourceLimit
import json

results=[]
def check(name,condition):
    assert condition,name
    results.append({'test':name,'pass':True})

# Independently derived one-variable interval criterion, including strict ties.
onevar=[]
for a,b,strict in product((-1,0,1),(-1,0,1),(False,True)):
    onevar.append(Row((a,),b,strict))
for r,s in product(onevar,repeat=2):
    rows=(r,s)
    impossible=any(x.a[0]==0 and not x.holds((0,)) for x in rows)
    lo=[(x.b/x.a[0],x.strict) for x in rows if x.a[0]<0]
    hi=[(x.b/x.a[0],x.strict) for x in rows if x.a[0]>0]
    for l,ls in lo:
        for h,hs in hi:
            impossible |= l>h or (l==h and (ls or hs))
    assert (solve(rows,1) is None)==impossible
check('324 exact one-variable systems vs independent endpoint test',True)

# Small supplied calendar charts only; no assertion that these are admitted
# n>=4 biological networks. This isolates joint-bank arithmetic.
node=lambda x:Atom(node=x)
cut=lambda x:Atom(cut=Q(x))
eq=lambda x:Interval(Bound(Q(x)),Bound(Q(x)))
base=Chart(nodes=('old','young'),populations=('edge','ancestral'),hybrids=('h',),
    edges=(('edge','old','young'),),tips=('young',),
    orders=(Order(node('old'),cut(2),'='),),
    exposures=(Exposure('edge',cut(0),cut(1),eq(1)),Exposure('edge',cut(1),cut(2),eq(1))),
    coins=(('h',eq(Q(1,3))),))
w=solve_chart(base)
check('two finite epochs use one rate and rational gamma',w is not None and w['rates']['edge']==1 and w['gammas']['h']==Q(1,3))
bad=replace(base,exposures=(base.exposures[0],replace(base.exposures[1],cell=eq(2))))
check('individually feasible rows jointly impossible under one rate',solve_chart(bad) is None)
variable=replace(base,orders=(Order(cut(1),node('old'),'<'),),
    exposures=(Exposure('edge',node('young'),node('old'),eq(3)),))
w=solve_chart(variable)
check('variable original age reconstructs exact positive rational rate',w is not None and w['rates']['edge']*w['ages']['old']==3)
saturated=replace(base,exposures=(Exposure('edge',cut(0),cut(1),Interval(Bound(Q(100)),None)),))
check('saturated cell has no artificial upper bound',solve_chart(saturated)['rates']['edge']>=100)
strictbad=replace(base,coins=(('h',Interval(Bound(Q(1,3),True),Bound(Q(1,3)))),))
check('strict singleton contradiction',solve_chart(strictbad) is None)
ancestral=replace(base,exposures=(Exposure('ancestral',cut(2),cut(3),eq(1)),Exposure('ancestral',cut(3),cut(5),eq(2))))
check('one ancestral rate across distinct finite intervals',solve_chart(ancestral)['rates']['ancestral']==1)
try:
    solve_chart(base,max_pairs=0)
except ResourceLimit:
    check('resource ceiling is UNKNOWN exception',True)
else:raise AssertionError('ceiling must be reached')
# An explicit admitted four-tip rooted binary tree (no hybrids). The fixed
# calendar is root=3, the two cherries=1, and all four tips=0. The cut at2
# splits each root-to-cherry physical edge into two finite exposures.
node_ages={'root':3,'left':1,'right':1,'a':0,'b':0,'c':0,'d':0}
edges=(('rl','root','left'),('rr','root','right'),('la','left','a'),
       ('lb','left','b'),('rc','right','c'),('rd','right','d'))
exposures=[]
for e,older,younger in edges:
    if older=='root':
        exposures.extend((Exposure(e,cut(1),cut(2),eq(1)),Exposure(e,cut(2),cut(3),eq(1))))
    else:exposures.append(Exposure(e,cut(0),cut(1),eq(1)))
exposures.append(Exposure('ancestral',cut(3),cut(4),eq(2)))
tree=Chart(tuple(node_ages),tuple(e[0] for e in edges)+('ancestral',),(),edges,
    ('a','b','c','d'),tuple(Order(node(v),cut(t),'=') for v,t in node_ages.items()),
    tuple(exposures),())
w=solve_chart(tree,max_pairs=100000)
check('explicit four-tip binary-tree chart with original cut-crossing rates',
      w is not None and all(w['rates'][e[0]]==1 for e in edges) and w['rates']['ancestral']==2)
print(json.dumps({'status':'BOUNDED_EXACT_TESTS_PASS','tests':results,'scope':'unit-level affine solver and supplied-chart arithmetic; no full source admission, observation cloud or Lean correctness claim'},indent=2))
