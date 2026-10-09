from fractions import Fraction as Q
from dataclasses import replace
from rational_affine_feasibility import Row,solve
from natural_cell_feasibility import Atom,Bound,Interval,Exposure,Order,Chart,solve_chart
import json
checks=[]
def test(name,p):
 assert p,name
 checks.append(name)
# x=y, x>=0, y<0: contradiction must survive strict projection.
test('strict two-dimensional projected contradiction',solve([Row((1,-1),0),Row((-1,1),0),Row((-1,0),0),Row((0,1),0,True)],2) is None)
# x=y=1/3: collapsed bounds must be reconstructed exactly.
test('weak singleton after two-dimensional projection',solve([Row((1,-1),0),Row((-1,1),0),Row((1,0),Q(1,3)),Row((-1,0),-Q(1,3))],2)==(Q(1,3),Q(1,3)))
n=lambda s:Atom(node=s)
c=lambda q:Atom(cut=Q(q))
eq=lambda q:Interval(Bound(Q(q)),Bound(Q(q)))
base=Chart(('r','a'),('e','anc'),('h',),(('e','r','a'),),('a',),(Order(n('r'),c(2),'='),),(Exposure('e',c(1),c(1),eq(0)),),(('h',eq(Q(1,3))),))
test('zero epoch allowed inside positive physical edge',solve_chart(base) is not None)
test('zero epoch cannot have positive saturated hazard',solve_chart(replace(base,exposures=(Exposure('e',c(1),c(1),Interval(Bound(Q(1)),None)),))) is None)
test('physical edge cannot collapse despite zero hazard epoch',solve_chart(replace(base,orders=(Order(n('r'),c(0),'='),))) is None)
test('shared inheritance contradictions remain joint',solve_chart(replace(base,coins=(('h',eq(Q(1,3))),('h',eq(Q(2,3)))))) is None)
test('strict endpoint gamma zero rejected',solve_chart(replace(base,coins=(('h',eq(0)),))) is None)
print(json.dumps({'status':'PASS','checks':checks,'scope':'seven independent exact adversarial unit controls; supplied-chart arithmetic only'},indent=2))
