"""Exact tree controls for the written c>1 every-order obstruction."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json
from twin_normalization_review import ex, distance, all_orders

def main():
    pairs=[('a','U'),('b','U'),('U','root'),('root','V'),('V','z'),('V','W'),('W','x'),('W','y')]
    edges={ex.edge(*p) for p in pairs};adj=ex.adjacency(edges)
    net=ex.Net(edges,set('abxyz'),{},'root',{v:sorted(ns) for v,ns in adj.items()},'tree-double-cherry')
    admission=net.validate();labels=sorted(net.leaves);qs,trees=ex.quartet_system(net)
    original=distance(qs,labels,0,1,F(1,2),1)
    controls=[]
    for c in (F(101,100),F(2),F(10)):
        d=distance(qs,labels,c,1,0,1)
        for x,y in combinations(labels,2):
            assert d[x,y]==12*c+(1-c)*original[x,y]
        contrasts=[]
        for x,y in combinations('xyz',2):
            t=d['a','b']+d[x,y]-d['a',x]-d['b',y]
            assert t==d['a','b']+d[x,y]-d['a',y]-d['b',x]>0
            contrasts.append(str(t))
        orders=list(all_orders(labels));valid=[];n=len(labels)
        for order in orders:
            if all(d[order[i],order[j]]+d[order[(i+1)%n],order[(j+1)%n]]
                   -d[order[i],order[(j+1)%n]]-d[order[(i+1)%n],order[j]]>=0
                   for i,j in combinations(range(n),2)):
                valid.append(order)
        assert len(orders)==12 and not valid
        controls.append({'c':str(c),'strict_twin_contrasts':contrasts,'orders_checked':12,'valid_orders':valid})
    report={'status':'PASS_TREE_UPPER_BOUNDARY_REPLAY','admission':admission,
            'displayed_trees':len(trees),'labels':labels,'controls':controls,
            'scope':'Finite arithmetic corroboration of all-real c>1 hand argument; inherited graph checker; no Lean execution.'}
    (Path(__file__).parent/'tree-boundary-review.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'controls':len(controls),'orders_each':12}))

if __name__=='__main__':main()
