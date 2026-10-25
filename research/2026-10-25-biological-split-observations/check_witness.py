"""Exact arithmetic and combinatorial checks of the stated witness, not a coalescent simulator."""
from fractions import Fraction as F
import json
edges=[('R','U'),('R','D'),('U','V'),('U','H'),('V','C'),('V','H'),('H','W'),('W','A'),('W','B')]
leaves=set('ABCD')
def displayed_splits(chosen, rename):
    es=[(rename.get(a,a),rename.get(b,b)) for a,b in edges if not (b=='H' and a!=chosen)]
    adj={}
    for a,b in es: adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
    splits=set()
    for a,b in es:
        seen={a}; todo=[a]
        while todo:
            v=todo.pop()
            for w in adj[v]:
                if {v,w}=={a,b} or w in seen:continue
                seen.add(w);todo.append(w)
        x=seen&leaves;y=leaves-x
        if len(x)>1 and len(y)>1:splits.add('|'.join(sorted((''.join(sorted(x)),''.join(sorted(y))))))
    return sorted(splits)
g=F(1,2);a=b=F(9,10);c=F(1,10);z=F(40,47)
conditional=g*g*(1-F(2,3)*a)+(1-g)**2*(1-F(2,3)*b)+2*g*(1-g)*c/3
p=1-z+z*conditional
u=g*g*a+g*(1-g)*(3-c)+(1-g)**2*b
assert conditional==F(13,60) and u==F(47,40) and z*u==1
assert p==F(1,3) and (1-p)/2==F(1,3)
result={'method':'Exact Fraction arithmetic plus exhaustive two-switching edge-split enumeration; no simulation, external package, or formal verification', 'parameters':{'gamma':str(g),'UH_survival':str(a),'VH_survival':str(b),'UV_survival':str(c),'HW_survival':str(z)},'conditional_AB_probability':str(conditional),'published_formula_u':str(u),'quartet_law':[str(p),str((1-p)/2),str((1-p)/2)],'original_switchings':{h:displayed_splits(h,{}) for h in ('U','V')},'B_C_relabelled_switchings':{h:displayed_splits(h,{'B':'C','C':'B'}) for h in ('U','V')}}
assert all(x==['AB|CD'] for x in result['original_switchings'].values())
assert all(x==['AC|BD'] for x in result['B_C_relabelled_switchings'].values())
print(json.dumps(result,indent=2))
