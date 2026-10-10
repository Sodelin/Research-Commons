from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
lam=lambda n:n*(n-1)//2
@lru_cache(None)
def killed_eppf(s,q):
    if not s:return F(1)
    # Counts of surviving roots within each specified final block; all cross-block
    # mergers are killed. No exchangeable-partition normalization formula is used.
    states=sorted(product(*(range(1,x+1) for x in s)), key=sum, reverse=True)
    pol={s:{lam(sum(s)):F(1)}}
    for a in states:
        if a==s:continue
        inflow={}
        for i in range(len(s)):
            if a[i]<s[i]:
                b=tuple(x+(j==i) for j,x in enumerate(a))
                for power,c in pol[b].items():inflow[power]=inflow.get(power,F(0))+lam(b[i])*c
        l=lam(sum(a));v={power:-c/F(power-l) for power,c in inflow.items() if c}
        v[l]=-sum(v.values(),F(0));pol[a]=v
    return sum(c*q**power for power,c in pol[(1,)*len(s)].items())
def cell(s,q,g):
    # A final block has a single original arm; independent initial routing then
    # gives these g^mass weights. Within each arm use the killed source process.
    ans=F(0)
    for bits in product((0,1),repeat=len(s)):
        a=tuple(x for x,b in zip(s,bits) if b); b=tuple(x for x,z in zip(s,bits) if not z)
        ans+=g**sum(a)*(1-g)**sum(b)*killed_eppf(a,q)*killed_eppf(b,q)
    return ans
q=F(1,5);g=F(17,50)
patterns=[(2,2,1,1),(3,1,1,1),(3,2,1,1),(4,1,1,1)]
rows={','.join(map(str,s)):cell(s,q,g) for s in patterns}
d=(3*rows['2,2,1,1']-2*rows['3,1,1,1'])/9
e=(2*rows['3,2,1,1']-rows['4,1,1,1'])/6
assert d==F(5926106296,50067901611328125) and e==F(-25054764879056,156462192535400390625)
assert d>0 and e<0
# Source controls, same cap: deterministic routing boundary recovers ordinary;
# arm reversal; one-block and all-singleton probabilities; t=0 all singletons.
for s in patterns:
    assert cell(s,q,g)==cell(s,q,1-g)
    assert cell(s,q,F(1))==killed_eppf(s,q)
    assert killed_eppf(s,F(1))==F(all(x==1 for x in s))
for n in range(1,8):
    assert killed_eppf((1,)*n,q)==q**lam(n)
assert killed_eppf((2,),q)==1-q
out={'status':'EXACT_PASS','q':str(q),'g':str(g),'method':'killed multi-block Kingman ODE, rational q-polynomial coefficients','block_probabilities':{k:str(v) for k,v in rows.items()},'d6':str(d),'e':str(e),'product_negative':d*e<0,'max_input_roots':7,'controls':'arm symmetry, deterministic-route boundary, t=0, singleton survival, two-root merger','scope':'one actual equal-arm IID cell; no global sign or master closure'}
body=json.dumps(out,indent=2)+'\n';Path(__file__).with_name('RESULT.json').write_text(body);print(body,end='')
