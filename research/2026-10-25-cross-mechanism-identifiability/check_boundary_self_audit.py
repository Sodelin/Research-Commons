"""Bounded exact controls, not a proof of history identifiability."""
from itertools import product
import json

def killed(Q, lam, n):
    states=list(product(range(len(Q)), repeat=n)); ix={a:i for i,a in enumerate(states)}
    K=[[0]*len(states) for _ in states]
    for a,i in ix.items():
        for u in range(n):
            for j in range(len(Q)):
                if j!=a[u]:
                    b=list(a); b[u]=j; K[i][ix[tuple(b)]]+=Q[a[u]][j]
            K[i][i]+=Q[a[u]][a[u]]
        K[i][i]-=sum(lam[a[u]] for u in range(n) for v in range(u) if a[u]==a[v])
    return states,K

def conjugate(Q,lam,pi):
    d=len(pi); inv=[pi.index(i) for i in range(d)]
    return [[Q[inv[i]][inv[j]] for j in range(d)] for i in range(d)], [lam[inv[i]] for i in range(d)]

out=[]
for tag,Q,lam in [('equal_rate_symmetric',[[-1,1],[1,-1]],[2,2]),('equal_rate_asymmetric',[[-1,1],[3,-3]],[2,2]),('distinct_rates',[[-1,1],[3,-3]],[2,5])]:
    pi=[1,0]; R,mu=conjugate(Q,lam,pi)
    for n in range(1,5):
        states,K=killed(Q,lam,n); _,J=killed(R,mu,n); ix={a:i for i,a in enumerate(states)}
        p=[ix[tuple(pi[x] for x in a)] for a in states]
        assert all(K[i][j]==J[p[i]][p[j]] for i in range(len(states)) for j in range(len(states)))
        raw_swap_equal=all(K[i][j]==K[p[i]][p[j]] for i in range(len(states)) for j in range(len(states)))
        if tag=='equal_rate_symmetric': assert raw_swap_equal
        else: assert not raw_swap_equal
        out.append(dict(case=tag,n=n,dimension=len(states),conjugated_intertwining=True,unconjugated_swap_silent=raw_swap_equal))
# A ghost activates by a migration edge while its boundary column stays zero.
Q=[[-3,3],[0,0]]; lam=[2,7]; states,K=killed(Q,lam,2)
v=[lam[a[0]] if a[0]==a[1] else 0 for a in states]
i=states.index((0,0)); derivative=sum(K[i][j]*v[j] for j in range(len(states)))
assert v[i]==2 and derivative==-16 and derivative!=-(2**2)
out.append(dict(case='zero_column_ghost_activation',initial_density=v[i],density_derivative=derivative,null_derivative=-4,visible=True))
# Grouping silent swaps does not change the transported later routing.
B=[[1,0],[1,0]]
for swaps in range(6):
    composed=[0,1]
    for _ in range(swaps): composed=[1-x for x in composed]
    direct=[B[composed[i]] for i in range(2)]
    grouped=[B[i if swaps%2==0 else 1-i] for i in range(2)]
    assert direct==grouped
    out.append(dict(case='grouped_silent_swaps',count=swaps,effective_routing=direct))
print(json.dumps({'status':'all exact bounded controls passed','controls':out,'limitations':'No all-panel equivalence search; no full-history theorem checked.'},indent=2))
