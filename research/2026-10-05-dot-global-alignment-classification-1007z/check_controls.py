#!/usr/bin/env python3
"""Exact structural controls, not a substitute for the general hand proof."""
import itertools,json,hashlib
from fractions import Fraction as F
from math import comb

def build(support,R):
    h=len(support); K=[None]*h
    K[-1]=[[int(x) for x in row] for row in support[-1]]
    for j in range(h-1,0,-1):
        old,new=len(support[j-1]),len(support[j-1][0]); U=0; cols=[]
        for i in range(new):
            inc=sum(support[j-1][a][i] for a in range(old))
            C=sum(K[j][i])+R*sum(support[j][i])
            b=max(inc,2**C*(U+3)+1); cols.append(b); U+=b+R*inc
        K[j-1]=[[int(x) for x in row] for row in support[j-1]]
        for i,b in enumerate(cols):
            a=next(a for a in range(old) if support[j-1][a][i])
            K[j-1][a][i]+=b-sum(K[j-1][a][i] for a in range(old))
    return K

def weights(K,j):
    result=[]; running=0
    for i,row in enumerate(K[j]):
        c=sum(row); B=sum(row0[i] for row0 in K[j-1]); start=running; block=[]
        for _ in range(c-1):
            w=running+3; block.append(w); running+=w
        w=B-(running-start); block.append(w)
        assert w>running and w>=3
        running+=w
        assert sum(block)==B and len(block)==c
        result.append(block)
    flat=sum(result,[]); s=0
    for w in flat: assert w>s and w>=3; s+=w
    return result

flow=0; maxbits=0
supports=[
    [[[1,1],[1,1]],[[1],[1]]],
    [[[1,0],[0,1]],[[1],[1]]],
    [[[1,1]],[[1],[1]]],
    [[[1,1],[1,1]],[[1,1],[1,1]],[[1],[1]]],
    [[[1,1]],[[1,0],[0,1]],[[1],[1]]],
]
for S in supports:
    # All binary perturbations for two epochs; deterministic selected ones for three.
    R=1; base=build(S,R); edges=[(j,i,k) for j,A in enumerate(S) for i,row in enumerate(A) for k,x in enumerate(row) if x]
    perturb=list(itertools.product(range(2),repeat=len(edges))) if len(S)==2 else [tuple([0]*len(edges)),tuple([1]*len(edges))]+[tuple(int(a==b) for a in range(len(edges))) for b in range(len(edges))]
    for alpha in perturb:
        K=[[row[:] for row in A] for A in base]
        for (j,i,k),a in zip(edges,alpha):K[j][i][k]+=a
        for j in range(1,len(S)):
            W=weights(K,j)
            maxbits=max(maxbits,max(w.bit_length() for block in W for w in block))
            # Exact conservation across all labelled clusters, without enumerating huge leaf panels.
            assert sum(map(sum,W))==sum(map(sum,K[j-1]))
            assert sum(map(len,W))==sum(map(sum,K[j]))
        flow+=1

# Direct drop decoder with every assignment on modest superincreasing clusters.
decodes=0
for m in range(1,7):
    ws=[3*2**i for i in range(m)]
    for assign in itertools.product(range(2),repeat=m):
        rates=[F(2,3),F(2,3)] # equal rates deliberately
        counts=[sum(w for w,a in zip(ws,assign) if a==p) for p in range(2)]
        recovered=[]
        for i,(w,p) in enumerate(zip(ws,assign)):
            q1=(counts[p]-1)*rates[p]; q2=(counts[p]-2)*rates[p]
            r=q1-q2; k=q1/r+1
            recovered.append((r,k)); counts[p]-=w-1
        known=set()
        for i in range(m):
            if i in known:continue
            r,k=recovered[i]
            subsets=[set(t) for z in range(1,m+1) for t in itertools.combinations(range(m),z) if sum(ws[a] for a in t)==k]
            assert len(subsets)==1
            actual={a for a in range(m) if assign[a]==assign[i]}
            assert subsets[0]==actual
            known|=actual
        decodes+=1

# Coherent orbit moments: two hidden epochs, equal rates, labelled initial populations.
G=[[[F(1,4),F(3,4)],[F(2,3),F(1,3)]],[[F(1,5),F(4,5)],[F(3,7),F(4,7)]],[[F(1)],[F(1)]]]
perms=list(itertools.permutations(range(2)))
def orbit(A):
    out=[]
    for p,q in itertools.product(perms,repeat=2):
        sig=[(0,1),p,q,(0,)]
        out.append(tuple(A[j][sig[j][i]][sig[j+1][k]] for j in range(3) for i in range(len(A[j])) for k in range(len(A[j][0]))))
    return out
# Swap middle rows without matching the preceding columns: a local but incoherent alignment.
T=[[row[:] for row in A] for A in G]; T[1]=T[1][::-1]
OG,OT=orbit(G),orbit(T)
assert set(OG).isdisjoint(set(OT))
# Positive support tilt with simple base exponents; this tests orbit separation independently of flow.
base=[1]*len(OG[0])
def tilted(O):
    ans={}
    for a in O:
        w=F(1)
        for x,k in zip(a,base):w*=x**k
        if w:ans[a]=ans.get(a,F(0))+w
    return ans
mu,nu=tilted(OG),tilted(OT)
# An explicit nonnegative annihilator of degree 2|H| separates the measures.
def Q(x):
    val=F(1)
    for a in mu:val*=sum((u-v)**2 for u,v in zip(x,a))
    return val
assert sum(w*Q(a) for a,w in mu.items())==0
sep=sum(w*Q(a) for a,w in nu.items()); assert sep>0
# Support weight handles incompatibility: zero tilted mass is possible and detected at degree zero.
A=[[[F(1),F(0)],[F(0),F(1)]],G[1],G[2]]
OA=orbit(A); S=[i for i,x in enumerate(OA[0]) if x]
positive=[a for a in OA if all(a[i]>0 for i in S)]
assert positive and len(positive)<len(OA)
for a in positive:assert sum(x>0 for x in a)==len(S)
# Direct labelled-block wiring over two intermediate epochs. Enumerate the
# compatible hidden names, and multiply each individual current-block route.
cluster_sizes=[3*2**i for i in range(10)]
class1=[0]*4+[1]*6
# Each first-epoch cluster contains alternating initial-population labels.
leaf_sources=[[a%2 for a in range(w)] for w in cluster_sizes]
# Second epoch has clusters of sizes 3 and 7, each completed to one block.
cluster2=[list(range(3)),list(range(3,10))]
K0=[[0,0],[0,0]]
for sources,c in zip(leaf_sources,class1):
    for a in sources:K0[a][c]+=1
K1=[[0,0],[0,0]]
for k,indices in enumerate(cluster2):
    for i in indices:K1[class1[i]][k]+=1
flatK=tuple(x for A in [K0,K1,[[1],[1]]] for row in A for x in row)
route_sum=F(0)
for p,q in itertools.product(perms,repeat=2):
    route=F(1)
    for sources,c in zip(leaf_sources,class1):
        for a in sources:route*=G[0][a][p[c]]
    for k,indices in enumerate(cluster2):
        for i in indices:route*=G[1][p[class1[i]]][q[k]]
    for k in range(2):route*=G[2][q[k]][0]
    route_sum+=route
orbit_sum=F(0)
for a in OG:
    z=F(1)
    for x,k in zip(a,flatK):z*=x**k
    orbit_sum+=z
assert route_sum==orbit_sum and route_sum>0
result={'flow_perturbations':flow,'largest_cluster_bit_length':maxbits,'equal_rate_decoder_assignments':decodes,'coherent_orbit_size':len(mu),'incoherent_orbit_size':len(nu),'annihilator_degree':2*len(mu),'strict_positive_separation':str(sep),'support_survivors':len(positive),'multi_epoch_labelled_wiring_terms':4,'multi_epoch_initial_leaves':sum(cluster_sizes),'status':'PASS'}
print(json.dumps(result,sort_keys=True,indent=2))
