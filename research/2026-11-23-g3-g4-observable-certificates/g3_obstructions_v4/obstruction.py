"""Exact G3 NO test for the joint vector of five-leaf rooted shapes."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import combinations, product
from math import comb,prod
import json

# For four samples: 0 comb, 1 balanced.
# For five samples: 0 comb, 1 singleton + balanced quartet, 2 split 2+3.
SHAPES=("comb","1+(2+2)","2+3")

def join_shape(k,l,lshape,rshape):
    """Project an unlabeled binary join to one given group."""
    if k<4:
        return 0
    if l==0:
        return rshape
    if l==k:
        return lshape
    if k==4:
        return int(l==2)
    if l in (2,3):
        return 2
    return rshape if l==1 else lshape # 1 plus a four-leaf child

@cache
def uniform_counts(n):
    """Uniform exact counts on all nonplane labelled rooted binary topologies."""
    if sum(n)==1:
        return {tuple(0 for _ in n):1}
    out=Counter()
    for left in product(*(range(k+1) for k in n)):
        if not 0<sum(left)<sum(n):
            continue
        right=tuple(k-l for k,l in zip(n,left))
        mult=prod(comb(k,l) for k,l in zip(n,left))
        for lshape,lc in uniform_counts(left).items():
            for rshape,rc in uniform_counts(right).items():
                t=tuple(join_shape(*v) for v in zip(n,left,lshape,rshape))
                out[t]+=mult*lc*rc
    assert all(v%2==0 for v in out.values())
    answer={k:v//2 for k,v in out.items()}
    assert sum(answer.values())==prod(range(1,2*sum(n)-2,2))
    return answer

def comb_pair(n,left_size):
    """16 leaves, split into two combs with a uniform assignment of labels."""
    total=16
    out=Counter()
    groups=[tuple(range(sum(n[:i]),sum(n[:i+1]))) for i in range(len(n))]
    for left in combinations(range(total),left_size):
        ls=set(left)
        t=tuple(join_shape(k,sum(j in ls for j in group),0,0)
                for k,group in zip(n,groups))
        out[t]+=1
    return out

def chain_core(n):
    """16 leaves, balanced-capable 3+4 inner comb pair and 9 outer tips in a comb."""
    # Choose the seven core labels and the three on the smaller root side.
    # Actual within-side/outer comb ordering can be arbitrary under uniform
    # relabeling: below size 6 its restrictions are always comb-shaped.
    total=16
    out=Counter()
    groups=[set(range(sum(n[:i]),sum(n[:i+1]))) for i in range(len(n))]
    for core in combinations(range(total),7):
        nc=tuple(len(g.intersection(core)) for g in groups)
        for small in combinations(core,3):
            nl=tuple(len(g.intersection(small)) for g in groups)
            inner=tuple(join_shape(k,l,0,0) for k,l in zip(nc,nl))
            # Outside core, any leaves are singletons attached successively.
            # With at least two outside leaves a 4/5 group is a comb. Exactly
            # one outside leaf atop four balanced core leaves creates 1+(2+2).
            t=tuple(x if j==k or (j,k)==(4,5) else 0 for j,k,x in zip(nc,n,inner))
            out[t]+=1
    assert sum(out.values())==comb(16,7)*comb(7,3)
    return out

def norm(d):
    total=sum(d.values())
    return {k:Q(v,total) for k,v in d.items()}

def fixture_law(n):
    # Uniform rooted labelled law restricts projectively because every
    # fixed tree has the same number of stem/edge-insertion extensions.
    hist=Counter()
    uniform_weight=Q(1,1000)
    # This core weight makes the four-copy balanced marginal exactly 1/3.
    core_weight=Q(394513,1830375)
    base_weight=1-uniform_weight-core_weight
    components=((base_weight*Q(7,13),comb_pair(n,7)),
                (base_weight*Q(6,13),comb_pair(n,8)),
                (core_weight,chain_core(n)),
                (uniform_weight,uniform_counts(n)))
    for weight,counts in components:
        for k,p in norm(counts).items():
            hist[k]+=weight*p
    assert sum(hist.values())==1
    return hist

def minors(h):
    for j in range(1,len(h)+1):
        for ind in combinations(range(len(h)),j):
            a=[[h[i][k] for k in ind] for i in ind]
            if j==1:
                d=a[0][0]
            elif j==2:
                d=a[0][0]*a[1][1]-a[0][1]**2
            else:
                d=(a[0][0]*a[1][1]*a[2][2]+2*a[0][1]*a[0][2]*a[1][2]
                   -a[0][0]*a[1][2]**2-a[1][1]*a[0][2]**2-a[2][2]*a[0][1]**2)
            yield str(ind),d

def finite_covariance(j,p,n):
    return [[j[i][k]-p[i]*p[k]+((p[i] if i==k else 0)-j[i][k])/n
             for k in range(3)] for i in range(3)]

def matrix_screen(masses):
    if set(masses)!=set(product(range(3),repeat=2)):
        raise ValueError("need nine shape-pair masses")
    if any(type(v) not in (int,str,Q) for v in masses.values()):
        raise ValueError("exact rational input only")
    j=[[Q(masses[i,k]) for k in range(3)] for i in range(3)]
    if any(j[i][k]<0 or j[i][k]!=j[k][i] for i,k in masses) or sum(map(sum,j))!=1:
        raise ValueError("not a probability matrix with block-interchange symmetry")
    p=list(map(sum,j))
    c=[[j[i][k]-p[i]*p[k] for k in range(3)] for i in range(3)]
    bad={s:str(v) for s,v in minors(c) if v<0}
    result=dict(decision="UNKNOWN",marginal=list(map(str,p)),
                covariance=[list(map(str,a)) for a in c],negative_limit_minors=bad)
    if not bad:
        return result
    n=3
    while True:
        h=finite_covariance(j,p,n)
        violated={s:str(v) for s,v in minors(h) if v<0}
        if violated:
            return dict(result,decision="NO",hypothetical_blocks=n,
                        hypothetical_copies=5*n,negative_finite_minors=violated)
        n*=2

def fixture():
    quartet=fixture_law((4,4,4,4))
    m=[sum(v for k,v in quartet.items() if all(k[i] for i in range(j)))
       for j in range(5)]
    _,p,q,r,s=m
    h=[[m[i+j] for j in range(3)] for i in range(3)]
    g=[[m[i+j+1]-m[i+j+2] for j in range(2)] for i in range(2)]
    prev=[q-p*p,p*r-q*q,(1-p)*(q-r)-(p-q)**2]
    assert min(prev)>0 and p==Q(1,3)
    assert all(v>0 for _,v in (*minors(h),*minors(g)))
    table=fixture_law((5,5))
    assert min(table.values())>0
    core=norm(chain_core((5,5)))
    assert (1,1) not in core and sum(v for k,v in core.items() if k[0]==1)==Q(27,728)
    assert all(1 not in k for x in (7,8) for k in comb_pair((5,5),x))
    out=matrix_screen(table)
    assert out["decision"]=="NO"
    # Stronger finite certificate than any individual coordinate variance
    # at the same N: the mixed shape contrast has negative variance.
    j=[[table[i,k] for k in range(3)] for i in range(3)]
    fc=finite_covariance(j,list(map(sum,j)),34)
    contrast=(-1,22,0)
    contrast_var=sum(contrast[i]*contrast[k]*fc[i][k] for i,k in table)
    assert min(fc[i][i] for i in range(3))>0 and contrast_var<0
    out["finite_mixed_contrast"]=dict(blocks=34,copies=170,
        contrast=contrast,individual_variances=[str(fc[i][i]) for i in range(3)],
        contrast_variance=str(contrast_var))
    # Independent 10-tip to 5-tip projection: 60 combs, 15 singleton plus
    # balanced four, and 30 split 2+3, giving 105 total labelled topologies.
    assert uniform_counts((5,))=={(0,):60,(1,):15,(2,):30}
    uf=norm(uniform_counts((5,5)))
    assert {i:sum(v for (l,_),v in uf.items() if l==i) for i in range(3)}=={
        k[0]:v for k,v in norm(uniform_counts((5,))).items()}
    pctrl=(Q(2,7),Q(1,7),Q(4,7))
    assert matrix_screen({(i,j):pctrl[i]*pctrl[j] for i,j in table})["decision"]=="UNKNOWN"
    bad=dict(table)
    bad[0,1],bad[0,0]=bad[0,0],bad[0,1]
    try:
        matrix_screen(bad)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid asymmetric table accepted")
    return dict(shape_order=SHAPES, joint=[[str(table[i,j]) for j in range(3)] for i in range(3)],
                quartet_moments=list(map(str,m)),quartet_v1_v2_gaps=list(map(str,prev)),
                quartet_H_minors={k:str(v) for k,v in minors(h)},
                quartet_G_minors={k:str(v) for k,v in minors(g)}, v4=out)

if __name__=="__main__":
    print(json.dumps(fixture(),indent=2))
