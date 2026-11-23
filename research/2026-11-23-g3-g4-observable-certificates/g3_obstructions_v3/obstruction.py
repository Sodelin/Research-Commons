"""Observable exact fourth-moment rejection screen for original natural G3."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import combinations, product
from math import comb, prod
import json

def moments(masses, groups):
    return [sum(x for mask,x in masses.items() if mask&((1<<k)-1)==(1<<k)-1)
            for k in range(groups+1)]

def valid_masses(masses, groups):
    if set(masses) != set(range(1 << groups)):
        raise ValueError("missing or unknown bit mask")
    if any(type(x) not in (int,str,Q) for x in masses.values()):
        raise ValueError("supply exact rationals, not floats")
    m = {k:Q(x) for k,x in masses.items()}
    if min(m.values())<0 or sum(m.values())!=1:
        raise ValueError("not a probability distribution")
    for k,x in m.items():
        if x != m[(1 << k.bit_count())-1]:
            raise ValueError("not block exchangeable")
    return m

def principal_minors(h):
    """All principal minors of symmetric matrices up to size 3."""
    for j in range(1,len(h)+1):
        for ind in combinations(range(len(h)),j):
            a=[[h[i][k] for k in ind] for i in ind]
            if j==1:
                d=a[0][0]
            elif j==2:
                d=a[0][0]*a[1][1]-a[0][1]**2
            else:
                d=(a[0][0]*a[1][1]*a[2][2] + 2*a[0][1]*a[0][2]*a[1][2]
                   -a[0][0]*a[1][2]**2-a[1][1]*a[0][2]**2-a[2][2]*a[0][1]**2)
            yield str(ind),d

def negative_minors(m):
    h=[[m[i+j] for j in range(3)] for i in range(3)]
    g=[[m[i+j+1]-m[i+j+2] for j in range(2)] for i in range(2)]
    return {f"{name}:{ix}":str(value) for name,mat in (("H",h),("G",g))
            for ix,value in principal_minors(mat) if value<0}

def cutoff_moments(m,n):
    """Forced moments of K/n via ordinary-to-falling-factorial expansion."""
    st=[[1],[0,1],[0,1,1],[0,1,3,1],[0,1,7,6,1]]
    return [sum(st[k][j]*prod(n-u for u in range(j))*m[j]
                for j in range(k+1))/n**k for k in range(5)]

def check_no(masses):
    """Accept only a correctly projected natural 4-group topology row."""
    m=moments(valid_masses(masses,4),4)
    gaps=negative_minors(m)
    report=dict(decision="UNKNOWN",moments=list(map(str,m)),negative_limit_minors=gaps)
    if not gaps:
        return report
    # Compact finite witness; on a strictly negative limit minor this terminates.
    n=5
    while not (broken:=negative_minors(cutoff_moments(m,n))):
        n*=2
    return dict(report,decision="NO",hypothetical_blocks=n,hypothetical_copies=4*n,
                finite_violations=broken)

# Reused v2 root-split count idea, now exact for any number of four-label groups.
@cache
def uniform_tree_counts(n):
    """Count nonplane rooted labelled trees by the balanced-group bit mask."""
    if sum(n)==1:
        return {0:1}
    counts=Counter()
    for left in product(*(range(k+1) for k in n)):
        if sum(left) in (0,sum(n)):
            continue
        right=tuple(k-l for k,l in zip(n,left))
        choose=prod(comb(k,l) for k,l in zip(n,left))
        for lm,lc in uniform_tree_counts(left).items():
            for rm,rc in uniform_tree_counts(right).items():
                v=0
                for i,k in enumerate(n):
                    if k==4 and (left[i]==2 or left[i]==4 and lm&(1<<i)
                                 or left[i]==0 and rm&(1<<i)):
                        v |= 1<<i
                counts[v]+=choose*lc*rc
    assert all(v%2==0 for v in counts.values())
    out={k:v//2 for k,v in counts.items()}
    assert sum(out.values())==prod(range(1,2*sum(n)-2,2))
    return out

def comb_pair_counts(n,left_size):
    """Uniform relabeling of two rooted combs, by left-side subset counts."""
    count=Counter()
    for left in combinations(range(4*n),left_size):
        hits=Counter(i//4 for i in left)
        count[sum(1<<j for j in range(n) if hits[j]==2)]+=1
    return count

def marginalize(m,n):
    keep=(1<<n)-1
    return {k:sum(v for i,v in m.items() if i&keep==k) for k in range(1<<n)}

def fixture():
    n=4
    assert uniform_tree_counts((4,4)) == {0:87408,1:20700,2:20700,3:6327}
    assert uniform_tree_counts((4,4,4))[7]==169971291
    u=uniform_tree_counts((4,)*n)
    ulaw={k:Q(u.get(k,0),sum(u.values())) for k in range(1<<n)}
    assert min(ulaw.values())>0
    a=comb_pair_counts(n,7)
    alaw={k:Q(a.get(k,0),comb(16,7)) for k in range(1<<n)}
    assert moments(alaw,n)==[Q(1),Q(27,65),Q(126,715),Q(54,715),Q(0)]
    law={k:Q(999,1000)*alaw[k]+Q(1,1000)*ulaw[k] for k in range(1<<n)}
    _,p,q,r,s=moments(law,n)
    v2={"pair":q-p*p,"success":p*r-q*q,"failure":(1-p)*(q-r)-(p-q)**2}
    assert min(v2.values())>0 and p<Q(5,12)
    assert q*s-r*r<0
    four_moment=check_no(law)
    assert four_moment["decision"]=="NO" and four_moment["hypothetical_blocks"]==5
    # Independent finite polynomial: E[(K)_2*(K−3)^2] in a 5-block extension.
    poly=20*q-60*r+120*s
    assert poly<0
    # Controls: uniform input restrictions agree with v2; a nontrivial
    # two-atom Bernoulli mix survives, as must a degenerate all-0 or all-1 law.
    assert marginalize(ulaw,3)=={k:Q(v,13749310575)
                                 for k,v in uniform_tree_counts((4,4,4)).items()}
    for vals in ((Q(0),Q(0)),(Q(1),Q(1)),(Q(1,5),Q(2,3))):
        ctrl={k:sum(t**k.bit_count()*(1-t)**(4-k.bit_count()) for t in vals)/2
              for k in range(16)}
        assert check_no(ctrl)["decision"]=="UNKNOWN"
    bad={k:law[k] for k in law}
    bad[1],bad[0]=bad[0],bad[1]
    try:
        check_no(bad)
    except ValueError:
        pass
    else:
        raise AssertionError("accepted asymmetric malformed event table")
    return dict(uniform_topologies=sum(u.values()),uniform_counts=dict(sorted(u.items())),
                comb_pair_counts=dict(sorted(a.items())),fixture={k:str(v) for k,v in law.items()},
                v2_gaps={k:str(v) for k,v in v2.items()},v3=four_moment,
                independent_five_block_polynomial=str(poly))

if __name__=="__main__":
    print(json.dumps(fixture(),sort_keys=True,indent=2))
