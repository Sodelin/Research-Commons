"""Exact rational 12-copy G3 moment obstruction, standard library only."""
from collections import Counter
from fractions import Fraction as Q
from functools import cache
from itertools import combinations, product
from math import comb, prod
import json

def moment(masses, k):
    """Probability the first k blocks are all balanced."""
    mask = (1 << k) - 1
    return sum(mass for bits, mass in masses.items() if bits & mask == mask)

def forced_moments(p, q, r, n):
    """First three ordinary moments of balanced fraction among n blocks."""
    return p, ((n-1)*q+p)/n, ((n-1)*(n-2)*r+3*(n-1)*q+p)/(n*n)

def check_no(masses):
    """Eight exact joint masses, indexed by 3-bit binary outcomes.

    Input is limited to projections of a single natural response to three
    disjoint equally sized, same-taxon panels. This function cannot establish
    the observation adapter or identify the natural response by itself.
    """
    if set(masses) != set(range(8)):
        raise ValueError("need all eight Boolean event masses")
    if any(type(v) not in (int, str, Q) for v in masses.values()):
        raise ValueError("supply exact rational values, not floats")
    masses = {bits: Q(mass) for bits, mass in masses.items()}
    if min(masses.values()) < 0 or sum(masses.values()) != 1:
        raise ValueError("not a probability distribution")
    if any(masses[a] != masses[b] for a in masses for b in masses
           if a.bit_count() == b.bit_count()):
        raise ValueError("not block-exchangeable")
    p,q,r = (moment(masses,k) for k in (1,2,3))
    pair_gap = q - p*p
    success_gap = p*r - q*q
    failure_gap = (1-p)*(q-r)-(p-q)**2
    gaps = dict(pairwise=str(pair_gap), success_weighted=str(success_gap),
                failure_weighted=str(failure_gap))
    outcome = dict(decision="UNKNOWN",moments=dict(p=str(p),q=str(q),r=str(r)),gaps=gaps)
    if min(pair_gap,success_gap,failure_gap) >= 0:
        return outcome
    # Finite witness. Limits guarantee exit; no enumeration of G3 sources.
    n = 4
    while True:
        a,b,c = forced_moments(p,q,r,n)
        finite = dict(pairwise=b-a*a,success_weighted=a*c-b*b,
                      failure_weighted=(1-a)*(b-c)-(a-b)**2)
        broken = {k:str(v) for k,v in finite.items() if v<0}
        if broken:
            break
        n *= 2
    outcome.update(decision="NO", hypothetical_blocks=n, hypothetical_copies=4*n,
                   finite_violations=broken)
    return outcome

@cache
def labelled_tree_counts(n):
    """Counts by mask when each labelled group has n[i] <= 4 leaves.

    A bit records a balanced restricted tree for a four-leaf group. No
    other shape information is needed: root is balanced precisely if a
    group's split is 2+2, or if inherited from an occupied child when the
    other child contains no leaves of the group.
    """
    if sum(n) == 1:
        return {0:1}
    counts = Counter()
    for left in product(*(range(k+1) for k in n)):
        if sum(left) in (0,sum(n)):
            continue
        right = tuple(k-l for k,l in zip(n,left))
        label_choices = prod(comb(k,l) for k,l in zip(n,left))
        for lb,lc in labelled_tree_counts(left).items():
            for rb,rc in labelled_tree_counts(right).items():
                bits = 0
                for i,k in enumerate(n):
                    if k==4 and (left[i]==2 or left[i]==4 and lb&(1<<i)
                                 or left[i]==0 and rb&(1<<i)):
                        bits |= 1<<i
                counts[bits] += label_choices*lc*rc
    assert all(v%2==0 for v in counts.values())
    result = {bits:v//2 for bits,v in counts.items()}
    assert sum(result.values()) == prod(range(1,2*sum(n)-2,2))
    return result

def comb_pair_counts():
    count = Counter()
    for left in combinations(range(12),5):
        bits = sum(1<<i for i in range(3)
                   if sum(4*i <= j < 4*i+4 for j in left)==2)
        count[bits] += 1
    return count

def fixture():
    uniform = labelled_tree_counts((4,4,4))
    u_total = sum(uniform.values())
    u = {bits:Q(uniform.get(bits,0),u_total) for bits in range(8)}
    shape = comb_pair_counts()
    s = {bits:Q(shape.get(bits,0),comb(12,5)) for bits in range(8)}
    assert len(uniform)==8
    assert [moment(s,k) for k in (1,2,3)] == [Q(14,33),Q(2,11),0]
    # Uniform labelled-tree model preserves uniformity on restriction:
    # each tree has the same number of edge-insertion extensions.
    assert moment(u,1)==Q(1,5)
    assert moment(u,2)==Q(703,15015) # v1 independent full enumeration
    assert labelled_tree_counts((4,4)) == {0:87408,1:20700,2:20700,3:6327}
    law = {bits:Q(209,280)*s[bits]+Q(1,12)*u[bits] for bits in range(8)}
    law[0] += Q(143,840) # pure 12-leaf comb, relabelled uniformly
    v = check_no(law)
    assert v['decision']=="NO" and Q(v['gaps']['failure_weighted']) > 0
    p,q,r = (moment(law,i) for i in (1,2,3))
    assert p==Q(1,3) and q>=p*p and p*r<q*q
    # Simpler independent certificate for this fixture: K*(K-2)^2 >= 0.
    four_block_poly = 4*p - 12*q + 24*r
    assert four_block_poly == Q(-699554,2204475)
    for t in (Q(0),Q(1,3),Q(1)):
        assert check_no({bits:t**bits.bit_count()*(1-t)**(3-bits.bit_count())
                         for bits in range(8)})['decision']=="UNKNOWN"
    # Impose the reflected obstruction without a new source assertion.
    refl = check_no({bits:law[bits^7] for bits in range(8)})
    assert refl["decision"]=="NO" and Q(refl["gaps"]["failure_weighted"])<0
    return dict(all_labelled_trees=u_total,uniform_counts=uniform,
                shape_counts=dict(shape),fixture={bits:str(v) for bits,v in law.items()},
                result=v,reflected_result=refl,
                four_block_K_times_K_minus_2_squared=str(four_block_poly))

if __name__ == "__main__":
    print(json.dumps(fixture(),indent=2,sort_keys=True))
