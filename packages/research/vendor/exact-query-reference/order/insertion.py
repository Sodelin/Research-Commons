"""Exact insertion-slot learning. See INSERTION.md for hypotheses and proofs.
General mode certifies empty/nonempty slot sets. Promised mode assumes at least
one extension and must not be used as an unqualified frozen-order update.
"""
from core import pair_bit, filter_gaps


def reduced_gap_candidates(order,z,query):
    """Balanced 3-arc elimination. Return <=2 candidates; no extension promise."""
    m=len(order); candidates=set(range(m))
    while len(candidates)>2:
        s=sorted(candidates); n=len(s)
        # Put cuts immediately before the first gap in each group.
        cuts=(s[0],s[n//3],s[(2*n)//3])
        q=tuple(sorted((z,)+(tuple(order[i] for i in cuts))))
        ans=query(q); assert ans in (1,2,3,4,5,6,7)
        survivors=filter_gaps(order,z,cuts,ans,candidates)
        assert len(survivors)<len(candidates)
        candidates=survivors
    return candidates


def learn_all_gaps(order,z,query,promised=False):
    """Complete slot learning, linear general mode; logarithmic promised mode."""
    m=len(order)
    cand=reduced_gap_candidates(order,z,query)
    if promised and len(cand)<=1: return cand
    kept=set()
    for i in sorted(cand):
        b,c=order[i],order[(i+1)%m]
        if promised:
            j=next(x for x in cand if x!=i)
            tests=(order[j],order[(j+1)%m])
        else: tests=order
        ok=True
        for a in tests:
            if a in (b,c):continue
            q=tuple(sorted((z,a,b,c)))
            if query(q)&pair_bit(q,(z,a)):
                ok=False;break
        if ok:kept.add(i)
    return kept


