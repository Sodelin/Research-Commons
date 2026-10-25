"""Finite two-source confidence/design demo; not an inference method for arbitrary networks."""
from exact_small_nmsc import *
from math import log,ceil

def confidence_candidates(counts,models,alpha):
    """IID whole-genealogy outcomes; fixed finite catalogue assumed to contain the truth."""
    L=sum(counts.values());assert L>0 and 0<alpha<1
    outcomes=set(counts)
    for p in models.values():outcomes.update(p)
    r=(log(2*len(outcomes)/alpha)/(2*L))**.5
    return {'loci':L,'radius':r,'candidates':[name for name,p in models.items() if all(abs(counts.get(k,0)/L-float(p.get(k,F(0))))<=r for k in outcomes)]}

if __name__=='__main__':
    sources={'triangle':triangle(F(9,10)),'fourcycle':fourcycle()}
    candidates=[]
    for duplicated in 'ABCD':
        alloc={x:1 for x in 'ABCD'};alloc[duplicated]=2
        p,q=[unroot(run(source,alloc)) for source in sources.values()]
        event=sorted(k for k in set(p)|set(q) if p.get(k,F(0))>q.get(k,F(0)))
        ep=sum((p.get(k,F(0)) for k in event),F(0));eq=sum((q.get(k,F(0)) for k in event),F(0));gap=ep-eq
        assert gap==tv(p,q)
        candidates.append({'duplicated_taxon':duplicated,'gap':str(gap),'gap_float':float(gap),'event':event,'P_triangle_event':str(ep),'P_fourcycle_event':str(eq),'midpoint':str((ep+eq)/2),'iid_loci_sufficient_for_each_error_0_05':ceil(2*log(20)/float(gap)**2)})
    best=max(candidates,key=lambda r:F(r['gap']))
    one=[unroot(run(source,{x:1 for x in 'ABCD'})) for source in sources.values()]
    assert one[0]==one[1]
    # Exactly matching counts are only a deterministic confidence-set fixture, not sampled data.
    counts={k:int(v*400) for k,v in one[0].items()};assert sum(counts.values())==400
    fixture=confidence_candidates(counts,dict(zip(sources,one)),.05)
    assert fixture['candidates']==['triangle','fourcycle']
    print(json.dumps({'status':'Exact fixed-two-source design; numerical Hoeffding budget evaluated with floating logarithm, no empirical samples','criterion':'Largest unrooted whole-genealogy TV among four allocations with exactly one extra sampled copy','best_duplicate':best['duplicated_taxon'],'candidate_designs':candidates,'deterministic_onecopy_confidence_fixture':fixture},indent=2))
