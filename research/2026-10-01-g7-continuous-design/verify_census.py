"""Exhaustive small source-census replay, with exact rational law controls."""
import json,time
from pathlib import Path
import sympy as s
import networkx as nx
from source_census import census,displayed,admitted,cofacial,canonical_key
from law_compiler import compile_law,unrooted_law
from verify import TRIANGLE,DIAMOND,PAIR

start=time.monotonic()
for g in (TRIANGLE,DIAMOND,PAIR): assert admitted(g)
from itertools import combinations
assert cofacial(tuple(combinations('ABCD',2)),tuple('ABC'))
assert not cofacial(tuple(combinations('ABCD',2)),tuple('ABCD'))
counts={}
compiled=0
full_forcing_checks=0
natural_common_checks=0
symbolic_trees=0
for n,r in ((3,0),(4,0),(5,0),(3,1),(4,1)):
    nets=list(census(n,r)); counts[f'n{n}_r{r}']=len(nets)
    if r==0: assert len(nets)=={3:3,4:15,5:105}[n]
    if n!=4: continue
    for net in nets:
        answers=displayed(net)
        xx,gg=net.parameters()
        edgevals={i:s.Rational(i+4,i+7) for i in range(len(xx))}
        gvals={h:s.Rational(2,5) for h in gg}
        # Full symbolic tree law (15 complete sources); no numeric premise.
        if r==0:
            law=unrooted_law(compile_law(net))
            assert s.expand(sum(law.values()))==1
            match=next(iter(answers.values()))
            other=[p for t,p in law.items() if t!=match]
            assert s.expand(other[0]-other[1])==0
            survival=s.expand(1-(law[match]-other[0]))
            powers=survival.as_powers_dict()
            assert all(v in xx and p==1 for v,p in powers.items())
            assert len(powers)>0
            symbolic_trees+=1
        hybrids=net.structure()[3]
        forcedlaws={}
        for bits,target in answers.items():
            forced=dict(zip(hybrids,bits))
            p=unrooted_law(compile_law(net,'independent',forced,edge_values=edgevals,inheritance_values=gvals))
            q=unrooted_law(compile_law(net,'common',forced,edge_values=edgevals,inheritance_values=gvals))
            assert p==q and sum(p.values())==1
            assert p[target]>max(v for t,v in p.items() if t!=target)
            forcedlaws[bits]=p; full_forcing_checks+=1; compiled+=2
        indep=unrooted_law(compile_law(net,'independent',edge_values=edgevals,inheritance_values=gvals))
        common=unrooted_law(compile_law(net,'common',edge_values=edgevals,inheritance_values=gvals))
        assert sum(indep.values())==1 and all(p>0 for p in indep.values())
        mix={t:s.S.Zero for t in common}
        for bits,law in forcedlaws.items():
            w=s.S.One
            for h,b in zip(hybrids,bits): w*=gvals[h] if b==0 else 1-gvals[h]
            for t in mix: mix[t]+=w*law[t]
        assert mix==common
        baseline=min(common.values())
        assert {t for t,v in common.items() if v>baseline}==set(answers.values())
        natural_common_checks+=1; compiled+=2
report={'status':'PASS','census_counts':counts,'symbolic_all_source_tree_laws':symbolic_trees,
        'exact_rational_law_compilations':compiled,'full_forcing_target_and_mechanism_comparisons':full_forcing_checks,
        'natural_common_mixture_and_target_comparisons':natural_common_checks,
        'core_admitted_fixture_graphs':3,'cofacial_positive_negative_controls':2,
        'versions':{'sympy':s.__version__,'networkx':nx.__version__},
        'seconds':time.monotonic()-start,
        'limits':'Complete listed finite censuses; rational controls are not all-parameter certificates. General source-law and census correctness have hand proofs, not formal verification.'}
Path(__file__).with_name('census-checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
