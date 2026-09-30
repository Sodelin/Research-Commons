"""Reproducible exact checks. No simulation and no unexecuted all-network census."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from collections import defaultdict
from dataclasses import replace
from pathlib import Path
import json, hashlib, math, time
import sympy as sp
from metric_law import Network, Edge, histories, density, equal_metric_laws, encode_poly
from joint_kernel import (forest, lam, death, jump, evolve, apply_edge, apply_bigon,
                          pair_survival, common_moments, from_common_moments,
                          common_quadrature, rooted_law, unrooted_law, quartet_marginals,
                          unrooted_key)
from fixtures import tree_with_bigons, collapse_bigons, root_diamond


def run():
    start=time.monotonic()
    result={'scope':'Exact constructed fixtures; not empirical data, independent review, or complete network enumeration'}
    # Kingman spectral probabilities and semigroup law, independent jump-chain cases.
    counts=0
    kernel_comparisons=0
    for n in range(2,6):
        initial=forest(chr(97+i) for i in range(n))
        for x in (F(1,4),F(1,2),F(3,4)):
            ps=[death(n,j,x) for j in range(1,n+1)]
            assert sum(ps)==1 and min(ps)>=0
            counts+=1
            dist=dict(evolve(initial,x))
            assert sum(dist.values())==1 and min(dist.values())>=0
            actual=apply_edge(dist,F(2,3))
            expected=dict(evolve(initial,x*F(2,3)))
            assert actual==expected
            kernel_comparisons+=len(expected)
    result['kingman_probability_cases']=counts
    result['semigroup_coordinate_equalities']=kernel_comparisons

    # Entire forest kernels for all <=5 input lineages; both inheritance modes.
    pair_cases=0
    chain_coordinate_equalities=0
    segments=[('edge',F(4,5)),('bigon',F(1,2),F(2,3),F(1,3)),
              ('edge',F(3,4)),('bigon',F(3,5),F(4,7),F(2,5)),('edge',F(5,6))]
    for n in range(2,6):
        initial=forest(chr(97+i) for i in range(n))
        dist={initial:F(1)}
        for s in segments:
            dist=apply_edge(dist,s[1]) if s[0]=='edge' else apply_bigon(dist,*s[1:],'com')
        moment_kernel=from_common_moments(initial,common_moments(segments,n))
        assert dist==moment_kernel
        chain_coordinate_equalities+=len(dist)
    for mode in ('ind','com'):
        for x,y,g in ((F(1,2),F(1,4),F(1,2)),(F(2,3),F(3,5),F(2,7)),(F(1,2),F(1,2),F(1,2))):
            initial=forest(('a','b'))
            dist=apply_bigon({initial:F(1)},x,y,g,mode)
            assert dist[initial]==pair_survival(x,y,g,mode)
            pair_cases+=1
    result['pair_survival_cases']=pair_cases
    result['common_chain_forest_coordinate_equalities']=chain_coordinate_equalities

    # Streaming positive quadrature, explicitly without expanding 2^L choices.
    quad=[]
    for n,L in ((3,6),(4,6),(5,5)):
        seg=[]
        for j in range(L):
            seg.extend([('bigon',F(j+2,j+4),F(j+3,j+7),F(j+2,2*j+5)),('edge',F(4,5))])
        atoms,peak=common_quadrature(seg,n)
        expected=common_moments(seg,n)
        assert len(atoms)<=n and peak<=2*n
        assert all(w>0 for w in atoms.values()) and sum(atoms.values())==1
        assert all(sum(w*x**lam(k) for x,w in atoms.items())==expected[k] for k in range(1,n+1))
        quad.append({'lineage_cap':n,'bigons':L,'atoms':len(atoms),'peak_atoms':peak,
                     'potential_uncompressed_switchings':2**L,'moments_checked':n})
    result['streaming_quadrature']=quad

    # Positive rational five-taxon witnesses: complete law vs ALL quartet marginals.
    b=tree_with_bigons(n=5,left=3)
    t=collapse_bigons(b,left=3)
    b.validate(require_source=True);t.validate(require_source=True)
    result['five_taxon_source_checks']=[b.validate(True),t.validate(True)]
    results=[]
    for mode in ('ind','com'):
        x={e.id:F(1,2) for e in b.edges};x['arm1b']=F(1,4)
        y={e.id:x[e.id] for e in t.edges if e.id!='top'}
        z=pair_survival(x['arm1a'],x['arm1b'],F(1,2),mode)
        y['top']=x['top']*x['cut1']*z
        p,q=rooted_law(b,x,mode),rooted_law(t,y,mode)
        pm,qm=quartet_marginals(p),quartet_marginals(q)
        assert pm==qm and len(pm)==5 and all(len(v)==3 for v in pm.values())
        u,v=unrooted_law(p),unrooted_law(q)
        assert p!=q and u!=v and len(p)==105 and len(u)==15
        key=(('a','b'),('a','b','c'))
        init=forest(('a','b','c'))
        k3=apply_bigon({init:F(1)},x['arm1a'],x['arm1b'],F(1,2),mode)[init]
        delta=k3-z**3
        assert u[key]-v[key]==delta/F(3840)
        results.append({'mechanism':mode,'pair_survival':str(z),'three_lineage_survival':str(k3),
                        'edge_three_lineage_survival':str(z**3),'original_selected_probability':str(u[key]),
                        'replacement_selected_probability':str(v[key]),'difference':str(u[key]-v[key]),
                        'rooted_outcomes':len(p),'unrooted_outcomes':len(u),'quartet_coordinates_equal':15})
    result['full_joint_counterexamples']=results

    # Independent verification of the universal quintet coefficient 1/15.
    initial=forest(('a','b','c'))
    signed={initial:F(1)}
    for f,_ in jump(initial,2): signed[f]=F(-1,2)
    for f,_ in jump(initial,1): signed[f]=F(1,6)
    out=defaultdict(F)
    for f,w in signed.items():
        for completed,p in evolve(forest(f+('d','e')),F(0)):
            out[unrooted_key(completed[0])]+=w*p
    assert out[(('a','b'),('a','b','c'))]==F(1,15) and sum(out.values())==0
    result['quintet_response_coefficient']='1/15'

    # Complete metric equality on every history and calendar cell, not just samples.
    a=tree_with_bigons(arms=(F(3),F(3)))
    c=collapse_bigons(a)
    equal=equal_metric_laws(a,c,'com',max_cells=None)
    assert equal['status']=='equal' and equal['cells_checked']==630
    neq=equal_metric_laws(a,c,'ind',max_cells=None)
    assert neq['status']=='different'
    # Nonconstant common rates, and two different inheritance laws, are distinct.
    mixed=tree_with_bigons()
    unequal_common=equal_metric_laws(mixed,collapse_bigons(mixed),'com',max_cells=None)
    modes=equal_metric_laws(mixed,mixed,'ind','com',max_cells=None)
    assert unequal_common['status']==modes['status']=='different'
    result['metric_complete_equal_case']=equal
    result['metric_independent_difference']=neq
    result['metric_unequal_rates_difference']=unequal_common
    result['metric_mechanism_difference']=modes

    # Independent tree density identity on all-after-root cells.
    h=next(histories(4));bounds=tuple(sorted(set(c.ages.values())-{F(0)}))
    p=density(c,h,(len(bounds),)*3,'ind',bounds)
    # Two pair populations below root: left rate3, right rate1, both ages1..5.
    # Survival to root = exp(-16). Above root: exp(-6(t1-5)-3(t2-t1)-(t3-t2)).
    expected={(F(14),F(-3),F(-2),F(-1)):F(1)}
    assert p==expected
    result['independent_metric_density_identity']=encode_poly(expected)

    # Source-admitted level-two/root case and same-age order invariance.
    diamond=root_diamond()
    names={v:('z_'+v[::-1] if v not in diamond.leaves else v) for v in diamond.ages}
    renamed=Network({names[v]:age for v,age in diamond.ages.items()},
                    tuple(Edge('renamed_'+e.id,names[e.parent],names[e.child],e.rate,e.inheritance)
                          for e in reversed(diamond.edges)),diamond.root_rate)
    root_checks=[]
    for mode in ('ind','com'):
        chk=equal_metric_laws(diamond,renamed,mode,max_cells=None)
        assert chk['status']=='equal'
        root_checks.append({'mechanism':mode,**chk})
    result['root_level_two_source']=diamond.validate(True)
    result['root_level_two_relabeling_checks']=root_checks
    terminal=Network(a.ages,tuple(replace(e,rate=e.rate*7) if e.child in a.leaves else e
                                 for e in a.edges),a.root_rate)
    chk=equal_metric_laws(a,terminal,'ind',max_cells=None)
    assert chk['status']=='equal'
    result['terminal_rate_invariance']=chk
    # AB merges before the bigon, CD later, then the two ancestral clades merge.
    h2=((1,2),(4,8),(3,12)); bounds2=(F(1),F(2),F(3),F(5))
    hand={(F(9),F(-3),F(-1),F(-1)):F(3)}
    for mode in ('ind','com'):
        assert density(mixed,h2,(1,3,4),mode,bounds2)==hand
    result['early_merge_density_identity']=encode_poly(hand)

    # All-size family checked at selected lengths, NOT used as proof by extrapolation.
    family=[]
    for L in (1,2,3,5,10,20):
        n=tree_with_bigons(cycles=L)
        source=n.validate(True)
        ages=sorted(n.ages[f'{s}{i}'] for i in range(1,L+1) for s in ('H','U'))
        assert len(set(ages))==2*L
        family.append(source|{'guaranteed_distinct_density_jump_times':2*L,
                              'any_binary_four_taxon_equal_metric_law_reticulation_lower_bound':L-1})
    result['unbounded_metric_family_fixtures']=family
    # Symbolic strict scalar-collapse invariants, not floating-point sign tests.
    xx=sp.symbols('x')
    assert sp.expand((xx**3+3*xx)/4-((1+xx)/2)**3-(xx-1)**3/8)==0
    result['symbolic_independent_equal_arm_identity']='b3-b2^3=(x-1)^3/8'

    # Fail-closed and malformed input tests.
    guards=0
    assert equal_metric_laws(a,c,'com',max_cells=0)['status']=='unknown';guards+=1
    assert equal_metric_laws(a,c,'com',max_terms=0)['status']=='unknown';guards+=1
    for thunk in (
        lambda: equal_metric_laws(a,c,'nonsense'),
        lambda: density(a,((1,2),(1,4),(7,8)),(2,4,4)),
        lambda: density(a,next(histories(4)),(4,2,4)),
        lambda: Network.from_json(a.json()|{'root_rate':0.5}),
        lambda: Network.from_json(a.json()|{'root_rate':'0'}),
        lambda: equal_metric_laws(a,c,max_cells=-1),
        lambda: equal_metric_laws(a,c,max_terms=-1),
        lambda: pair_survival(F(1,2),F(1,2),F(1,2),'invalid'),
    ):
        try: thunk()
        except (ValueError,TypeError): guards+=1
        else: raise AssertionError('Invalid request accepted')
    result['guard_cases']=guards
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    here=Path(__file__).parent
    result['source_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in here.glob('*.py')}
    (here/'fixtures.json').write_text(json.dumps({'metric_bigon':a.json(),'metric_tree':c.json(),
                                                 'mixed_metric_bigon':mixed.json(),
                                                 'five_taxon_shape':b.json(),'root_level_two':diamond.json()},indent=2)+'\n')
    (here/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    run()
