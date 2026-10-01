"""Exact regression and boundary certificates; no numerical equality tolerance."""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import product
from math import comb
from pathlib import Path
import json
import sympy as sp
from forest_algebra import (ForestAlgebra,Span,forests,graft,edge_polynomials,death_polynomial,
                            bigon_law,leaves)
from source_checks import balanced,insert_chain,root_two_hybrids,compile_source

def monophyly_polynomial(m:int)->dict[int,Q]:
    ans={}
    for k in range(1,m+1):
        for e,c in death_polynomial(m,k).items():
            ans[e]=ans.get(e,Q(0))+c*Q(2,k*(k+1))
    return {e:c for e,c in ans.items() if c}

def sparse_poly_eval(coefs:dict[int,Q],x:Q)->Q:
    return sum((c*x**e for e,c in coefs.items()),Q(0))

def common_cap_collision(M:int)->dict:
    """An exact two-source family for every M, with algebraic inheritance weights.

    Polynomial roots are certified by rational isolating intervals.  The two
    sources have M actual positive pendant bigons, the same four taxa, and
    identical full forest kernels through cap M, but not at cap M+1.
    """
    z=sp.Symbol('z');q=Q(1,2);A=Q(1,2)
    ps=[Q(i,M+1) for i in range(1,M+1)]
    ar={r:1-q**comb(r,2) for r in range(2,M+2)}
    def F(a):
        y=Q(1)
        for p in ps:y*=1-p*a
        return y
    def H(a):
        y=a
        for r in range(2,M+1):y*=a-ar[r]
        return y
    radius=Q(1,4*M*(M+1))
    intervals=[(1/p-radius,1/p+radius) for p in ps]
    vals=[(F(b),H(b)) for lo,hi in intervals for b in (lo,hi)]
    t=Q(1,2);halvings=0
    while any(abs(t*h)>=abs(f)/2 for f,h in vals):
        t/=2;halvings+=1
    def Ft(a):return F(a)+t*H(a)
    for lo,hi in intervals:
        assert lo>1 and F(lo)*F(hi)<0 and Ft(lo)*Ft(hi)<0
    lower=[A**comb(r,2)*F(ar[r]) for r in range(2,M+1)]
    assert all(F(ar[r])==Ft(ar[r]) for r in range(2,M+1))
    diff=A**comb(M+1,2)*t*H(ar[M+1])
    assert diff>0
    Fsym=sp.prod(1-sp.Rational(p.numerator,p.denominator)*z for p in ps)
    Hsym=z*sp.prod(z-sp.Rational(ar[r].numerator,ar[r].denominator) for r in range(2,M+1))
    perturbed=sp.Poly(Fsym+sp.Rational(t.numerator,t.denominator)*Hsym,z,domain=sp.QQ)
    assert perturbed.degree()==M and perturbed.eval(0)==1
    sturm=[]
    for lo,hi in intervals:
        n=perturbed.count_roots(sp.Rational(lo.numerator,lo.denominator),sp.Rational(hi.numerator,hi.denominator))
        assert n==1
        sturm.append(int(n))
    # Every p'_i is the reciprocal of this unique root (>1), hence lies in (0,1).
    pad=1-(1-A)/Q(4*M+1)
    lead=A/pad**(2*M)
    assert 0<lead<1 and 0<pad*q<pad<1
    s=insert_chain(balanced(),'a',lead,tuple((pad*q,pad,p,pad) for p in ps))
    source_validation=s.validate()
    # Direct full labelled-kernel reconstruction, not just count marginals,
    # is actually executed for the manageable caps through five.
    full_kernel_coordinates=0
    if M<=5:
        mu0={0:Q(1),**{comb(r,2):A**comb(r,2)*F(ar[r]) for r in range(2,M+1)}}
        mu1={0:Q(1),**{comb(r,2):A**comb(r,2)*Ft(ar[r]) for r in range(2,M+1)}}
        for k in range(M+1):
            for f,p in edge_polynomials(k).items():
                assert sum((c*mu0[e] for e,c in p.items()),Q(0))==sum((c*mu1[e] for e,c in p.items()),Q(0))
                full_kernel_coordinates+=1
    c=monophyly_polynomial(M+1)[comb(M+1,2)]
    assert c!=0
    return {'cap_M':M,'common_bigons_per_source':M,'natural_edges':source_validation['edges'],
        'source_1_graph_validation':source_validation,
        'source_2_parameters':'Same graph and edge survivals; p_i are reciprocals of the uniquely isolated roots of F_t.',
        'F_t_coefficients_descending':[str(c) for c in perturbed.all_coeffs()],
        'root_intervals':[[str(lo),str(hi)] for lo,hi in intervals],
        'exact_Sturm_root_counts':sturm,'perturbation_t':str(t),
        'lower_sparse_moments_match':True,'executed_full_labelled_kernel_coordinates':full_kernel_coordinates,
        'first_different_no_merger_moment_index':M+1,'no_merger_difference':str(diff),
        'observable_monophyly_difference':str(c*diff),'whole_four_taxon_observation_copy_count':M+4,
        'lead_survival':str(lead),'short_arm_and_connector_survival':str(pad),'long_arm_survival':str(pad*q)}

def run()->dict:
    r={}
    # Check the combinatorial associativity used by the finite algebra, including
    # labelled prior histories, rather than assume matrix multiplication models it.
    total=0
    for k in range(6):
        for a in forests(tuple(range(k))):
            for b in forests(tuple(range(len(a)))):
                for c in forests(tuple(range(len(b)))):
                    assert graft(graft(a,b),c)==graft(a,graft(b,c))
                    total+=1
    r['labelled_grafting_associativity_cases']=total
    A=ForestAlgebra(4)
    assert A.mul(A.edge(Q(2,3)),A.edge(Q(3,5)))==A.edge(Q(2,5))
    r['ordinary_edge_semigroup_exact']=True
    noncommute={}
    for mode in ('common','independent'):
        u=A.cell(Q(1,3),Q(4,5),Q(2,7),Q(3,4),mode)
        v=A.cell(Q(2,5),Q(5,6),Q(3,8),Q(4,7),mode)
        dif=[(i,x-y) for i,(x,y) in enumerate(zip(A.mul(u,v),A.mul(v,u))) if x!=y]
        assert bool(dif)==(mode=='independent')
        noncommute[mode]={'differing_coordinates':len(dif),'example':str(dif[0]) if dif else None}
    r['composition_order_guard']=noncommute
    # A span closed under ordinary edges is not complete for the legal hybrid language.
    edge_span=Span(A.dim)
    for j in range(1,8):edge_span.add(A.edge(Q(j,8)))
    assert len(edge_span)==4
    b=A.cell(Q(1,3),Q(4,5),Q(2,7),Q(3,4),'independent')
    assert not edge_span.contains(b)
    r['omitted_constructor_guard']={'ordinary_edge_span_rank':len(edge_span),'legal_independent_bigon_escapes':True}
    # Swapping original IDs preserves this common natural law but not the named response.
    lead=A.edge(Q(2,3));x0,y0,g0,a0=Q(1,4),Q(1,2),Q(3,10),Q(3,4)
    x1,y1,g1,a1=Q(1,8),Q(1,2),Q(2,5),Q(3,4)
    u=A.cell(x0,y0,g0,a0,'common');v=A.cell(x1,y1,g1,a1,'common')
    natural0=A.mul(lead,A.mul(u,v));natural1=A.mul(lead,A.mul(v,u))
    forced0=A.mul(lead,A.mul(A.cell(x0,y0,Q(1),a0,'common'),v))
    forced1=A.mul(lead,A.mul(A.cell(x1,y1,Q(1),a1,'common'),u))
    assert natural0==natural1 and forced0!=forced1
    r['original_ID_guard']={'natural_laws_equal':True,'named_H0_force_laws_differ':True}
    # A synchronized program uses ONE joint bit for both original sites.
    # Its deterministic configurations are internal computations, not newly
    # authorized observations. Resampling the bit at each site is a different law.
    source=root_two_hybrids();allocation={a:1 for a in 'abcd'}
    forced={}
    for b0,b1 in product((0,1),repeat=2):
        settings={'H0':b0,'H1':b1}
        com=compile_source(source,allocation,'common',settings)
        ind=compile_source(source,allocation,'independent',settings)
        assert com==ind
        forced[b0,b1]=com
    outcomes=set().union(*(law.keys() for law in forced.values()))
    shared={t:(forced[0,0].get(t,Q(0))+forced[1,1].get(t,Q(0)))/2 for t in outcomes}
    resampled={t:sum((law.get(t,Q(0)) for law in forced.values()),Q(0))/4 for t in outcomes}
    assert shared!=resampled and sum(shared.values())==sum(resampled.values())==1
    first=next(t for t in sorted(outcomes,key=repr) if shared[t]!=resampled[t])
    r['shared_program_register_guard']={'original_sites':['H0','H1'],
        'joint_bit_resampling_changes_authorized_law':True,
        'fully_forced_modes_match':True,'observed_rooted_topology':repr(first),
        'one_shared_bit_probability':str(shared[first]),
        'separately_resampled_bit_probability':str(resampled[first])}
    # Three input roots suffice to separate an independently routed bigon from
    # its pair-matched ordinary edge.  All finite natural edges remain positive.
    B=ForestAlgebra(3)
    independent=B.mul(B.edge(Q(1,2)),B.cell(Q(1,2),Q(1,2),Q(1,2),Q(1,2),'independent'))
    ordinary=B.edge(Q(3,16))
    assert all(independent[i]==ordinary[i] for i,(k,f) in enumerate(B.coords) if k<=2)
    ix=B.index[3,tuple(range(3))]
    assert independent[ix]-ordinary[ix]==-Q(1,4096)
    r['independent_small_cap_collision']={'all_cap_2_forest_coordinates_equal':True,'cap_3_no_merger_difference':'-1/4096'}
    # Exact Cauchy Jacobian controls at the independent algebraic boundary.  The
    # theorem uses continuity to enter the strict-positive source domain.
    dets=[]
    for d in range(1,9):
        gs=[sp.Rational(j,d+1) for j in range(1,d+1)]
        mat=sp.Matrix([[-sp.Rational(m*(m-1))*g/((1-g)*(1+(m-1)*g)) for g in gs] for m in range(2,d+2)])
        det=sp.factor(mat.det());assert det!=0
        dets.append({'dimension':d,'boundary_log_Jacobian_determinant':str(det)})
    r['independent_Cauchy_controls']=dets
    # Positive perturbation for one nontrivial dimension, evaluated directly
    # from the independent no-merger polynomials, not the boundary formula.
    d=4;gvar=sp.Symbol('g');xx=sp.Rational(1,1000);yy=sp.Rational(999,1000)
    gs=[sp.Rational(j,7) for j in range(1,d+1)]
    rows=[]
    for m in range(2,d+2):
        bm=sum(sp.binomial(m,k)*gvar**k*(1-gvar)**(m-k)*xx**comb(k,2)*yy**comb(m-k,2) for k in range(m+1))
        rows.append([sp.diff(bm,gvar).subs(gvar,g)/bm.subs(gvar,g) for g in gs])
    determinant=sp.factor(sp.Matrix(rows).det());assert determinant!=0
    r['independent_positive_rank_control']={'dimension':d,'x':str(xx),'y':str(yy),'weights':list(map(str,gs)),
        'determinant_nonzero':True,'all_parameters_strictly_interior':True}
    # Verify the all-size leading coefficient formula used for the genuinely
    # observable A-clade event (one B outgroup), separately from hidden probes.
    coeffs=[]
    for m in range(2,25):
        c=monophyly_polynomial(m)[comb(m,2)]
        expected=-Q(2,3) if m==2 else Q((-1)**(m-1)*2,(m-1)*comb(2*m-2,m-1))
        assert c==expected and c!=0
        coeffs.append({'m':m,'coefficient':str(c)})
    r['observable_monophyly_coefficients']=coeffs
    r['common_arbitrary_cap_collisions']=[common_cap_collision(m) for m in range(2,9)]
    # Exact exposing certificates used by the adaptive common-chain theorem.
    # The generic quantified certificate FINDER is not implemented by this test.
    xx=sp.Symbol('x')
    exposed=[]
    for atoms,weights in (([sp.Rational(1,2)],[sp.Rational(1)]),
                          ([sp.Rational(1,3),sp.Rational(2,3)],[sp.Rational(2,5),sp.Rational(3,5)])):
        M=2*len(atoms)+1;exponents=[comb(k,2) for k in range(1,M+1)]
        matrix=sp.Matrix([[a**e for e in exponents] for a in atoms]
                       +[[e*a**(e-1) if e else 0 for e in exponents] for a in atoms])
        null=matrix.nullspace();assert len(null)==1
        c=null[0]
        if c[0]<0:c=-c
        poly=sp.Poly(sum(v*xx**e for e,v in zip(exponents,c)),xx,domain=sp.QQ)
        signs=[sp.sign(v) for v in reversed(c) if v]
        variations=sum(a!=b for a,b in zip(signs,signs[1:]))
        assert c[0]>0 and variations==2*len(atoms)
        for a in atoms:assert poly.eval(a)==0 and poly.diff().eval(a)==0
        moments=[sum(w*a**e for a,w in zip(atoms,weights)) for e in exponents]
        assert sum(v*m for v,m in zip(c,moments))==0
        vandermonde=sp.Matrix([[a**e for a in atoms] for e in exponents])
        assert vandermonde.rank()==len(atoms)
        exposed.append({'atoms':list(map(str,atoms)), 'weights':list(map(str,weights)),
                        'interface_cap':M,'exposing_polynomial':str(sp.factor(poly.as_expr())),
                        'positive_roots_counting_multiplicity':variations,
                        'zero_expectation_exact':True, 'weights_unique':True})
    r['adaptive_common_exposing_certificates']=exposed
    # Calendar-bin obstruction: equal-arm COMMON bigons have a deterministic
    # population path. Two positive rate schedules have identical integrated
    # duration over an unobserved interval, for every copy cap, but different
    # pair survival at the interior time 1/2.
    old=[Q(1),Q(1),Q(1)];new=[Q(3,2),Q(1),Q(1,2)];dur=[Q(1,3)]*3
    assert sum(r*t for r,t in zip(old,dur))==sum(r*t for r,t in zip(new,dur))==1
    old_half=old[0]*dur[0]+old[1]*Q(1,6)
    new_half=new[0]*dur[0]+new[1]*Q(1,6)
    assert old_half==Q(1,2) and new_half==Q(2,3)
    r['calendar_bin_obstruction']={'interval':'(0,1)','positive_durations':list(map(str,dur)),
       'reference_pair_rates':list(map(str,old)),'alternative_pair_rates':list(map(str,new)),
       'same_total_coalescent_duration':'1','all_copy_caps_same_interval_forest_kernel':True,
       'interior_pair_survivals_at_half':['exp(-1/2)','exp(-2/3)'],
       'source_realization':'One equal-arm common-inheritance bigon with positive lower and upper connectors; place the interval within a pendant branch.'}
    r['not_executed']=['All-size positive independent collision QE construction','Full bounded-core enumeration',
                      'General clock-cell symbolic basis construction','General independent all-cap stopping algorithm',
                      'Independent review or proof-assistant verification']
    return r

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',default='adversarial-checks.json');a=p.parse_args()
    r=run();Path(a.output).write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({'output':a.output,'associativity_cases':r['labelled_grafting_associativity_cases'],
        'all_cap_common_collision_caps':[x['cap_M'] for x in r['common_arbitrary_cap_collisions']],
        'monophyly_coefficients':len(r['observable_monophyly_coefficients']),
        'all_assertions_passed':True},indent=2))
