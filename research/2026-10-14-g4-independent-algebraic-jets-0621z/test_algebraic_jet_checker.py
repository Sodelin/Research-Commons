"""Exact controls for the polynomial certificate core. No G4 source fixtures."""
from __future__ import annotations
import copy
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random
import algebraic_jet_checker as C

def term(c, ex):
    return {'coefficient':c, 'exponents':ex}

def radical():
    return {'schema':'algebraic_margin_jet_v1',
        'embedding':{'polynomial':['-2','0','1'], 'interval':['1','2']},
        'base':[['0'],['0']], 'jets':[{'1':['0','1']},{'1':['1']}],
        'residuals':[[term(['1'],[2,0]),term(['-2'],[0,2])]],
        'distinguishing':[term(['1'],[0,1])], 'order':19,
        'example_scope':'Algebraic countercontrol, NOT an admitted G4 source'}

def parabola():
    return {'schema':'algebraic_margin_jet_v1',
        'embedding':{'polynomial':['0','1'], 'interval':['-1','1']},
        'base':[['0'],['0']], 'jets':[{'1':['1']},{'2':['1'],'37':['1']}],
        'residuals':[[term(['1'],[0,1]),term(['-1'],[2,0])]],
        'distinguishing':[term(['1'],[1,0])], 'order':37,
        'example_scope':'Polynomial exactification control, NOT an admitted G4 source'}

def outcome(data, max_order=256):
    try:
        return C.verify(data,max_order), None
    except (C.InvalidCertificate, C.ResourceLimit) as exc:
        return None, type(exc).__name__+': '+str(exc)

def main():
    checks = {}
    details = {}
    a = radical()
    result,err = outcome(a)
    checks['algebraic_exact_path_accepted'] = result is not None
    details['algebraic_result'] = result
    checks['degree_dimension_and_threshold_computed'] = result is not None and result['error_exponent']=='18' and result['strict_threshold']=='18'
    checks['no_physical_or_master_promotion'] = result is not None and not result['physical_source_binding_verified'] and not result['legal_observation_binding_verified'] and not result['g4_master_established']
    p = parabola()
    # The coefficient at t^q is not part of a q-jet; dropping it preserves
    # every claimed lower coefficient and gives the same margin certificate.
    p['jets'][1].pop('37')
    r,err = outcome(p)
    checks['parabola_jet_accepted'] = r is not None and r['strict_threshold']=='36'
    # A genuinely non-exact jet still passes the sufficient order criterion:
    # x=t+t^36,y=t^2 gives residual -2t^37-t^72, q=37>2*18.
    apx=copy.deepcopy(p); apx['jets'][0]['36']=['1']
    rr,ee=outcome(apx)
    checks['nonexact_approximate_jet_accepted_with_sufficient_order']=rr is not None
    af=C.RealEmbedding(apx['embedding'])
    aj=[{1:C.ONE,36:C.ONE},{2:C.ONE}]
    ar=C.compose(C.parse_mp(apx['residuals'][0],2,af),aj,af,38)
    checks['accepted_approximate_jet_residual_starts_at_exact_order']=ar=={37:(Q(-2),)}
    # A perturbation included below the claimed order must be rejected.
    p2=copy.deepcopy(p); p2['order']=38; p2['jets'][1]['37']=['1']
    r,err = outcome(p2)
    checks['nonzero_full_residual_detected'] = r is None and 'Residual row' in err
    p3=copy.deepcopy(p); p3['order']=37; p3['residuals'][0].append(term(['1'],[37,0]))
    r,err=outcome(p3)
    # A supplied degree 37 map requires a larger exponent. Do not trust a
    # user-declared old degree from a different map.
    checks['actual_degree_prevents_underdeclared_bound'] = r is None and 'threshold' in err
    b=radical(); b['jets'][0]['1']=['99/70']
    r,err=outcome(b)
    checks['close_rational_approximation_rejected_exactly'] = r is None and 'Residual row' in err
    b=radical(); b['order']=18
    r,err=outcome(b)
    checks['equal_threshold_rejected'] = r is None and 'threshold' in err
    b=radical(); b['embedding']['interval']=['-2','-1']
    r,err=outcome(b)
    checks['wrong_real_conjugate_rejected_by_positivity'] = r is None and 'negative leading' in err
    b['jets'][0]['1']=['0','-1']
    r,err=outcome(b)
    checks['consistent_negative_embedding_accepted'] = r is not None
    b=radical(); b['jets'][1]={}
    r,err=outcome(b)
    checks['frozen_boundary_rejected'] = r is None and 'forbidden boundary' in err
    b=radical(); b['distinguishing']=copy.deepcopy(b['residuals'][0])
    r,err=outcome(b)
    checks['vanishing_distinction_rejected'] = r is None and 'distinguishing' in err
    b=radical(); b['distinguishing']=[term(['1'],[0,2])]
    r,err=outcome(b)
    checks['distinction_margin_checked_separately'] = r is None and 'distinction threshold' in err
    b=radical(); b['residuals'].append([term(['1'],[1,0])])
    r,err=outcome(b)
    checks['all_supplied_rows_checked_on_same_tuple'] = r is None and 'row 1' in err
    b=radical(); b['embedding']['interval']=['-2','2']
    r,err=outcome(b)
    checks['multiple_roots_in_embedding_interval_rejected'] = r is None and 'exactly one' in err
    b=radical(); b['embedding']['polynomial']=['4','0','-4','0','1']
    r,err=outcome(b)
    checks['repeated_embedding_polynomial_rejected'] = r is None and 'squarefree' in err
    b=radical(); b['embedding']['polynomial']=['1','0','1']
    r,err=outcome(b)
    checks['nonreal_embedding_rejected'] = r is None and 'exactly one' in err
    b=radical(); b['jets'][0]['1']=[1.41421356237]
    r,err=outcome(b)
    checks['floating_point_coefficients_rejected'] = r is None and 'floats' in err
    b=radical(); b['base'][0]=['1/2']
    r,err=outcome(b)
    checks['fixed_base_mismatch_rejected'] = r is None and 'fixed base' in err
    b=radical(); b['source_binding']={'verified':True,'g4_master_established':True}
    r,err=outcome(b)
    checks['untrusted_binding_flags_cannot_promote_verdict'] = r is not None and not r['physical_source_binding_verified'] and not r['g4_master_established']
    b=radical(); b['embedding']['polynomial']=['6','-2','-3','1']
    r,err=outcome(b)
    checks['reducible_squarefree_embedding_root_specific_equality'] = r is not None
    b['distinguishing']=[term(['-2','0','1'],[0,0])]
    r,err=outcome(b)
    checks['selected_root_zero_not_only_remainder_zero'] = r is None and 'distinguishing' in err
    r,err=outcome(radical(),max_order=10)
    checks['resource_limit_is_not_mathematical_rejection'] = r is None and err.startswith('ResourceLimit')
    # Correct approximate lift with residual exactly t^q but degree two:
    # p=(t, t^2+t^37) has residual order 37. Its valid 37-jet discards t^37.
    # Separately check all composition coefficients up to degree 37.
    fld=C.RealEmbedding(p['embedding'])
    fulljets=[{1:C.ONE},{2:C.ONE,37:C.ONE}]
    residual=C.compose(C.parse_mp(p['residuals'][0],2,fld),fulljets,fld,38)
    checks['approximate_parabola_residual_exactly_t37']= residual == {37:C.ONE}
    # Orthogonal sign oracle for A+B sqrt(2), based only on rational squares.
    def elementary_sign(A,B):
        if B==0: return (A>0)-(A<0)
        if A==0: return (B>0)-(B<0)
        if A>0 and B>0: return 1
        if A<0 and B<0: return -1
        return ((A*A>2*B*B)-(A*A<2*B*B))*((A>0)-(A<0))
    rng=random.Random(14062026)
    fld=C.RealEmbedding(radical()['embedding'])
    sign_ok=True
    for _ in range(300):
        A,B=Q(rng.randint(-40,40),rng.randint(1,13)),Q(rng.randint(-40,40),rng.randint(1,13))
        sign_ok &= fld.sign(C.trim((A,B)))==elementary_sign(A,B)
    checks['300_quadratic_sign_checks_against_distinct_exact_oracle']=bool(sign_ok)
    checks['sturm_cubic_three_real_roots']=C.roots((Q(0),Q(-1),Q(0),Q(1)),Q(-2),Q(2))==3
    receipt={'all_passed':all(checks.values()),'check_count':len(checks),'checks':checks,
             'details':details,'scope':'Exact arithmetic and certificate controls only; all fixtures are abstract polynomial examples, NOT G4 source rivals',
             'checker_sha256':hashlib.sha256(Path(C.__file__).read_bytes()).hexdigest(),
             'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    Path(__file__).with_name('example-algebraic-certificate.json').write_text(json.dumps(a,indent=2,sort_keys=True)+'\n')
    Path(__file__).with_name('example-rational-certificate.json').write_text(json.dumps(p,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))
    if not receipt['all_passed']:
        raise SystemExit(1)

if __name__=='__main__':
    main()
