"""Targeted fail-closed tests after independently raised adapter objections."""
from fractions import Fraction as F
from pathlib import Path
from hashlib import sha256
import json
from robust_support import Contract,GuardedOracle,RecoveryAbstention,Certificate,certify,sufficient_prefix,exceeds_twice_radius
from cf_confidence import ideal_cf_boxes,safe_controller_answer


def main():
    tested=[]
    def check(name,condition):
        assert condition,name;tested.append(name)
    C=Contract(F(1,8),(F(1,128),))
    check('squared_radius_equality_is_not_certificate',not exceeds_twice_radius(F(1,2),F(1,16)))
    check('strict_squared_boundary_can_certify',exceeds_twice_radius(F(501,1000),F(1,16)))
    q=(0,1,2,3);q2=(0,1,2,4)
    calls=[]
    oracle=GuardedOracle(lambda x:calls.append(x) or [(1,1,1)],C,1,F(1,20))
    for quartet in (q,q2):
        try:oracle(quartet)
        except RecoveryAbstention as exc:check('sticky_abstention_'+str(quartet),str(exc)=='INCONCLUSIVE')
        else:raise AssertionError('must abstain')
    check('aborted_callback_not_reentered',calls==[q] and oracle.attempted=={q})
    calls=[]
    complete=GuardedOracle(lambda x:calls.append(x) or [(640000,160000,160000)],C,1,F(1,20))
    check('large_source_counts_certify_tree',complete(q)==1)
    check('memoized_query_consumes_no_more_data',complete(q)==1 and calls==[q])
    for quartet in (q2,q):
        try:complete(quartet)
        except RecoveryAbstention as exc:check('sticky_cap_'+str(quartet),str(exc)=='QUERY_LIMIT')
        else:raise AssertionError('must cap and latch')
    broken=GuardedOracle(lambda x:[(1,2.5,3)],C,1,F(1,20))
    for quartet in (q,q2):
        try:broken(quartet)
        except RecoveryAbstention as exc:check('input_failure_latched_'+str(quartet),str(exc)=='INPUT_ERROR')
        else:raise AssertionError('bad callback must abort')
    fabricated=GuardedOracle(lambda x:[(1,1,1)],C,1,F(1,20),provider=lambda *a,**k:Certificate('CERTIFIED',(7,), (True,)*3,(False,)*3,(3,)))
    try:fabricated(q)
    except RecoveryAbstention as exc:check('illegal_provider_mask_rejected',str(exc)=='INVALID_CERTIFICATE')
    else:raise AssertionError('illegal mask')
    bad=Contract(F(1,8),(F(1,8),))
    check('nonpositive_margin_no_sufficient_prefix',sufficient_prefix(bad,1,F(1,20)) is None)
    for queries,delta in ((0,F(1,20)),(True,F(1,20)),(1,0),(1,0.05)):
        try:sufficient_prefix(bad,queries,delta)
        except ValueError:tested.append('invalid_risk_rejected_'+str((queries,delta)))
        else:raise AssertionError('risk validation skipped')
    check('zero_data_preserves_candidates',certify([(0,0,0)],C,1,F(1,20)).candidates==C.legal_masks)
    check('contradiction_abstains',certify([(100000,100000,100000)],C,1,F(1,20)).status=='MODEL_INCOMPATIBLE')
    check('unknown_solver_is_inconclusive',safe_controller_answer({'full_class_status':'INCONCLUSIVE','solver_feasible_targets':{1},'all_class_outer_candidates':'ALL_ADMITTED_TARGETS'})['status']=='INCONCLUSIVE')
    report={'scope':'root-executed targeted adapter regressions after independent objections; no proof of scientific inputs','checks':tested,'all_passed':True,
            'sha256':{p.name:sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(__file__).with_name('robust_support.py'),Path(__file__).with_name('cf_confidence.py'))}}
    Path(__file__).with_name('guard-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'checks':len(tested),'all_passed':True}))

if __name__=='__main__':
    if not __debug__:raise RuntimeError('run without -O')
    main()
