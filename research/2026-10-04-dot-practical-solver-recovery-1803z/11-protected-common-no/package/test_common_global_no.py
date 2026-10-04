#!/usr/bin/env python3
"""Exact all-size COMMON certificate controls; no graph census expansion."""
import copy
import json
from pathlib import Path
from common_global_no import solve,CONTRACT
from verify_common_certificate import verify

ROOT=Path(__file__).resolve().parent
def request():
    return {'schema':'unknown-size-common-intervention-profile-v1','observation_kind':'exact_unranked_law','source_contract':CONTRACT,
            'protected_site':'H0','mechanisms':['common'],'taxa':['L0','L1','L2','L3'],
            'profiles':[{'id':'original-quartet','sample_panel':{f'L{i}':[f'L{i}'] for i in range(4)},
                         'coordinate_ids':['01|23','02|13','03|12'],'background_controls':{},
                         'laws':{'force0':['2/3','1/6','1/6'],'force1':['2/9','5/9','2/9'],'natural':['4/9','13/36','7/36']}}]}
def main():
    cases=[]
    q=request();assert solve(q)['status']=='UNKNOWN_PASSES_NECESSARY_COMMON_INTERVENTION_TEST';cases.append({'kind':'shared_interior_parameter_pass_is_NOT_SAT','request':q,'result':solve(q)})
    q=request();q['profiles'][0]['laws']['natural']=['1/3','1/3','1/3'];out=solve(q);assert out['status']=='GLOBAL_UNKNOWN_SIZE_UNSAT_FOR_DECLARED_COMMON_MODEL';assert verify(q,out)['status'].startswith('PASS');cases.append({'kind':'noncollinear_unknown_size_common_NO','request':q,'result':out,'independent_replay':verify(q,out)})
    q=request();q['profiles'][0]['laws']['natural']=q['profiles'][0]['laws']['force0'];out=solve(q);assert out['proof']['kind']=='COMMON_INTERIOR_PARAMETER_VIOLATION';verify(q,out);cases.append({'kind':'strict_positive_gamma_boundary','request':q,'result':out})
    q=request();q['profiles'][0]['laws']['force1']=q['profiles'][0]['laws']['force0'];out=solve(q);assert out['proof']['kind']=='FORCED_ROWS_EQUAL_NATURAL_DIFFERS';verify(q,out);cases.append({'kind':'equal_forced_rows','request':q,'result':out})
    # Each group separately passes at a different gamma; one SAME original
    # source across both profiles cannot independently refit those gammas.
    q=request();second=copy.deepcopy(q['profiles'][0]);second['id']='same-source-second-panel'
    from fractions import Fraction as F
    def mix(group,g):
        group['laws']['natural']=[str(g*F(a)+(1-g)*F(b)) for a,b in zip(group['laws']['force0'],group['laws']['force1'])]
    mix(q['profiles'][0],F(1,4));mix(second,F(3,4));q['profiles'].append(second);out=solve(q);assert out['proof']['kind']=='NONZERO_SHARED_PARAMETER_MINOR';verify(q,out);cases.append({'kind':'no_independent_profile_refitting','request':q,'result':out})
    q=request();q['profiles'][0]['laws']['natural']=['1/3','1/3','1/3'];q['mechanisms']=['common','independent'];out=solve(q);assert out['status'].startswith('UNKNOWN_UNION');verify(q,out);cases.append({'kind':'COMMON_NO_does_not_exclude_I_union','request':q,'result':out})
    failures=[]
    q=request();q['observation_kind']='DNA';failures.append(q)
    q=request();q['empirical_admission']={'status':'ADMITTED'};failures.append(q)
    q=request();q['profiles'][0]['laws']['natural']=[0.4,0.4,0.2];failures.append(q)
    q=request();q['profiles'][0]['laws']['natural']=['1/2','1/2'];failures.append(q)
    for q in failures:assert solve(q)['status']=='UNKNOWN_UNADMITTED_PROFILE'
    proof=copy.deepcopy(cases[1]['result']);proof['proof']['minor_value']='0'
    try:verify(cases[1]['request'],proof)
    except ValueError:pass
    else:raise AssertionError('Tampered minor accepted.')
    result={'status':'PASS_ALL_SIZE_COMMON_INTERVENTION_CERTIFICATE_CONTROLS','cases':cases,'unadmitted_controls':len(failures),
            'tamper_controls':1,'no_graph_or_word_bound_used':True,'generic_G3_completeness_claimed':False}
    (ROOT/'TEST-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))

if __name__=='__main__':main()
