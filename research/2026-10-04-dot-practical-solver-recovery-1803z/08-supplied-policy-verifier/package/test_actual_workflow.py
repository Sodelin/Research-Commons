#!/usr/bin/env python3
"""Small actual-export, controller and fail-closed interface replay."""
import copy
import json
from pathlib import Path
from verify_actual_policy import run
from execute_actual_policy import replay

ROOT=Path(__file__).resolve().parent
def main():
    q=json.loads((ROOT/'ACTUAL-SOURCE-POLICY-REQUEST.json').read_bytes());verification=run(q,ROOT/'runs/final-actual-verification')
    assert verification['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND'
    assert verification['actual_source_models_sha256']=='78da02b2099204557d1414aec1d10c1dd2063b22e012c72834b00dafe985c402'
    (ROOT/'ACTUAL-VERIFICATION-RECEIPT.json').write_text(json.dumps(verification,indent=2)+'\n')
    execution=json.loads((ROOT/'ACTUAL-EXECUTION-REQUEST.json').read_bytes());paths=[]
    for label,responses in [('root',[]),('leaf',[['2/3','1/6','1/6']]),('impossible',[['1/3','1/3','1/3']])]:
        e=copy.deepcopy(execution);e['observed_responses']=responses;out=replay(e,ROOT/f'runs/final-{label}')
        expected={'root':'NEXT_VERIFIED_SOURCE_ADMITTED_ACTION','leaf':'IDENTIFIED_ACTUAL_TARGET_BY_VERIFIED_ADAPTIVE_POLICY_SAME_BACKEND','impossible':'UNKNOWN_OR_IMPOSSIBLE_ACTUAL_HISTORY'}[label]
        assert out['status']==expected,out;paths.append({'label':label,'result':out})
    controls=[]
    bad=copy.deepcopy(q);bad['design_request']['limits']['max_sources']=1
    out=run(bad,ROOT/'runs/incomplete-catalogue');assert out['status']=='UNKNOWN_INCOMPLETE_ACTUAL_SOURCE_EXPORT';controls.append({'kind':'incomplete_catalogue','result':out})
    for metadata in [{'status':'ADMITTED'},{'status':'NOT_ADMITTED_TO_EMPIRICAL_SOLVER'},{'dataset_hash':'unverified'}]:
        bad=copy.deepcopy(q);bad['design_request']['empirical_admission']=metadata
        try:run(bad,ROOT/'runs/rejected-empirical')
        except ValueError as e:controls.append({'kind':'unsupported_empirical_metadata','reason':str(e)})
        else:raise AssertionError('Unsupported empirical payload accepted.')
    bad=copy.deepcopy(execution);bad['observed_responses']=[[0.66,0.17,0.17]]
    try:replay(bad,ROOT/'runs/rejected-float')
    except ValueError as e:controls.append({'kind':'floating_frequencies','reason':str(e)})
    else:raise AssertionError('Floating data accepted.')
    receipt={'status':'PASS_ACTUAL_EXPORT_POLICY_VERIFICATION_AND_EXECUTION','actual_source_count':15,
             'verification_status':verification['status'],'unchanged_actual_model_hash':verification['actual_source_models_sha256'],
             'paths':paths,'negative_controls':controls,'generic_synthesis_claimed':False}
    (ROOT/'ACTUAL-WORKFLOW-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'actual_source_count':15,'path_cases':len(paths),'negative_controls':len(controls)},indent=2))

if __name__=='__main__':main()
