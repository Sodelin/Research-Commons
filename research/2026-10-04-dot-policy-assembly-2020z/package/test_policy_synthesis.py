"""Whole generated-policy coverage and unsupported-boundary controls."""
import copy,json
from pathlib import Path
from synthesize_policy import synthesize,provider
from verify_policy import verify

ROOT=Path(__file__).resolve().parent

def main():
    result=json.loads((ROOT/'SYNTHESIS-RESULT.json').read_text())
    assert result['status']=='AUTOMATIC_SOURCE_ADMITTED_ADAPTIVE_POLICY_SYNTHESIZED_AND_VERIFIED_SAME_BACKEND'
    assert result['policy_word_was_supplied_by_caller'] is False
    assert result['complete_reachable_response_coverage'] is True
    assert result['source_projection_and_whole_policy_certificate']['verification']['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND'
    sources,_=provider();base=result['request'];negative=[]
    requests=[]
    for label,patch in [('different_provider',{'source_provider':'unknown_original_size'}),
                        ('changing_mechanism',{'mechanism':'per-row-fit'}),
                        ('calls_too_small_for_this_witness',{'budget':[1,2,1]}),
                        ('configuration_cap',{'budget':[2,1,1]}),('site_cap',{'budget':[2,2,0]}),
                        ('Pareto_not_implemented',{'prefer_adaptive':False}),
                        ('DNA_observation',{'observation_kind':'DNA'}),
                        ('empirical_payload',{'empirical_admission':{'status':'ADMITTED'}}),
                        ('caller_supplied_word',{'calls':[]})]:
        request={**base,**patch};out=synthesize(request)
        assert out['status'].startswith('UNKNOWN') and out['mathematical_budget_NO_claimed'] is False,(label,out['status'])
        negative.append({'control':label,'result':out})
    mutations=[]
    for label in ('coverage_hole','hidden_source_action','future_action','wrong_target'):
        policy=copy.deepcopy(result['policy'])
        if label=='coverage_hole':policy['next']['next']['branches'].pop()
        elif label=='hidden_source_action':policy['next']['weights']=['originalProtectedNaturalGammaH0','1-originalProtectedNaturalGammaH0']
        elif label=='future_action':policy['next']['weights']=['h1_0','1-h1_0']
        else:policy['next']['next']['branches'][0]['next']['target']=[99]
        checked=verify(sources,policy,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
        assert checked['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND',label
        mutations.append({'control':label,'result':checked})
    out={'status':'PASS_WHOLE_GENERATED_POLICY_AND_FAIL_CLOSED_SYNTHESIS_CONTROLS',
         'source_admitted_policy_generated_without_supplied_word':True,'unsupported_requests':negative,
         'whole_policy_semantic_mutations':mutations,'candidate_section_exhaustion_is_not_budget_NO':True,
         'complete_general_CAD_policy_extraction_claimed':False}
    (ROOT/'SYNTHESIS-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'unsupported_request_controls':len(negative),
                      'whole_policy_mutations':len(mutations)},indent=2))

if __name__=='__main__':main()
