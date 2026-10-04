"""Preserve a winning endpoint outside the constructor's chosen full support."""
import json
from pathlib import Path
from synthesize_policy import provider,compile_policy

ROOT=Path(__file__).resolve().parent

def main():
    models,_=provider()
    calls=[{'support':[0],'weights':['1','0']},{'support':[1],'weights':['0','1']}]
    result=compile_policy(models,calls,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    assert result['status']=='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND',result['status']
    output={'status':'PASS_WINNING_ENDPOINT_OUTSIDE_CHOSEN_FULL_SUPPORT',
            'endpoint_second_weight0':'0','second_support':[1],
            'certified_chosen_mixed_support_region':'0<w<1',
            'whole_menu_winning_fibre_not_identified_with_that_region':True,
            'inherited_two_forcing_strategy_not_a_new_mathematical_claim':True,
            'complete_source_decoder_and_whole_policy_receipt':result}
    (ROOT/'ENDPOINT-BRANCH-RECEIPT.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='complete_source_decoder_and_whole_policy_receipt'},indent=2))

if __name__=='__main__':main()
