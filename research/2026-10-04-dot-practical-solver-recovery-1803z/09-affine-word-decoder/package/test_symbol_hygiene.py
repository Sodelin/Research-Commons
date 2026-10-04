"""Abstract namespace controls; no biological source census is asserted."""
import json
from pathlib import Path
import sympy as sp
import z3
from compile_leaves import compile_policy
from verify_policy import guard

ROOT=Path(__file__).resolve().parent

def terminal_guard(result,history):
    node=result['policy']
    while node['kind']=='call':node=node['next']
    observations={f'h{i}_{j}':z3.RealVal(value) for i,row in enumerate(history) for j,value in enumerate(row)}
    accepted=[]
    for branch in node['branches']:
        truth,defined=guard(branch['guard'],observations)
        accepted.append(z3.is_true(z3.simplify(z3.And(truth,defined))))
    return any(accepted)

def main():
    cases=[]
    spellings=[('history','h0_0','h0_1'),
               ('future_history','h2_0','h2_1'),
               ('action','action_root_0','action_root_1'),
               ('source_display','_g7Source_model0_parameter0','_g7Source_model0_parameter1'),
               ('history_display','_g7History_step0_coordinate0','_g7History_step0_coordinate1'),
               ('auxiliary','sameOriginalSourceForRank!0','oneOriginalSourceParameter!0')]
    calls=[{'support':[0],'weights':['1','0']},
           {'support':[1],'weights':['0','1']},
           {'support':[0],'weights':['1','0']}]
    impossible=[['1/5','4/5'],['2/5','3/5'],['3/5','2/5']]
    possible=[['1/5','4/5'],['2/5','3/5'],['1/5','4/5']]
    for label,left,right in spellings:
        x,y=sp.symbols((left,right));a,b=sp.symbols(('freshSourceX','freshSourceY'))
        models=[{'variables':[x,y],'laws':[[x,1-x],[y,1-y]],'target':'T'},
                {'variables':[a,b],'laws':[[a,1-a],[b,1-b]],'target':'T'}]
        result=compile_policy(models,calls,[[0],[1]],[[],[]],[3,2,0])
        assert result['status']=='WHOLE_ACTION_WORD_TARGET_DECODER_COMPILED_AND_VERIFIED_SAME_BACKEND',result
        assert not terminal_guard(result,impossible),'Inconsistent repeated-row history admitted.'
        assert terminal_guard(result,possible),'Legal source-name collision caused loss of a real history.'
        assert result['symbol_identity_provenance']['sources'][0]['parameters'][0]['original_name']==left
        cases.append({'namespace':label,'original_source_names':[left,right],
                      'legal_names_capture_avoiding_canonicalization':True,
                      'impossible_repeated_row_history_rejected':True,'real_history_retained':True})
    out={'status':'PASS_TYPED_CAPTURE_AVOIDING_SYMBOL_IDENTITY_CONTROLS',
         'cases':cases,'abstract_encoding_controls_not_new_biological_sources':True,
         'generic_affine_compiler_independent_acceptance_claimed':False}
    (ROOT/'SYMBOL-HYGIENE-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
