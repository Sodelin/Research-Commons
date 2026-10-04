"""Fresh admitted source-word nuisance-gamma and encoding-boundary checks."""
import json
from pathlib import Path
import sys
import sympy as sp
import z3
from compile_projected_word import compile_policy, parsed_action

sys.path.insert(0, str(Path(__file__).resolve().parent/'providers'))
from test_policy_verification import models
from compile_leaves import compile_policy as old_pivot_compile
from verify_policy import guard

ROOT=Path(__file__).resolve().parent

def accepts(result,history):
    node=result['policy']
    while node['kind']=='call':node=node['next']
    observed={f'h{i}_{j}':z3.RealVal(str(v)) for i,row in enumerate(history) for j,v in enumerate(row)}
    return any(z3.is_true(z3.simplify(z3.And(*guard(b['guard'],observed)))) for b in node['branches'])

def main():
    sources=models()
    for model in sources:model['variables'] += [sp.Symbol('originalProtectedNaturalGammaH0')]
    calls=[{'support':[0],'weights':['1','0']}, {'support':[0,1],'weights':['h0_0','1-h0_0']}]
    out=compile_policy(sources,calls,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    (ROOT/'FRESH-NUISANCE-GAMMA-ATTEMPT.json').write_text(json.dumps(out,indent=2)+'\n')
    assert out['status']=='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND', {k:v for k,v in out.items() if k not in ('policy','verification')}
    old=old_pivot_compile(sources,calls,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    assert old['status'].startswith('UNKNOWN')
    (ROOT/'INHERITED-PIVOT-NUISANCE-UNKNOWN.json').write_text(json.dumps(old,indent=2)+'\n')
    (ROOT/'FRESH-PROJECTED-POLICY.json').write_text(json.dumps(out['policy'],indent=2)+'\n')
    (ROOT/'FRESH-WHOLE-POLICY-RECEIPT.json').write_text(json.dumps(out['verification'],indent=2)+'\n')
    x,z=sp.symbols('abstractCurrentSourceX abstractCurrentSourceZ')
    abstract=[{'variables':[x,z],'laws':[[z,1-z],[x,1-x],[1-x,x]],'target':'abstract'}]
    word=[{'support':[0],'weights':['1','0','0']},{'support':[1,2],'weights':['0','h0_0','1-h0_0']}]
    rank=compile_policy(abstract,word,[[0],[1,2]],[[],[],[]],[2,3,0])
    assert rank['status']=='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND',rank
    points=0
    for a in [sp.Rational(i,8) for i in range(1,8)]:
        for b in [sp.Rational(j,8) for j in range(9)]:
            truth=(b==a if a==sp.Rational(1,2) else min(a,1-a)<b<max(a,1-a))
            assert accepts(rank,[[a,1-a],[b,1-b]])==truth,(a,b)
            points+=1
    (ROOT/'FRESH-ABSTRACT-RANK-DROP-CONTROL.json').write_text(json.dumps({'status':rank['status'],'rational_inverse_points_checked':points,'model_is_abstract_encoding_control':True,'receipt':rank},indent=2)+'\n')
    h=sp.Dummy('typedEarlierHistory')
    for text in ['h0_0/h0_0','(1/h0_0)**0','0*(1/h0_0)']:
        value,domains=parsed_action(text,{'h0_0':h});assert domains and any(sp.cancel(d)==h for d in domains)
    controls=[]
    for label,badword,kwargs in [
        ('hidden_source_action',[{'support':[0],'weights':['originalProtectedNaturalGammaH0','0']}],{}),
        ('future_observation',[{'support':[0],'weights':['h0_0','0']}],{}),
        ('malformed_syntax',[{'support':[0],'weights':['(','0']}],{}),
        ('float',[{'support':[0],'weights':['1.0','0']}],{}),
        ('resource_pairs',calls,{'max_pairs':1}),
        ('written_zero_denominator',[calls[0],{'support':[0,1],'weights':['(1/(h0_0-h0_0))**0/2','1/2']}],{})]:
        bad=compile_policy(sources,badword,[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1],**kwargs)
        assert bad['status'].startswith('UNKNOWN'),(label,bad['status'])
        controls.append({'label':label,'result':bad})
    # Legal input spellings remain accepted through typed identities.
    spellings=[('h0_0','h0_1'),('_g7History_step0_coordinate0','action_root_0'),('sourceA_0','oneOriginalSourceParameter!0')]
    namespace=[]
    for left,right in spellings:
        u,v=sp.symbols((left,right))
        m=[{'variables':[u,v],'laws':[[u,1-u],[v,1-v]],'target':'same'}]
        w=[{'support':[0],'weights':['1','0']},{'support':[1],'weights':['0','1']},{'support':[0],'weights':['1','0']}]
        result=compile_policy(m,w,[[0],[1]],[[],[]],[3,2,0])
        assert result['status']=='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND',result
        legal=[[sp.Rational(1,5),sp.Rational(4,5)],[sp.Rational(2,5),sp.Rational(3,5)],[sp.Rational(1,5),sp.Rational(4,5)]]
        impossible=legal[:2]+[[sp.Rational(3,5),sp.Rational(2,5)]]
        assert accepts(result,legal) and not accepts(result,impossible)
        namespace.append({'names':[left,right],'legal_history_retained':True,'inconsistent_shared_row_rejected':True})
    (ROOT/'FRESH-WORD-BOUNDARY-CONTROLS.json').write_text(json.dumps({'negative':controls,'typed_namespace':namespace,'written_division_domains_before_simplification':True},indent=2)+'\n')
    print(json.dumps({'status':out['status'],'source_models':len(sources),'source_variables_per_model':3,
                     'target_families':len(out['policy']['next']['next']['branches']),
                     'abstract_rank_drop_inverse_points':points,'negative_controls':len(controls),
                     'namespace_controls':len(namespace),'new_biological_census':False,'old_lost_PASS_inherited':False},indent=2))

if __name__=='__main__':main()
