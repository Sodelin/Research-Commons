#!/usr/bin/env python3
"""Actual admitted image compiler plus fail-closed implementation controls."""
import json
from pathlib import Path
import sympy as sp
import z3
from compile_leaves import compile_policy
from test_policy_verification import models

ROOT=Path(__file__).resolve().parent
def main():
    source=models();menu=[[0],[1],[0,1]];sites=[['H0'],['H0']]
    calls=[{'support':[0],'weights':['1','0']},{'support':[0,1],'weights':['h0_0','1-h0_0']}]
    out=compile_policy(source,calls,menu,sites,[2,2,1]);assert out['status']=='WHOLE_ACTION_WORD_TARGET_DECODER_COMPILED_AND_VERIFIED_SAME_BACKEND',out
    assert len(out['rank_receipts'])==9 and all(r['status']=='unsat' for r in out['rank_receipts'])
    (ROOT/'COMPILED-DECODER-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
    (ROOT/'COMPILED-POLICY.json').write_text(json.dumps(out['policy'],indent=2)+'\n')
    controls=[]
    for label,word in [('insufficient_history',calls[:1]),('same_row_repeated',[calls[0],calls[0]]),
                       ('future_observation',[{'support':[0],'weights':['h0_0','1-h0_0']}]),
                       ('illegal_normalization',[calls[0],{'support':[0,1],'weights':['h0_0','h0_0']}])]:
        bad=compile_policy(source,word,menu,sites,[2,2,1]);assert bad['status'].startswith('UNKNOWN'),bad;controls.append({'label':label,'result':bad})
    x=sp.Symbol('abstractSourceParameter')
    abstract=[{'variables':[x],'laws':[[x*x,1-x*x]],'target':0}]
    bad=compile_policy(abstract,[{'support':[0],'weights':['1']}],[[0]],[[]],[1,1,0]);assert bad['status'].startswith('UNKNOWN'),bad
    controls.append({'label':'nonlinear_abstract_not_a_biological_source','result':bad})
    for label,word in [('malformed_action_syntax',[{'support':[0],'weights':['(','0']}]),
                       ('expression_nesting_resource',[{'support':[0],'weights':['+'.join(['1']*1100),'0']}]),
                       ('word_length_resource',[calls[0]]*129)]:
        bad=compile_policy(source,word,menu,sites,[200,2,1]);assert bad['status'].startswith('UNKNOWN'),bad;controls.append({'label':label,'result':bad})
    (ROOT/'COMPILER-NEGATIVE-CONTROLS.json').write_text(json.dumps(controls,indent=2)+'\n')
    # The backend obstruction is retained: variable-coefficient projection of
    # the actual SAME-source two-step relation leaves a quantified source t.
    s,t=z3.Reals('sameSourceS sameSourceT');h=z3.Reals('h0_0 h0_1 h0_2');y=z3.Reals('h1_0 h1_1 h1_2');w=h[0]
    f=[1-2*s/3,s/3,s/3];g=[t/3,1-2*t/3,t/3]
    formula=z3.Exists([s,t],z3.And(s>0,s<1,t>0,t<1,*[f[i]==h[i] for i in range(3)],*[w*f[i]+(1-w)*g[i]==y[i] for i in range(3)]))
    goal=z3.Goal();goal.add(formula);partial=z3.TryFor(z3.Tactic('qe'),3000)(goal).as_expr()
    def quantified(e):return z3.is_quantifier(e) or any(quantified(v) for v in e.children())
    obstruction={'status':'UNKNOWN_PARTIAL_SYMBOLIC_SOURCE_PROJECTION' if quantified(partial) else 'COMPLETED_BACKEND_PROJECTION',
                 'input_smt2':formula.sexpr(),'output_smt2':partial.sexpr(),'z3':z3.get_version_string(),
                 'new_decoder_does_not_treat_residual_as_false':True,'shared_source_parameters':True}
    (ROOT/'BASIC-QE-OBSTRUCTION.json').write_text(json.dumps(obstruction,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'automatically_compiled_target_families':len(out['policy']['next']['next']['branches']),
                      'original_source_rank_coverage_checks':len(out['rank_receipts']),'negative_controls':len(controls),
                      'baseline_projection':obstruction['status'],'generic_action_search_claimed':False},indent=2))

if __name__=='__main__':main()
