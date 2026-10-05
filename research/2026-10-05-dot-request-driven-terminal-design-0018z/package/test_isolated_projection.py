#!/usr/bin/env python3
"""Independent hand formula controls for retained isolated root coordinates."""
import copy,json
from pathlib import Path
import sympy as sp
import z3
from project_branch_word import project_branch_word
from verify_algebraic_policy import verify,guard
from cad_action_sections import ActionSectionWriter
from algebraic_history_point import evaluate_section,encode_exact
from cad_value import evaluate_value
ROOT=Path(__file__).resolve().parent

def run():
    source=sp.Symbol('action_root_test') # Intentional source/auxiliary spelling collision.
    models=[{'variables':[source],'laws':[[source,1-source]],'target':'x'}]
    first={'support':[0],'weights':['1']}
    root={'name':'action_root_test','coefficients':['-h0_0','0','1'],'lower':'0','upper':'1'}
    menu=[[0]];sites=[[]];budget=[2,1,0];controls=[]
    for name,coeff,extra in [('ordinary','-h0_0',True),('cancelled_written_domain','-h0_0*(h0_0-1/2)/(h0_0-1/2)',False)]:
        section=copy.deepcopy(root);section['coefficients'][0]=coeff
        call={'support':[0],'weights':['1'],'sections':[section]}
        projected=project_branch_word(models,[first,call],menu,sites,budget)
        assert projected['status']=='COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED',projected
        assert projected['section_determinism_claimed_by_projection'] is False
        assert projected['policy_candidate']['next']['sections']==[section]
        final=projected['policy_candidate']['next']['next'];branch=final['branches'][0]
        h=z3.Real('h0_0');r=z3.Real('action_root_test');h01=z3.Real('h0_1');h10=z3.Real('h1_0');h11=z3.Real('h1_1')
        actual,defined=guard(branch['guard'],{'h0_0':h,'h0_1':h01,'h1_0':h10,'h1_1':h11,'action_root_test':r})
        expected=z3.And(h>0,h<1,h01==1-h,h10==h,h11==1-h,r>0,r<1,r*r==h,
                        z3.BoolVal(True) if extra else h!=z3.RealVal('1/2'))
        solver=z3.SolverFor('QF_NRA');solver.add(z3.Xor(z3.And(defined,actual),expected));status=solver.check();assert status==z3.unsat
        controls.append({'name':name,'status':str(status),'query_smt2':solver.to_smt2(),'one_source_shared_across_both_rows':True})
    positive=project_branch_word(models,[first,{'support':[0],'weights':['1'],'sections':[root]}],menu,sites,budget)
    checked=verify(models,positive['policy_candidate'],menu,sites,budget)
    assert checked['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND',checked
    for name,change in [('endpoint_root',{'coefficients':['0','0','1']}),('multiple_roots',{'coefficients':['3/16','-1','1']}),('hidden_parameter',{'coefficients':['-source_gamma','0','1']}),('future_response',{'coefficients':['-h1_0','0','1']}),('duplicate_section_name',None)]:
        section=copy.deepcopy(root)
        if change:section.update(change)
        call={'support':[0],'weights':['1'],'sections':[section]+([copy.deepcopy(section)] if change is None else [])}
        projected=project_branch_word(models,[first,call],menu,sites,budget)
        if name in ('hidden_parameter','future_response','duplicate_section_name'):
            assert projected['status']=='UNKNOWN_UNSUPPORTED_OR_RESOURCE_LIMIT',projected
            status=projected['status']
        else:
            assert projected['status']=='COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED'
            out=verify(models,projected['policy_candidate'],menu,sites,budget)
            assert out['status']=='INVALID_OR_REFUTED_POLICY',out
            status=out['status']
        controls.append({'name':name,'status':status,'projection_never_a_policy_certificate':True})
    known={'h0_0':{'kind':'rational','value':'1/2'}}
    for degree in (2,3,5):
        ast={'kind':'principal_power','base':{'kind':'observation','name':'h0_0'},'numerator':1,'denominator':degree}
        writer=ActionSectionWriter(1);call=writer.call([ast],[0]);section=call['sections'][0]
        a,value=evaluate_section(section,known);b,exported=evaluate_value(ast,known)
        assert a['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND',a
        assert b['status']=='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND',b
        assert z3.is_true(z3.simplify(value==exported))
        controls.append({'name':'principal_positive_root_degree_'+str(degree),'status':'EXACT_AST_SECTION_VALUE_MATCH','encoding':encode_exact(value)})
    malformed=[{'kind':'root','coefficients':[{'kind':'rational','value':'-1'},{'kind':'rational','value':'1'}],'real_root_index':1},
               {'kind':'principal_power','base':{'kind':'rational','value':'1/2'},'numerator':1,'denominator':0},
               {'kind':'observation','name':'source_gamma'},
               {'kind':'observation','name':'action_root_undeclared'},
               {'kind':'principal_power','base':{'kind':'rational','value':'1/2'},'numerator':1,'denominator':129}]
    for i,ast in enumerate(malformed):
        try:ActionSectionWriter(1).call([ast],[0])
        except ValueError as e:controls.append({'name':'unsupported_AST_'+str(i),'status':'UNKNOWN_BOUNDARY_REJECTED','reason':str(e)})
        else:raise AssertionError('Unsupported AST was accepted.')
    receipt={'status':'PASS_ISOLATED_ROOT_PROJECTION_AND_PRINCIPAL_CAD_ACTION_BINDING','controls':controls,
             'one_source_shared_parameters':True,'pure_projection_determinism_claimed':False,
             'complete_policy_IVT_uniqueness_gate_mandatory':True,'trust':'SAME_BACKEND; two independent hand-transcribed global formulas'}
    (ROOT/'ISOLATED-PROJECTION-CONTROLS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'controls':len(controls)}))
if __name__=='__main__':run()
