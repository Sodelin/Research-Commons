#!/usr/bin/env python3
"""Configuration, exact pruning equivalence and complete-policy controls."""
import copy,json
from pathlib import Path
import sympy as sp
import z3
from prepare_terminal_request import prepare
from prune_terminal_relations import prune
from assemble_request_policy import assemble
from provider_models import models
from verify_algebraic_policy import guard,verify
ROOT=Path(__file__).resolve().parent

def run():
    records=[]
    source=sp.Symbol('x');one=[{'variables':[source],'laws':[[source,1-source]],'target':'x'}]
    for name,prefix,menu,sites,budget in [('empty_menu',[],[],[[]],[1,1,0]),('zero_budget',[],[[0]],[[]],[0,0,0]),
        ('duplicate_menu',[],[[0],[0]],[[]],[1,1,0]),('wrong_row_sites',[],[[0]],[],[1,1,0]),
        ('outside_menu_history',[{'support':[0],'weights':['1']}],[[True]],[[]],[2,1,0]),
        ('historical_Root_sections_pending',[{'support':[0],'weights':['1'],'sections':[]}],[[0]],[[]],[2,1,0])]:
        out=prepare(one,prefix,menu,sites,budget,seconds=2)
        assert out['status']=='UNKNOWN_TERMINAL_REQUEST_PREPARATION',out
        assert out['global_budget_NO_claimed'] is False
        records.append({'name':name,'status':out['status'],'reason':out['reason']})
    h=z3.Real('h0_0');raw={'op':'or','args':[{'op':'and','args':[{'op':'gt','left':'h0_0','right':'0'},{'op':'lt','left':'h0_0','right':'0'}]},
                                        {'op':'eq','left':'h0_0','right':'0'}]}
    fake={'status':'COMPLETE_DECLARED_AFFINE_TERMINAL_MENU_RELATIONS','relations':[{'menu_index':0,'fibre':{'history_coordinates':['h0_0'],'free_action_coordinates':[],'winning_relation':raw}}]}
    for cap in (1,512):
        result=prune(fake,max_queries=cap);assert result['status']=='COMPLETE_TERMINAL_RELATIONS_WITH_CHECKED_EMPTY_CELL_PRUNING'
        simplified=result['prepared']['relations'][0]['fibre']['winning_relation']
        a,ad=guard(raw,{'h0_0':h});b,bd=guard(simplified,{'h0_0':h});s=z3.SolverFor('QF_NRA');s.add(z3.Xor(z3.And(ad,a),z3.And(bd,b)))
        assert s.check()==z3.unsat
        records.append({'name':'global_empty_cell_equivalence_query_cap_'+str(cap),'status':'unsat','query_smt2':s.to_smt2()})
    broken=copy.deepcopy(fake);broken['relations'][0]['fibre']['winning_relation']={'op':'gt','left':'1/h0_0','right':'0'}
    out=prune(broken);assert out['status']=='UNKNOWN_TERMINAL_RELATION_PRUNING';records.append({'name':'nonconstant_written_guard_domain','status':out['status']})
    prepared=json.loads((ROOT/'PRUNED-TERMINAL-REQUEST.json').read_text())['prepared'];selector=json.loads((ROOT/'EXPORTED-REQUEST-TERMINAL-SELECTOR.json').read_text())
    for name,change in [('incomplete_backend',lambda x:x.update(SelectorStatus='UNKNOWN')),('uncovered_backend',lambda x:x['Export'].update(coverage=False)),
            ('truncated_action',lambda x:x['Export']['cells'][0]['weights'].pop()),
            ('fractional_menu_index',lambda x:x['Export']['cells'][0]['weights'].__setitem__(-1,{'kind':'rational','value':'1/2'})),
            ('wrong_selected_support',lambda x:x['Export']['cells'][0]['weights'].__setitem__(-1,{'kind':'rational','value':'0'}))]:
        changed=copy.deepcopy(selector);change(changed);out=assemble(models(),prepared,changed)
        assert out['status']=='UNKNOWN_REQUEST_POLICY_ASSEMBLY',(name,out['status'])
        assert out['global_budget_NO_claimed'] is False
        records.append({'name':name,'status':out['status'],'reason':out['reason']})
    policy=json.loads((ROOT/'CAD-ASSEMBLED-POLICY.json').read_text());policy['next']['branches'].pop(0)
    checked=verify(models(),policy,prepared['configured_supports'],prepared['row_sites'],prepared['budget'])
    assert checked['status']=='INVALID_OR_REFUTED_POLICY'
    records.append({'name':'actual_reachable_history_cell_removed','status':checked['status']})
    full=json.loads((ROOT/'PREPARED-TERMINAL-REQUEST.json').read_text())
    reduced=json.loads((ROOT/'PRUNED-TERMINAL-REQUEST.json').read_text())['prepared']
    for original,changed in zip(full['relations'],reduced['relations']):
        fibre=original['fibre'];scope={name:z3.FreshReal('independentlyComparedRetainedVariable') for name in fibre['history_coordinates']+fibre['free_action_coordinates']}
        a,ad=guard(fibre['winning_relation'],scope);b,bd=guard(changed['fibre']['winning_relation'],scope)
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=5000);solver.add(z3.Xor(z3.And(ad,a),z3.And(bd,b)));assert solver.check()==z3.unsat
        records.append({'name':'complete_original_menu_relation_equivalence_'+str(original['menu_index']),'status':'unsat','query_smt2':solver.to_smt2()})
    out={'status':'PASS_REQUEST_DRIVER_SOURCE_MENU_PRUNING_AND_POLICY_BOUNDARIES','controls':records,
         'source_parameters_remain_joint_and_rivals_separate':True,'SAME_BACKEND_trust':True,'general_recursive_synthesis_claimed':False}
    (ROOT/'REQUEST-BOUNDARY-CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'controls':len(records)}))
if __name__=='__main__':run()
