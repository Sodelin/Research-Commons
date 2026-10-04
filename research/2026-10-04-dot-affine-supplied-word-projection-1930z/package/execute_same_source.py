"""Fresh two-call execution from one original graph/edge/gamma assignment."""
import json
from pathlib import Path
import sys
import sympy as sp
import z3

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'actual-source'))
from check_forced_pair_policy import witness
from solver import (decode_value,compile_law,unrooted_law,prepare_request,
                    verify_witness,target_json,graph_json,physical_realization)
sys.path.insert(0,str(ROOT/'providers'))
from verify_policy import guard

def main():
    certificate=json.loads((ROOT/'providers/FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_text())
    row=next(r for r in certificate['surjection_representatives']
             if tuple(v['target_coordinate'] for v in r['forced_rows'])==(0,1))
    source,values=witness(row,sp.Rational(1,2),sp.Rational(2,3))
    # Pick gamma BEFORE both calls, even though the forcing rows hide it.
    for gamma in source.parameters()[1].values():values[str(gamma)]={'kind':'rational','value':'2/5'}
    assignment={v:decode_value(values[str(v)]) for v in list(source.parameters()[0])+list(source.parameters()[1].values())}
    assert all(v.is_positive is True and (1-v).is_positive is True for v in assignment.values())
    coordinates=certificate['coordinate_order']
    policy=json.loads((ROOT/'FRESH-PROJECTED-POLICY.json').read_text())
    paths=[]
    for mode in ('common','independent'):
        forced=[]
        for bit in (0,1):
            law=unrooted_law(compile_law(source,mechanism=mode,forced={'H0':bit}))
            forced.append([sp.simplify(sp.sympify(law.get(tuple(tuple(tuple(side) for side in split) for split in outcome),0)).subs(assignment))
                           for outcome in coordinates])
        first=forced[0]
        weights=[first[0],1-first[0]]
        second=[sp.simplify(weights[0]*first[j]+weights[1]*forced[1][j]) for j in range(3)]
        assert sum(first)==sum(second)==1 and all(v>0 for v in first+second+weights)
        def encoded(vector):return [{'outcome':coordinates[j],'p':str(v)} for j,v in enumerate(vector)]
        request={'observation_kind':'exact_unranked_law','n':4,'registry':{'complete':True,'hybrid_ids':['H0']},
                 'mechanisms':[mode],'rows':[{'readout':'unrooted_splits','forced':{'H0':0},'law':encoded(first)},
                    {'readout':'unrooted_splits','program':[{'weight':str(weights[0]),'forced':{'H0':0}},
                                                         {'weight':str(weights[1]),'forced':{'H0':1}}],
                     'law':encoded(second)}]}
        verified_assignment=verify_witness(source,mode,prepare_request(request)[-1],values)
        assert verified_assignment==assignment
        node=policy
        observations={}
        for step,response in enumerate((first,second)):
            assert node['kind']=='call'
            if step==0:assert node['weights']==['1','0']
            else:assert node['weights']==['h0_0','1-h0_0']
            observations.update({f'h{step}_{j}':z3.RealVal(str(v)) for j,v in enumerate(response)})
            node=node['next']
        accepted=[]
        for branch in node['branches']:
            truth,defined=guard(branch['guard'],observations)
            if z3.is_true(z3.simplify(z3.And(truth,defined))):accepted.append(branch['next']['target'])
        target=target_json(source)['nontrivial_displayed_split_union']
        expected=sorted(tuple(tuple(side) for side in coordinates[j][0]) for j in (0,1))
        assert target==expected and accepted and all(t==[0,1] for t in accepted)
        paths.append({'mode':mode,'first_response':[str(v) for v in first],
                      'response_dependent_second_weights':[str(v) for v in weights],
                      'second_response':[str(v) for v in second],'accepted_target':[0,1],
                      'actual_original_target':target,'PATH':[2,2,1],
                      'same_original_assignment_recompiled_at_both_rows':True})
    result={'status':'PASS_FRESH_SAME_ORIGINAL_SOURCE_PROJECTED_WORD_EXECUTION',
            'graph':graph_json(source),'pre_existing_source_values':values,
            'physical_positive_calendar_and_rate_realization':physical_realization(source,values),
            'gamma_chosen_before_both_calls':'2/5','paths':paths,
            'same_source_edges_parameters_and_mechanism_through_history':True,
            'mechanisms_checked_separately':True,'new_census_or_generic_synthesis_claimed':False,
            'old_lost_execution_receipt_reused':False}
    (ROOT/'FRESH-ACTUAL-SAME-SOURCE-EXECUTION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'modes':[p['mode'] for p in paths],
                      'gamma_before_calls':'2/5','PATH':[2,2,1]},indent=2))

if __name__=='__main__':main()
