"""Execute the generated policy on pre-existing actual source assignments."""
import json
from pathlib import Path
import sys
import sympy as sp
import z3

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'actual-source'))
from check_forced_pair_policy import witness
from solver import (decode_value,compile_law,unrooted_law,prepare_request,verify_witness,
                    target_json,graph_json,physical_realization)
sys.path.insert(0,str(ROOT/'projection/providers'))
from verify_policy import expression,guard

def exact_rational(value):
    value=z3.simplify(value)
    if not z3.is_rational_value(value):
        raise ValueError('This source-execution control records exact rational responses.')
    return sp.Rational(value.numerator_as_long(),value.denominator_as_long())

def run():
    policy=json.loads((ROOT/'GENERATED-ADAPTIVE-POLICY.json').read_text())
    raw=(ROOT/'GENERATED-ADAPTIVE-POLICY.json').read_bytes()
    import hashlib
    policy_sha=hashlib.sha256(raw).hexdigest()
    provider=json.loads((ROOT/'projection/providers/FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_text())
    representative=next(r for r in provider['surjection_representatives']
                        if tuple(v['target_coordinate'] for v in r['forced_rows'])==(0,1))
    coordinates=provider['coordinate_order'];paths=[];observed_actions=[]
    for survival in (sp.Rational(1,3),sp.Rational(2,3)):
        source,values=witness(representative,survival,sp.Rational(2,3))
        for gamma in source.parameters()[1].values():values[str(gamma)]={'kind':'rational','value':'2/5'}
        assignment={v:decode_value(values[str(v)]) for v in list(source.parameters()[0])+list(source.parameters()[1].values())}
        assert all(v.is_positive is True and (1-v).is_positive is True for v in assignment.values())
        for mode in ('common','independent'):
            forced=[]
            for bit in (0,1):
                law=unrooted_law(compile_law(source,mechanism=mode,forced={'H0':bit}))
                forced.append([sp.simplify(sp.sympify(law.get(tuple(tuple(tuple(side) for side in split) for split in outcome),0)).subs(assignment)) for outcome in coordinates])
            node=policy;observations={};rows=[];history=[];actions=[]
            for step in range(2):
                assert node['kind']=='call'
                weights=[]
                for value in node['weights']:
                    computed,defined=expression(value,observations)
                    assert z3.is_true(z3.simplify(defined))
                    weights.append(exact_rational(computed))
                assert sum(weights)==1 and all(weights[i]>0 if i in node['support'] else weights[i]==0 for i in range(2))
                response=[sp.simplify(sum(weights[i]*forced[i][j] for i in range(2))) for j in range(3)]
                assert sum(response)==1 and all(v>0 for v in response)
                programme=[{'weight':str(weights[i]),'forced':{'H0':i}} for i in node['support']]
                rows.append({'readout':'unrooted_splits','program':programme,
                             'law':[{'outcome':coordinates[j],'p':str(v)} for j,v in enumerate(response)]})
                history.append([str(v) for v in response]);actions.append(programme)
                observations.update({f'h{step}_{j}':z3.RealVal(str(v)) for j,v in enumerate(response)})
                node=node['next']
            request={'observation_kind':'exact_unranked_law','n':4,'registry':{'complete':True,'hybrid_ids':['H0']},'mechanisms':[mode],'rows':rows}
            assert verify_witness(source,mode,prepare_request(request)[-1],values)==assignment
            selected=None
            for branch in node['branches']:
                truth,defined=guard(branch['guard'],observations)
                if z3.is_true(z3.simplify(z3.And(truth,defined))):selected=branch['next']['target'];break
            assert selected==[0,1]
            target=target_json(source)['nontrivial_displayed_split_union']
            assert target==sorted(tuple(tuple(side) for side in coordinates[j][0]) for j in selected)
            paths.append({'original_mode':mode,'survival_before_calls':str(survival),'graph':graph_json(source),
                          'same_original_values_before_calls':values,'positive_calendar_rates':physical_realization(source,values),
                          'actions_chosen_by_generated_policy':actions,'observed_history':history,'selected_target':selected,
                          'actual_original_target':target,'both_rows_recompiled_with_one_assignment':True,'PATH':[2,2,1]})
            if mode=='common':observed_actions.append(actions[1])
    assert observed_actions[0]!=observed_actions[1],'The generated second action must actually depend on the first response.'
    out={'status':'PASS_GENERATED_ADAPTIVE_POLICY_ACTUAL_SAME_SOURCE_EXECUTION',
         'generated_policy_sha256':policy_sha,'gamma_fixed_before_every_path':'2/5','paths':paths,
         'different_first_responses_choose_different_second_actions':True,
         'source_parameters_are_not_refit_between_calls':True,'new_census_or_optimality_or_generic_G7_claimed':False}
    (ROOT/'GENERATED-POLICY-ACTUAL-EXECUTION.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'actual_fixed_source_paths':len(paths),
                      'genuinely_response_dependent':True,'PATH':[2,2,1]},indent=2))

if __name__=='__main__':run()
