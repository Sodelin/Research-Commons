#!/usr/bin/env python3
"""Two source-admitted calls with a history-only algebraic action and codec."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp
import z3
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'sourcekit'))
from solver import decode_value,exact_zero,graph_json,physical_realization,target_json
from law_compiler import compile_law,unrooted_law
from source_census import admitted
from check_forced_pair_policy import witness
from section_point import select

def encode(value):
    value=sp.cancel(value)
    if value.is_Rational:return {'kind':'rational','value':str(value)}
    x=sp.Symbol('_exact_probability_root');poly=sp.Poly(sp.minimal_polynomial(value,x),x);poly=poly.clear_denoms()[1].primitive()[1]
    roots=sp.real_roots(poly.as_expr());index=next((i+1 for i,r in enumerate(roots) if exact_zero(r-value)),None)
    if index is None:raise ValueError('No exact real-root encoding for this probability.')
    return {'kind':'algebraic','polynomial_ascending':[str(c) for c in reversed(poly.all_coeffs())],'real_root_index':index}

def run():
    raw=(ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8'
    provider=json.loads(raw);representative=next(r for r in provider['surjection_representatives'] if [r['forced_rows'][i]['target_coordinate'] for i in (0,1)]==[0,1])
    # This one graph and assignment are constructed BEFORE both calls.
    source,values=witness(representative,sp.Rational(1,2),sp.Rational(2,3));assert admitted(source)
    source_vars=list(source.parameters()[0])+list(source.parameters()[1].values());assignment={v:decode_value(values[str(v)]) for v in source_vars}
    assert all(v.is_positive is True and (1-v).is_positive is True for v in assignment.values())
    coordinates=[tuple(tuple(tuple(side) for side in cut) for cut in event) for event in provider['coordinate_order']]
    def actual_forced(mode,bit):
        law=unrooted_law(compile_law(source,mode,{'H0':bit}))
        return [sp.cancel(law.get(event,0).subs(assignment)) for event in coordinates]
    outcomes=[]
    for mode in ('common','independent'):
        first=actual_forced(mode,0);assert all(v.is_Rational for v in first)
        # The selector sees only the FIRST observed coordinate, not source s/t.
        descriptor={'name':'action_root_weight','coefficients':['-h0_0','0','1'],'lower':'0','upper':'1'}
        action,value=select(descriptor,{'h0_0':z3.RealVal(str(first[0]))});w=decode_value(action)
        assert exact_zero(w-value) and exact_zero(w*w-first[0]) and w.is_Rational is False
        forced1=actual_forced(mode,1);second=[sp.cancel(w*first[i]+(1-w)*forced1[i]) for i in range(3)]
        encoded_first=[encode(v) for v in first];encoded_second=[encode(v) for v in second]
        decoded_first=[decode_value(v) for v in encoded_first];decoded_second=[decode_value(v) for v in encoded_second]
        assert all(exact_zero(a-b) for a,b in zip(first,decoded_first))
        assert all(exact_zero(a-b) for a,b in zip(second,decoded_second))
        # Whole-history recheck, not independent marginal fitting. Recompile
        # BOTH actual original source rows with that SAME pre-existing point.
        replay0=actual_forced(mode,0);replay1=actual_forced(mode,1)
        assert all(exact_zero(decoded_first[i]-replay0[i]) and exact_zero(decoded_second[i]-w*replay0[i]-(1-w)*replay1[i]) for i in range(3))
        # The decoder reads ONLY the second observed vector: its exact minimum.
        baseline=decoded_second[0]
        for observed in decoded_second[1:]:
            difference=sp.cancel(observed-baseline)
            if difference.is_negative is True:baseline=observed
            elif difference.is_positive is not True and not exact_zero(difference):raise ValueError('Unsupported exact algebraic comparison.')
        # Hidden-source quantities are used solely for this verification check.
        assert exact_zero(baseline-(w*sp.Rational(1,2)+(1-w)*sp.Rational(2,3))/3)
        expected=set((0,1));selected=[]
        for i,v in enumerate(decoded_second):
            delta=sp.cancel(v-baseline)
            if delta.is_positive is True:selected.append(i)
            else:assert exact_zero(delta)
        assert set(selected)==expected
        target=target_json(source)['nontrivial_displayed_split_union']
        assert target==sorted(coordinates[i][0] for i in selected)
        outcomes.append({'mechanism':mode,'first_observation':encoded_first,
                         'history_only_section':descriptor,'actual_action_weights':[action,encode(1-w)],
                         'second_observation':encoded_second,'actual_target':target,'target_coordinate_set':selected,
                         'both_original_rows_recompiled_under_one_assignment':True,'path_cost':[2,2,1]})
    # Different algebraic root is not the recorded history-only action.
    bad=copy.deepcopy(outcomes[0]['actual_action_weights'][0]);bad['real_root_index']=1
    assert not exact_zero(decode_value(bad)-decode_value(outcomes[0]['actual_action_weights'][0]))
    # A changed exact probability cannot replay the same original history.
    wrong=sp.Rational(1,3)
    assert not exact_zero(wrong-decode_value(outcomes[0]['second_observation'][0]))
    out={'schema':'actual-source-algebraic-adaptive-whole-history-replay-v1','status':'PASS_ACTUAL_SOURCE_ALGEBRAIC_ACTION_AND_RESPONSE_CODEC',
         'source':graph_json(source),'same_original_source_values':values,'physical_realization':physical_realization(source,values),
         'source_image_provider_sha256':hashlib.sha256(raw).hexdigest(),'outcomes':outcomes,
         'wrong_root_and_changed_probability_controls_reject':True,'new_source_family_or_census_added':False,
         'generic_adaptive_synthesis_claimed':False,'empirical_admission_claimed':False,'Lean_certification_claimed':False}
    (ROOT/'ACTUAL-SOURCE-ALGEBRAIC-REPLAY.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'mechanisms':len(outcomes),'shared_original_source':True,
                      'exact_algebraic_action':outcomes[0]['actual_action_weights'][0],
                      'both_actual_history_rows_recompiled':True,'path_cost':[2,2,1]},indent=2))

if __name__=='__main__':run()
