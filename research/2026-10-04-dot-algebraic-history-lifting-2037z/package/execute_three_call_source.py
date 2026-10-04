#!/usr/bin/env python3
"""All three calls reuse one original positive graph/edge/gamma assignment."""
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp
import z3
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'sourcekit'))
from solver import decode_value,graph_json,physical_realization,target_json
from law_compiler import compile_law,unrooted_law
from source_census import admitted
from check_forced_pair_policy import witness
from algebraic_history_point import evaluate_section,decode_exact,encode_exact

def equal(a,b):return z3.is_true(z3.simplify(a==b))
def run():
    raw=(ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8'
    provider=json.loads(raw)
    rep=next(r for r in provider['surjection_representatives'] if [r['forced_rows'][i]['target_coordinate'] for i in (0,1)]==[0,1])
    # The entire original graph and assignment predate every response/action.
    source,values=witness(rep,sp.Rational(1,2),sp.Rational(2,3));assert admitted(source)
    source_vars=list(source.parameters()[0])+list(source.parameters()[1].values())
    assignment={v:decode_value(values[str(v)]) for v in source_vars}
    assert all(v.is_positive is True and (1-v).is_positive is True for v in assignment.values())
    coordinates=[tuple(tuple(tuple(side) for side in cut) for cut in event) for event in provider['coordinate_order']]
    def forced(mode,bit):
        law=unrooted_law(compile_law(source,mode,{'H0':bit}))
        values=[sp.cancel(law.get(event,0).subs(assignment)) for event in coordinates]
        assert all(v.is_Rational for v in values)
        return [z3.RealVal(str(v)) for v in values]
    paths=[]
    policy=json.loads((ROOT/'THREE-CALL-POLICY.json').read_text())
    for mode in ('common','independent'):
        p0=forced(mode,0);p1=forced(mode,1)
        first=p0
        section1=policy['next']['sections'][0]
        point1,w=evaluate_section(section1,{f'h0_{i}':encode_exact(v) for i,v in enumerate(first)})
        assert point1['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND',point1
        second=[z3.simplify(w*p0[i]+(1-w)*p1[i]) for i in range(3)]
        assert any(isinstance(v,z3.AlgebraicNumRef) for v in second)
        section2=policy['next']['next']['sections'][0]
        observed={**{f'h0_{i}':encode_exact(v) for i,v in enumerate(first)},
                  **{f'h1_{i}':encode_exact(v) for i,v in enumerate(second)}}
        point2,u=evaluate_section(section2,observed)
        assert point2['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND',point2
        assert equal(u*u,second[0])
        third=[z3.simplify(u*p0[i]+(1-u)*p1[i]) for i in range(3)]
        histories=[[encode_exact(v) for v in y] for y in (first,second,third)]
        decoded=[[decode_exact(v) for v in y] for y in histories]
        recompiled0=forced(mode,0);recompiled1=forced(mode,1)
        for weights,row in zip(((z3.RealVal(1),z3.RealVal(0)),(w,1-w),(u,1-u)),decoded):
            assert all(equal(row[i],weights[0]*recompiled0[i]+weights[1]*recompiled1[i]) for i in range(3))
        minimum=third[0]
        for v in third[1:]:
            if z3.is_true(z3.simplify(v<minimum)):minimum=v
        targets=[i for i,v in enumerate(third) if z3.is_true(z3.simplify(v>minimum))]
        assert targets==[0,1]
        target=target_json(source)['nontrivial_displayed_split_union']
        assert target==sorted(coordinates[i][0] for i in targets)
        # The second section genuinely needs the removed algebraic-coefficient
        # lift: its h1_0 input is an irrational closed algebraic number.
        assert observed['h1_0']['kind']=='algebraic'
        paths.append({'mode':mode,'observations':histories,'actions':[[{'kind':'rational','value':'1'},{'kind':'rational','value':'0'}],
                        [encode_exact(w),encode_exact(1-w)],[encode_exact(u),encode_exact(1-u)]],
                      'section_points':[point1,point2],'target':target,'path_cost':[3,2,1],
                      'all_three_rows_recompiled_under_one_original_assignment':True})
    receipt={'schema':'actual-three-call-algebraic-history-source-replay-v1','status':'PASS_ACTUAL_SOURCE_ALGEBRAIC_HISTORY_LIFT',
             'source':graph_json(source),'same_original_source_values':values,'physical_realization':physical_realization(source,values),
             'paths':paths,'one_preselected_source_across_all_calls':True,'provider_sha256':hashlib.sha256(raw).hexdigest(),
             'new_source_census_claimed':False,'generic_synthesis_claimed':False,'empirical_admission_claimed':False,'Lean_claimed':False}
    (ROOT/'ACTUAL-THREE-CALL-SOURCE-REPLAY.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'fixed_modes':len(paths),'path_cost':[3,2,1],'algebraic_observation_consumed':True}))
if __name__=='__main__':run()
