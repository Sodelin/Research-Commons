#!/usr/bin/env python3
"""Execute the emitted CAD-cell policy at preselected actual original sources."""
import hashlib,json,sys
from pathlib import Path
import sympy as sp
import z3
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'sourcekit'))
from solver import decode_value,graph_json,physical_realization,target_json
from law_compiler import compile_law,unrooted_law
from source_census import admitted
from check_forced_pair_policy import witness
from verify_policy import expression,guard

def run():
    raw=(ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8'
    provider=json.loads(raw);policy=json.loads((ROOT/'CAD-ASSEMBLED-POLICY.json').read_text())
    coordinates=[tuple(tuple(tuple(side) for side in cut) for cut in event) for event in provider['coordinate_order']]
    cases=[]
    # Cover all three first-observation cells with actual original witnesses.
    for pair in ((0,1),(1,2),(2,0)):
        rep=next(r for r in provider['surjection_representatives'] if tuple(r['forced_rows'][i]['target_coordinate'] for i in (0,1))==pair)
        source,encoded=witness(rep,sp.Rational(1,2),sp.Rational(2,3));assert admitted(source)
        symbols=list(source.parameters()[0])+list(source.parameters()[1].values())
        assignment={v:decode_value(encoded[str(v)]) for v in symbols}
        assert all(v.is_positive is True and (1-v).is_positive is True for v in assignment.values())
        for mode in ('common','independent'):
            # No source fit occurs inside walk. Every law uses this ONE point.
            forced=[]
            for bit in (0,1):
                law=unrooted_law(compile_law(source,mode,{'H0':bit}))
                forced.append([sp.cancel(law.get(c,0).subs(assignment)) for c in coordinates])
            assert all(v.is_Rational for row in forced for v in row)
            observed={};history=[];branches=[];used_rows=set();used_sites=set();node=policy;target=None
            while node['kind']!='leaf':
                if node['kind']=='decision':
                    selected=None
                    for index,branch in enumerate(node['branches']):
                        g,defined=guard(branch['guard'],observed);assert z3.is_true(z3.simplify(defined))
                        value=z3.simplify(g);assert z3.is_true(value) or z3.is_false(value)
                        if z3.is_true(value):selected=index;node=branch['next'];branches.append(index);break
                    assert selected is not None,'No generated policy branch covers this original source.'
                    continue
                assert node['kind']=='call'
                values=[expression(v,observed) for v in node['weights']]
                assert all(z3.is_true(z3.simplify(d)) and z3.is_rational_value(z3.simplify(v)) for v,d in values)
                weights=[sp.Rational(str(z3.simplify(v).as_fraction())) for v,d in values]
                assert sum(weights)==1 and all((v>0) if i in node['support'] else (v==0) for i,v in enumerate(weights))
                used_rows|=set(node['support']);used_sites.add('H0')
                response=[sp.cancel(sum(weights[i]*forced[i][j] for i in range(2))) for j in range(3)]
                # Freshly recompile the original rows under the same assignment.
                replay=[]
                for bit in (0,1):
                    law=unrooted_law(compile_law(source,mode,{'H0':bit}));replay.append([sp.cancel(law.get(c,0).subs(assignment)) for c in coordinates])
                assert all(sp.cancel(response[j]-sum(weights[i]*replay[i][j] for i in range(2)))==0 for j in range(3))
                step=len(history);observed.update({f'h{step}_{j}':z3.RealVal(str(v)) for j,v in enumerate(response)})
                history.append({'weights':[str(v) for v in weights],'response':[str(v) for v in response]});node=node['next']
            target=node['target'];expected=tuple(sorted(set(pair)));assert tuple(target)==expected
            actual=target_json(source)['nontrivial_displayed_split_union'];assert actual==sorted(coordinates[i][0] for i in expected)
            assert len(history)==2 and len(used_rows)==2 and len(used_sites)==1
            cases.append({'source':graph_json(source),'same_preselected_original_values':encoded,'physical_realization':physical_realization(source,encoded),
                          'mode':mode,'source_pair':list(pair),'history':history,'first_eligible_branch_path':branches,'actual_target':actual,'path_cost':[2,2,1],
                          'both_calls_recompiled_under_one_original_assignment':True})
    assert len({case['first_eligible_branch_path'][0] for case in cases})==3
    out={'status':'PASS_ACTUAL_SOURCE_CAD_POLICY_EXECUTION','cases':cases,'covers_every_emitted_terminal_CAD_cell':True,
         'provider_sha256':hashlib.sha256(raw).hexdigest(),'full_generic_recursive_synthesis_claimed':False,'empirical_admission_claimed':False,'Lean_claimed':False}
    (ROOT/'ACTUAL-CAD-POLICY-EXECUTION.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':out['status'],'actual_source_paths':len(cases),'terminal_CAD_cells_covered':3,'path_cost':[2,2,1]}))
if __name__=='__main__':run()
