#!/usr/bin/env python3
"""Closed algebraic coefficients, chained roots and fail-closed controls."""
import copy
import json
from pathlib import Path
import z3
from algebraic_history_point import evaluate_section, decode_exact, encode_exact

ROOT = Path(__file__).resolve().parent
def section(coeff, lower='0', upper='1', name='action_root_point'):
    return {'name': name, 'coefficients': coeff, 'lower': lower, 'upper': upper}
def eq(a,b):
    return z3.is_true(z3.simplify(a==b))

def run():
    positives=[];negatives=[]
    def yes(label,s,known,identity):
        out,value=evaluate_section(s,known)
        assert out['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND',out
        assert identity(value)
        assert eq(decode_exact(out['encoding']),value)
        positives.append({'name':label,'section':s,'known':{k:encode_exact(decode_exact(v) if isinstance(v,dict) else v) for k,v in known.items()},'result':out})
        return out,value
    first,a=yes('quadratic_rational',section(['-1/2','0','1']),{},lambda v:eq(v*v,z3.RealVal('1/2')))
    second,b=yes('genuine_algebraic_coefficient',section(['-h0_0','0','1']),{'h0_0':first['encoding']},lambda v:eq(v*v,a))
    third,c=yes('chained_own_root_coefficients',section(['-action_root_old','0','1']),{'action_root_old':second['encoding']},lambda v:eq(v*v,b))
    yes('algebraic_bounds_and_division',section(['-h0_0/2','1'],'h0_0/3','h0_0'),{'h0_0':first['encoding']},lambda v:eq(2*v,a))
    yes('quintic_symbolic_CAD_shape',section(['-h0_0','0','0','0','0','1']),{'h0_0':first['encoding']},lambda v:eq(v**5,a))
    yes('repeated_root_still_one_distinct_value',section(['h0_0*h0_0','-2*h0_0','1']),{'h0_0':first['encoding']},lambda v:eq(v,a))
    yes('coefficient_rank_drop_at_point',section(['-1/3','1','h0_0-h0_0']),{'h0_0':first['encoding']},lambda v:eq(v,z3.RealVal('1/3')))
    cases=[
      ('syntax_error',section(['(','0','1']),{}),
      ('hidden_parameter',section(['-source_gamma','0','1']),{}),
      ('future_response',section(['-h2_0','0','1']),{'h0_0':first['encoding']}),
      ('undefined_written_denominator',section(['-1/(h0_0-h0_0)','0','1']),{'h0_0':first['encoding']}),
      ('zero_power_keeps_written_domain',section(['-(1/(h0_0-h0_0))**0','0','1']),{'h0_0':first['encoding']}),
      ('all_zero_polynomial',section(['0','0']),{}),
      ('two_interval_roots',section(['3/16','-1','1']),{}),
      ('no_real_root',section(['1','0','1']),{}),
      ('endpoint_only',section(['0','1']),{}),
      ('root_name_collision',section(['-1/2','0','1']),{'action_root_point':a}),
      ('nonclosed_observation',section(['-h0_0','0','1']),{'h0_0':z3.Real('hiddenSourceValue')}),
      ('float_observation',section(['-h0_0','0','1']),{'h0_0':0.5}),
      ('bad_polynomial_leading_zero_codec',section(['-h0_0','0','1']),{'h0_0':{'kind':'algebraic','polynomial_ascending':['1','0'],'real_root_index':1}}),
      ('invalid_root_index',section(['-h0_0','0','1']),{'h0_0':{'kind':'algebraic','polynomial_ascending':['-2','0','1'],'real_root_index':0}}),
      ('zero_denominator_rational_codec',section(['-h0_0','0','1']),{'h0_0':{'kind':'rational','value':'1/0'}}),
      ('forged_hidden_scope_name',section(['-source_gamma','0','1']),{'source_gamma':a}),
      ('invalid_resource',section(['-1/2','0','1']),{},0)
    ]
    for item in cases:
        name,s,known=item[:3];out,value=evaluate_section(s,known,*item[3:])
        assert out['status'].startswith('UNKNOWN_') and value is None,(name,out)
        negatives.append({'name':name,'status':out['status'],'reason':out['reason']})
    receipt={'status':'PASS_EXACT_ALGEBRAIC_HISTORY_POINT_CONTROLS','positive_cases':positives,'negative_cases':negatives,'trust':'fresh exact Z3 point/codec checks; no generic CAD or policy synthesis claim'}
    (ROOT/'HISTORY-POINT-CONTROLS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'positive':len(positives),'unknown_controls':len(negatives)}))
if __name__=='__main__':run()
