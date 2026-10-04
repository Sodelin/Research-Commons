#!/usr/bin/env python3
import copy
import json
from pathlib import Path
import z3
from cad_value import evaluate_value
from algebraic_history_point import encode_exact,decode_exact
ROOT=Path(__file__).resolve().parent
def rational(x):return {'kind':'rational','value':str(x)}
def obs(x):return {'kind':'observation','name':x}
def root(coeff,k):return {'kind':'root','coefficients':coeff,'real_root_index':k}
def yes(out):return out['status']=='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND'
def equal(a,b):return z3.is_true(z3.simplify(a==b))
def run():
    records=[]
    def check(name,tree,scope,predicate):
        out,v=evaluate_value(tree,scope);assert yes(out),(name,out)
        assert predicate(v) and equal(decode_exact(out['encoding']),v)
        records.append({'name':name,'ast':tree,'observed':scope,'result':out})
        return out,v
    supplied=json.loads((ROOT/'EXPORTED-CAD-VALUES.json').read_text())
    history={'h0_0':rational('1/2')}
    _,q=check('fresh_Wolfram_quintic_export',supplied['Examples']['quintic']['AST'],history,lambda v:equal(v**5,z3.RealVal('1/2')))
    check('native_normalized_root_flag',supplied['Examples']['native_normalized_root_flag']['AST'],history,lambda v:equal(v**5,z3.RealVal('1/2')))
    _,a=check('fresh_Wolfram_square_root_export',supplied['Examples']['square_root']['AST'],history,lambda v:equal(v*v,z3.RealVal('1/2')))
    check('fresh_Wolfram_midpoint_export',supplied['Examples']['midpoint']['AST'],history,lambda v:equal((2*v-1)**5,z3.RealVal('1/2')))
    check('fresh_Wolfram_rational_division_export',supplied['Examples']['rational_division']['AST'],history,lambda v:equal(v,z3.RealVal('2/3')))
    check('fresh_Wolfram_minimum_export',supplied['Examples']['minimum']['AST'],history,lambda v:equal(v,z3.RealVal('1/2')))
    for index,expected in ((1,1),(2,1),(3,2)):
        check('multiplicity_index_'+str(index),root([rational(-2),rational(5),rational(-4),rational(1)],index),{},lambda v,e=expected:equal(v,z3.RealVal(e)))
    for index,expected in ((1,-1),(2,0),(3,1)):
        check('simple_index_'+str(index),root([rational(0),rational(-1),rational(0),rational(1)],index),{},lambda v,e=expected:equal(v,z3.RealVal(e)))
    tree=copy.deepcopy(supplied['Examples']['square_root']['AST'])
    check('algebraic_observation_export',tree,{'h0_0':encode_exact(a)},lambda v:equal(v*v,a))
    tree=root([{'kind':'multiply','args':[rational(-1),obs('action_root_prior')]},rational(0),rational(1)],2)
    check('earlier_own_root_coefficient',tree,{'action_root_prior':encode_exact(a)},lambda v:equal(v*v,a))
    check('zero_principal_root_multiplicity',{'kind':'principal_power','base':rational(0),'numerator':1,'denominator':2},{},lambda v:equal(v,z3.RealVal(0)))
    check('negative_integer_power_domain',{'kind':'power','base':rational(2),'exponent':-2},{},lambda v:equal(v,z3.RealVal('1/4')))
    negative=[]
    bad=[('nonreal_index',root([rational(1),rational(0),rational(1)],1),{}),
         ('index_beyond_roots',root([rational(-2),rational(0),rational(1)],3),{}),
         ('zero_leading_stratum',root([rational(1),rational(0)],1),{}),
         ('undeclared_source',obs('source_gamma'),{}),
         ('future_not_recorded',obs('h9_0'),history),
         ('invalid_principal_negative_base',{'kind':'principal_power','base':rational(-2),'numerator':1,'denominator':3},{}),
         ('zero_negative_power',{'kind':'power','base':rational(0),'exponent':-1},{}),
         ('written_zero_power_keeps_domain',{'kind':'power','base':{'kind':'divide','numerator':rational(1),'denominator':rational(0)},'exponent':0},{}),
         ('unexpected_AST_field',{'kind':'rational','value':'1','source':'gamma'},{}),
         ('float',{'kind':'rational','value':0.5},{}),
         ('complex_observation',obs('h0_0'),{'h0_0':{'kind':'algebraic','polynomial_ascending':['1','0','1'],'real_root_index':1}})]
    for name,tree,scope in bad:
        out,v=evaluate_value(tree,scope);assert out['status'].startswith('UNKNOWN_') and v is None,(name,out)
        negative.append({'name':name,'result':out})
    out,v=evaluate_value(root([rational(-2),rational(0),rational(1)],1),{},max_degree=1)
    assert out['status']=='UNKNOWN_CAD_VALUE_RESOURCE_LIMIT';negative.append({'name':'degree_resource_ceiling','result':out})
    deep=rational(1)
    for i in range(70):deep={'kind':'add','args':[deep]}
    out,v=evaluate_value(deep,{});assert out['status']=='UNKNOWN_CAD_VALUE_RESOURCE_LIMIT'
    negative.append({'name':'depth_resource_ceiling','result':out})
    assert all(v['Status'].startswith('UNKNOWN_') for v in supplied['Negative'].values())
    output={'status':'PASS_STRUCTURED_CAD_VALUE_CONTROLS','positive':records,'negative':negative,'export_negative_controls':supplied['Negative'],'trust':'SAME_BACKEND value/codec controls; no whole generic selector claim'}
    (ROOT/'CAD-VALUE-CONTROLS.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],'positive':len(records),'unknown_controls':len(negative),'export_rejections':len(supplied['Negative'])}))
if __name__=='__main__':run()
