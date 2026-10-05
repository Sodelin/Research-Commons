"""Independent closed-form source images and principal-section controls."""
import sys,json,copy
from pathlib import Path
import sympy as sp
import z3
P=Path(sys.argv[1]).resolve();sys.path.insert(0,str(P))
from project_branch_word import project_branch_word
from verify_algebraic_policy import guard,verify
from cad_action_sections import ActionSectionWriter
from algebraic_history_point import evaluate_section,encode_exact
from cad_value import evaluate_value
out=[]
def check(name,formula):
 s=z3.SolverFor('QF_NRA');s.set(timeout=10000);s.add(formula);r=s.check();out.append({'name':name,'status':str(r),'query_smt2':s.to_smt2()});assert r==z3.unsat,(name,r)
x,y=sp.symbols('action_root_r h0_0')
models=[{'variables':[x,y],'laws':[[x,1-x],[y,1-y]],'target':'T'}]
first={'support':[0],'weights':['1','0']}; sec={'name':'action_root_r','coefficients':['-h0_0','0','1'],'lower':'0','upper':'1'}
menu=[[0],[0,1]];sites=[[],[]];budget=[2,2,0]
h,a,b,c,r=z3.Reals('h0_0 h0_1 h1_0 h1_1 action_root_r');obs=dict(zip(['h0_0','h0_1','h1_0','h1_1','action_root_r'],[h,a,b,c,r]))
for variant in ['plain','coefficient_cancel','bound_cancel','weight_cancel']:
 s=copy.deepcopy(sec);weights=['action_root_r','1-action_root_r']
 if variant=='coefficient_cancel':s['coefficients'][0]='-h0_0+0/(h0_0-1/2)'
 if variant=='bound_cancel':s['upper']='1+0/(h0_0-1/2)'
 if variant=='weight_cancel':weights[0]+='+0/(h0_0-1/2)'
 call={'support':[0,1],'weights':weights,'sections':[s]}
 v=project_branch_word(models,[first,call],menu,sites,budget,seconds=30,max_branches=256)
 assert v['status']=='COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED',v
 tree=v['policy_candidate']['next']['next'];g,d=guard(tree['branches'][0]['guard'],obs)
 expected=z3.And(0<h,h<1,a==1-h,0<r,r<1,r*r==h,c==1-b,r*h<b,b<r*h+1-r,z3.BoolVal(True) if variant=='plain' else h!=z3.RealVal('1/2'))
 check('free_original_parameter_image_'+variant,z3.Xor(z3.And(g,d),expected))
 if variant=='plain':
  vr=verify(models,v['policy_candidate'],menu,sites,budget);assert vr['status']=='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND';out.append({'name':'full_universal_toy_policy','status':vr['status'],'obligations':len(vr['receipts'])})
 else:
  vr=verify(models,v['policy_candidate'],menu,sites,budget);assert vr['status']=='INVALID_OR_REFUTED_POLICY';out.append({'name':'domain_hole_refuted_'+variant,'status':vr['status'],'reason':vr['reason']})
# A unique repeated root is an exact point but is outside the symbolic IVT proof rule.
repeated={'name':'action_root_r','coefficients':['1/4','-1','1'],'lower':'0','upper':'1'}
point,val=evaluate_section(repeated,{})
assert point['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND' and z3.is_true(z3.simplify(val==z3.RealVal('1/2')))
call={'support':[0,1],'weights':['action_root_r','1-action_root_r'],'sections':[repeated]}
p=project_branch_word(models,[first,call],menu,sites,budget);assert p['status']=='COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED'
v=verify(models,p['policy_candidate'],menu,sites,budget);assert v['status']=='INVALID_OR_REFUTED_POLICY'
out.append({'name':'unique_repeated_point_vs_symbolic_IVT','point_status':point['status'],'policy_status':v['status'],'reason':v['reason']})
# AST and isolated equation select the same positive root, including powers and inverses.
for q in [2,3,5]:
 for power in [-2,0,1,3]:
  ast={'kind':'principal_power','base':{'kind':'observation','name':'h0_0'},'numerator':power,'denominator':q}
  writer=ActionSectionWriter(1);call=writer.call([ast],[0]);rec,root=evaluate_section(call['sections'][0],{'h0_0':{'kind':'rational','value':'2/3'}})
  rec2,value=evaluate_value(ast,{'h0_0':{'kind':'rational','value':'2/3'}})
  assert rec['status']=='EXACT_ALGEBRAIC_HISTORY_SECTION_POINT_SAME_BACKEND' and rec2['status']=='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND'
  expected=z3.RealVal(1) if power==0 else (1/(root**(-power)) if power<0 else root**power)
  assert z3.is_true(z3.simplify(expected==value));out.append({'name':f'principal_q{q}_p{power}','status':'EXACT_MATCH','value':encode_exact(value)})
# A written undefined base remains undefined even when exponent zero would simplify it.
ast={'kind':'principal_power','base':{'kind':'divide','numerator':{'kind':'observation','name':'h0_0'},'denominator':{'kind':'observation','name':'h0_0'}},'numerator':0,'denominator':2}
call=ActionSectionWriter(1).call([ast],[0]);rec,val=evaluate_section(call['sections'][0],{'h0_0':{'kind':'rational','value':'0'}});assert val is None;out.append({'name':'zero_power_undefined_written_base','status':rec['status']})
print(json.dumps({'status':'PASS_INDEPENDENT_ROOT_SEMANTIC_CONTROLS','controls':out},indent=2))
