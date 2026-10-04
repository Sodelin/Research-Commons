"""Hand-derived GLOBAL relation controls for the terminal affine compiler.
These are abstract affine models, not new biological-source admissions.
"""
from pathlib import Path
import sys,json,hashlib
import sympy as sp
import z3
stage=Path(sys.argv[1]).resolve();sys.path.insert(0,str(stage))
from terminal_fibres import compile_terminal_fibre
from verify_policy import guard
x=sp.Symbol('h0_0')
R=sp.Rational
def src(vars,rows,target):return {'variables':vars,'laws':rows,'target':target}
records=[]
def check(name,models,calls,support,expected):
 out=compile_terminal_fibre(models,calls,support,[[],[]],[len(calls)+1,2,0],seconds=15)
 assert out['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',(name,out)
 names=out['history_coordinates']+out['free_action_coordinates'];scope={n:z3.Real(n) for n in names}
 got,defined=guard(out['winning_relation'],scope)
 want=expected(scope)
 solver=z3.SolverFor('QF_NRA');solver.set(timeout=10000);solver.add(z3.Or(z3.Not(defined),z3.Xor(got,want)))
 result=solver.check();assert result==z3.unsat,(name,str(result),str(solver.model()) if result==z3.sat else solver.reason_unknown())
 records.append({'name':name,'status':str(result),'query_smt2':solver.to_smt2(),'projected_relation':out['winning_relation']})
def hist(s):
 return z3.And(s['h0_0']>0,s['h0_0']<1,s['h0_1']==1-s['h0_0'])
def action(s):return z3.And(s['a0_0']>0,s['a0_0']<1)
first=[{'support':[0],'weights':['1','0']}]
# BOTH models use the exact same caller Symbol object. Rival assignments still differ.
same_name=[src([x],[[x,1-x],[x,1-x]],'A'),src([x],[[x/2,1-x/2],[x/2,1-x/2]],'B')]
check('separate_rival_assignments_and_strict_pivot_bounds',same_name,first,[0,1],lambda s:z3.And(hist(s),action(s),s['h0_0']>=z3.RealVal('1/2')))
# No history: the action coefficient 2w-1 really vanishes at an interior action.
rank=[src([x],[[x,1-x],[1-x,x]],'A'),src([],[[R(1,5),R(4,5)],[R(1,5),R(4,5)]],'B')]
check('variable_rank_zero_and_open_source_endpoints',rank,[],[0,1],lambda s:z3.And(s['a0_0']>=z3.RealVal('1/5'),s['a0_0']<=z3.RealVal('4/5')))
# Each historical action is legal only on its written domain; cancellation cannot restore it.
two=first+[{'support':[0],'weights':['(h0_0-1/2)/(h0_0-1/2)','0']}]
check('joint_history_and_cancelled_domain',same_name,two,[0,1],lambda s:z3.And(hist(s),action(s),s['h0_0']>z3.RealVal('1/2'),s['h1_0']==s['h0_0'],s['h1_1']==s['h0_1']))
# Exact constant pivots retain the strict cube interval, not a closed-source relaxation.
bounded=[src([x],[[x/2,1-x/2],[x/2,1-x/2]],'A'),src([],[[R(3,4),R(1,4)],[R(3,4),R(1,4)]],'B')]
check('constant_pivot_open_bounds_and_constant_model',bounded,first,[0,1],lambda s:z3.And(action(s),s['h0_1']==1-s['h0_0'],z3.Or(z3.And(s['h0_0']>0,s['h0_0']<z3.RealVal('1/2')),s['h0_0']==z3.RealVal('3/4'))))
# An invalid historical probability action may produce normalized numeric rows,
# but is not an admitted history of its declared support.
for label,call in [
 ('negative_historical_weight',{'support':[0,1],'weights':['-1','2']}),
 ('nonzero_off_support_weight',{'support':[0],'weights':['2','-1']}),
 ('unnormalized_historical_action',{'support':[0],'weights':['2','0']})
]:
 check(label,same_name,[call],[0,1],lambda s:z3.BoolVal(False))
# Repeating a configuration cannot refit its hidden parameter.
check('persistent_source_across_repeated_rows',same_name,first+first,[0,1],lambda s:z3.And(hist(s),action(s),s['h0_0']>=z3.RealVal('1/2'),s['h1_0']==s['h0_0'],s['h1_1']==s['h0_1']))
result={'status':'PASS','global_equivalence_checks':records,
'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
'source_sha256':hashlib.sha256((stage/'terminal_fibres.py').read_bytes()).hexdigest(),
'trust':'global exact QF_NRA comparisons with hand-derived predicates; SAME_BACKEND',
'scope':'eight abstract complete relation controls, not a new source census or generic recursive policy'}
Path(__file__).with_name('GLOBAL-RELATION-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','global_relations':len(records),'checker_sha256':result['checker_sha256']}))

