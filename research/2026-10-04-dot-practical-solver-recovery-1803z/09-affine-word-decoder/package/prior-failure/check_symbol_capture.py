"""Abstract encoding countercontrol, not an admitted biological-source collision."""
from pathlib import Path
import sys,json,hashlib
import sympy as sp
import z3
P=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent.parent/'checkpoint-compiler-v1.2'
sys.path.insert(0,str(P))
from compile_leaves import compile_policy
from verify_policy import guard
x,y=sp.symbols('h0_0 h0_1');a,b=sp.symbols('x y')
models=[{'variables':[x,y],'laws':[[x,1-x],[y,1-y]],'target':'T'}, {'variables':[a,b],'laws':[[a,1-a],[b,1-b]],'target':'T'}]
calls=[{'support':[0],'weights':['1','0']},{'support':[1],'weights':['0','1']},{'support':[0],'weights':['1','0']}]
r=compile_policy(models,calls,[[0],[1]],[[],[]],[3,2,0])
result={'manifest_sha256':hashlib.sha256((P/'SOURCE-MANIFEST.json').read_bytes()).hexdigest(),'compiler_status':r['status'],'abstract_control_not_biological_source':True,'history':[['1/5','4/5'],['2/5','3/5'],['3/5','2/5']],'history_is_impossible':'Calls1and3 use the same row of one unchanged parameter point but their responses differ.','guards':[]}
if r['status']=='WHOLE_ACTION_WORD_TARGET_DECODER_COMPILED_AND_VERIFIED_SAME_BACKEND':
 node=r['policy']
 while node['kind']=='call':node=node['next']
 obs={f'h{i}_{j}':z3.RealVal(v) for i,row in enumerate(result['history']) for j,v in enumerate(row)}
 for branch in node['branches']:
  g,d=guard(branch['guard'],obs);result['guards'].append({'truth':str(z3.simplify(g)),'defined':str(z3.simplify(d))})
 result['status']='FAIL_PROJECTION_EQUIVALENCE' if any(v=={'truth':'True','defined':'True'} for v in result['guards']) else 'NO_COUNTEREXAMPLE'
else:result['status']='PASS_FAIL_CLOSED'
out=Path(__file__).resolve().parent/('SYMBOL-CAPTURE-'+P.name+'.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
