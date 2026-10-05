from pathlib import Path
import sys,json,hashlib
import sympy as s
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT/'disposable'))
from compile_projected_word import compile_policy,parsed_action
x=s.Symbol('h0_0'); models=[{'variables':[x],'laws':[[x,1-x],[x,1-x]],'target':'fixed-target'}]
first={'support':[0],'weights':['1','0']};results=[]
for expr,expect in [('(h0_0-1/2)/(h0_0-1/2)',False),('(1/(h0_0-1/2))**0',False),('0*(1/(h0_0-1/2))+1',False),('1/((h0_0-1/2)/(h0_0-1/2))',False),('h0_0/h0_0',True),('(1/h0_0)**0',True),('0*(1/h0_0)+1',True)]:
 out=compile_policy(models,[first,{'support':[0],'weights':[expr,'0']}],[[0]],[[],[]],[2,1,0])
 yes=out['status']=='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND';assert yes==expect,(expr,out)
 results.append({'expression':expr,'expected_complete_verified_policy':expect,'status':out['status'],'verification_status':out.get('verification',{}).get('status')})
r={'status':'PASS','checks':results,'scope':'Fresh independent written-domain controls; the original source parameter deliberately has the same spelling as a history observation. Reachable undefined midpoint must prevent universal policy verification. Backend checks remain SAME_BACKEND.'};(ROOT/'INDEPENDENT-WRITTEN-DOMAIN-CONTROLS.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
