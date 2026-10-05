from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'disposable-v1'))
from synthesize_policy import provider
from compile_projected_word import compile_policy
models,_=provider();records=[]
for name,second,expected in [('pure_second_parent',{'support':[1],'weights':['0','1']},True),('repeat_first_parent',{'support':[0],'weights':['1','0']},False)]:
 r=compile_policy(models,[{'support':[0],'weights':['1','0']},second],[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
 ok=r['status']=='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND'
 assert ok==expected,(name,r['status'])
 records.append({'control':name,'status':r['status'],'expected_verified':expected,'source_and_history_shared':True})
x={'status':'PASS','scope':'An endpoint outside the full-support interior is winning after the first force0. This checks the wording distinction between a certified full-support subregion and the complete menu/history-conditioned winning fibre. Backend trust SAME_BACKEND.','controls':records};(ROOT/'ENDPOINT-FIBRE-CONTROL.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
