"""Exact rational consistency check of previously certified same-device intervals.
Does not rerun scattering solvers, fit a model, or evaluate an ML predictor.
"""
import json, hashlib
from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parents[1]
gp=root/'conductance-certificate/CONDUCTANCE-RESULT.json'
qp=root/'finite-m-certificate/FINITE-PAIR-RESULT.json'
g=json.loads(gp.read_text());q=json.loads(qp.read_text())
assert g['status']==q['status']=='PASS'
out={'scope':'Exact rational post-check of saved declared-model certificates; no ML or paper-source validation','inputs':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [gp,qp]},'devices':{}}
for key in ['minus','plus']:
 x=g['values'][key]['g_LL'];y=q['visibility'][key]['real']
 gl,gu=F(x['lower']),F(x['upper']);ql,qu=F(y['lower']),F(y['upper'])
 assert 0<=gl<=gu<=4 and -1<=ql<=qu<=1
 # N=2 full region requires Q>=1-g and Q>=g-3.
 lower_slack=ql+gl-1;upper_slack=ql-gu+3
 assert lower_slack>=0 and upper_slack>=0
 out['devices'][key]={'g_display':float((gl+gu)/2),'Q_display':float((ql+qu)/2),'low_edge_slack_lower_exact':str(lower_slack),'high_edge_slack_lower_exact':str(upper_slack),'low_edge_slack_display':float(lower_slack),'positive_sign_from_g_alone':gu<1,'full_region_consistency':'PASS'}
out['status']='PASS'
path=Path(__file__).with_name('SAVED-PAIR-RULE-AUDIT.json');path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='devices'},indent=2))
for k,v in out['devices'].items():print(k,{a:b for a,b in v.items() if not a.endswith('_exact')})
