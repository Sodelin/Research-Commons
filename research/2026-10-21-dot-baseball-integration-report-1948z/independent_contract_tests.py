"""Independent adversarial contract tests. No actual player inputs."""
import copy
from compose import compose,COMPONENTS
base=dict(player_id='fixture',window_start='2025-05-01',window_end='2025-06-30',window_convention='[start,end)',mode='forecast',reference_id='fixture',accounting_version='fixture',components={})
for k in COMPONENTS:base['components'][k]=dict(status='available',value=0.,units='runs',player_id=base['player_id'],window_start=base['window_start'],window_end=base['window_end'],window_convention='[start,end)',mode='forecast',reference_id='fixture',accounting_version='fixture',source='synthetic',definition=k)
assert compose(base)["coverage_complete"]
print("VALID CONTROL accepted")
cases={}
r=copy.deepcopy(base);r['window_end']='2025-04-30';cases['reversed window']=r
r=copy.deepcopy(base);r['components']['fielding']['window_end']='2024-06-30';cases['component wrong window']=r
r=copy.deepcopy(base);r['components']['batting']['player_id']='someone-else';cases['component wrong player']=r
r=copy.deepcopy(base);r['components']['pitching']['status']='not_applicable';r['components']['pitching']['reason']='assumption';r['components']['pitching']['reference_id']='other';cases['not-applicable wrong reference']=r
r=copy.deepcopy(base);r['components']['batting']['value']=True;cases['boolean value']=r
for label,r in cases.items():
 try:compose(r)
 except (ValueError,TypeError):print('REJECTED',label)
 else:raise AssertionError('UNGUARDED '+label)
