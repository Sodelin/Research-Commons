from pathlib import Path
import json,hashlib,time
O=Path(__file__).parent;P=Path('LOCAL_EVIDENCE/connected-union1598-20261012-0456z');R=P/'.build/runs/20261012T045734.142946Z';rd=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic();t=R/'targets/current_connected';inv=rd(t/'ACTUAL-IMPORTED-ARTIFACTS.json');modules={};total=0
for a in inv:
 p=Path(a['path']);b=p.read_bytes();assert len(b)==a['bytes'] and H(b)==a['sha256'];total+=len(b);assert a['suffix'] not in modules.setdefault(a['module'],{});modules[a['module']][a['suffix']]=a['sha256']
roots=rd(Path('LOCAL_EVIDENCE/certificate310-independent-review-20261012-0447z/POLYNOMIAL-ROOTS-PREFLIGHT.json'))
differences=[]
for n,e in roots['recursive_mathlib_sources_and_external_companions'].items():
 if modules[n]!=e['artifacts']:differences.append(n)
assert not differences,differences
assert rd(t/'FINAL-NAMESPACE-AUTHENTICATION.json')['final_inventory_matches_initial']
l=rd(P/'LAKE-ATTEMPT1-TERMINAL.json');assert l['exit_code']==0 and l['graph_sha256']=='9a8467c792c066cc97b939c05ddef04a77bdf21447fcb2df832be84215ec253e' and l['command'][-1]=='current/connected'
x={'status':'PASS_COMPLETE_ACTUAL_IMPORTED_INVENTORY_AND_LAUNCH','entries':len(inv),'modules':len(modules),'bytes_rehashed':total,'roots_recursive_bundles_match':len(roots['recursive_mathlib_sources_and_external_companions']),'differences':differences,'launcher_sha256':H((P/'LAKE-ATTEMPT1-TERMINAL.json').read_bytes()),'elapsed_seconds':time.monotonic()-start,'compiler_invoked':False};(O/'IMPORTED-ARTIFACT-RECHECK.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
