from pathlib import Path
import json,hashlib,time
O=Path(__file__).parent;P=Path('LOCAL_EVIDENCE/connected-union1607-20261012-0558z');R=Path(json.loads((P/'.build/LATEST-RUN.json').read_text())['run']);rd=lambda p:json.loads(p.read_text());H=lambda b:hashlib.sha256(b).hexdigest();start=time.monotonic();t=R/'targets/current_connected';inv=rd(t/'ACTUAL-IMPORTED-ARTIFACTS.json');modules={};total=0
for a in inv:
 p=Path(a['path']);b=p.read_bytes();assert len(b)==a['bytes'] and H(b)==a['sha256'];total+=len(b);assert a['suffix'] not in modules.setdefault(a['module'],{});modules[a['module']][a['suffix']]=a['sha256']
roots=rd(Path('LOCAL_EVIDENCE/grid319-independent-review-20261012-0549z/SPARSE-EXTERNAL-PREFLIGHT.json'))
differences=[];receipts={r["module"]:r for r in rd(t/"RESULT.json")["component_receipts"]}
for n,e in roots['recursive_mathlib_sources_and_external_companions'].items():
 expected=e.get('artifacts') or receipts[n]['object_artifacts']
 if modules[n]!=expected:differences.append(n)
assert not differences,differences
assert rd(t/'FINAL-NAMESPACE-AUTHENTICATION.json')['final_inventory_matches_initial']
l=rd(P/'LAKE-ATTEMPT1-TERMINAL.json');assert l['exit_code']==0 and l['graph_sha256']=='89697782c00dc25a5e4f6bb572f7d9a08a41c87d224eab77d04fedbdd1e7c403' and l['command'][-1]=='current/connected'
x={'status':'PASS_COMPLETE_ACTUAL_IMPORTED_INVENTORY_AND_LAUNCH','entries':len(inv),'modules':len(modules),'bytes_rehashed':total,'roots_recursive_bundles_match':len(roots['recursive_mathlib_sources_and_external_companions']),'differences':differences,'launcher_sha256':H((P/'LAKE-ATTEMPT1-TERMINAL.json').read_bytes()),'elapsed_seconds':time.monotonic()-start,'compiler_invoked':False};(O/'IMPORTED-ARTIFACT-RECHECK.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(x,indent=2))
