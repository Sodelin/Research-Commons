"""Replay only the 24 restriction modules; never rebuild the inherited provider.
Usage: python3 replay.py FINITE_OBJECT_ROOT LEAN_BINARY NEW_OUTPUT DEP_OLEAN_DIR...
FINITE_OBJECT_ROOT must contain its accepted sources, objects and build receipts.
Use the pinned dependencies recorded in README; no downloads/installations occur.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
base=Path(__file__).resolve().parent
if len(sys.argv)<5: raise SystemExit(__doc__)
old,lean,out=map(lambda s:Path(s).resolve(),sys.argv[1:4])
deps=[str(Path(s).resolve()) for s in sys.argv[4:]]
m=json.loads((base/'SOURCE-MANIFEST.json').read_text())
assert sha(base/'SOURCE-MANIFEST.json')=='5b0960dd18826871ccb47db13eb431c9496a5838d2cb80ba911423b69528d4a0'
assert sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert sha(old/'SOURCE-MANIFEST.json')=='312620dfe5e26a2811a9db23cee18fc3242bf8f9cda75226b5a319fe2af99273'
om=json.loads((old/'SOURCE-MANIFEST.json').read_text())
last={r['module']:r for r in map(json.loads,(old/'BUILD-EVENTS.jsonl').read_text().splitlines())}
assert len(om['modules'])==1211
for mod,row in om['modules'].items():
 assert sha(old/(mod+'.lean'))==row['source_sha256']==last[mod]['source_sha256']
 assert last[mod]['exit']==0 and sha(old/(mod+'.olean'))==last[mod]['olean_sha256']
for mod,row in m['modules'].items(): assert sha(base/(mod+'.lean'))==row['source_sha256']
out.mkdir(exist_ok=False)
for mod in m['order']:(out/(mod+'.lean')).write_bytes((base/(mod+'.lean')).read_bytes())
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out),str(old)]+deps)
for mod in m['order']:
 p=subprocess.run([str(lean),'-M','1800','-o',mod+'.olean',mod+'.lean'],cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(mod+'.log')).write_bytes(p.stdout)
 row={'module':mod,'source_sha256':sha(out/(mod+'.lean')),'exit':p.returncode}
 if p.returncode==0:row['olean_sha256']=sha(out/(mod+'.olean'))
 with (out/'REPLAY-EVENTS.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if p.returncode:raise SystemExit('FAILED '+mod)
a=(out/'RestrictionEndpoints.log').read_text(); ax=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',a)
assert len(ax)==10
for x in ax:assert set(y.strip() for y in x.split(','))<={'propext','Classical.choice','Quot.sound'}
(out/'REPLAY-ACCEPTANCE.json').write_text(json.dumps({'status':'PASS_ORDERED_TREE_RESTRICTION_NOT_FULL_NANUQ','modules':24,'inherited_modules_rebuilt':0,'axioms':a},indent=2)+'\n')
