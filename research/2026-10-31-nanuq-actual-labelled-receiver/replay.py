"""python3 replay.py LEAN_BINARY NEW_OUTPUT GRAPH_ROOT RESTRICTION_ROOT FINITE_ROOT DEP_OLEAN_DIR..."""
from pathlib import Path
import sys,json,hashlib,os,subprocess,re
if len(sys.argv)<7:raise SystemExit(__doc__)
b=Path(__file__).resolve().parent;lean=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();roots=dict(zip(['graph','restriction','finite'],map(lambda p:Path(p).resolve(),sys.argv[3:6])));deps=[str(Path(p).resolve())for p in sys.argv[6:]]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert sha(b/'SOURCE-MANIFEST.json')=='d61c58fbe13020a28333826ddfacf43a178934b7aba90d2a9782ac0e8ddaa62b'
for n,mods in json.loads((b/'INHERITED-BINDINGS.json').read_text()).items():
 for m,r in mods.items():
  assert sha(roots[n]/(m+'.lean'))==r['source_sha256']
  assert sha(roots[n]/(m+'.olean'))==r['olean_sha256']
m=json.loads((b/'SOURCE-MANIFEST.json').read_text())
for n,r in m['modules'].items():assert sha(b/(n+'.lean'))==r['source_sha256']
out.mkdir(exist_ok=False);env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+[str(p)for p in roots.values()]+deps)
for n in m['order']:
 (out/(n+'.lean')).write_bytes((b/(n+'.lean')).read_bytes())
 p=subprocess.run([str(lean),'-Ddebug.skipKernelTC=false','-M','1800','-o',n+'.olean',n+'.lean'],cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(n+'.log')).write_bytes(p.stdout);r={'module':n,'exit':p.returncode,'source_sha256':sha(out/(n+'.lean'))}
 if not p.returncode:r['olean_sha256']=sha(out/(n+'.olean'))
 with (out/'REPLAY-EVENTS.jsonl').open('a')as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 for ax in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',p.stdout.decode()):assert set(a.strip()for a in ax.split(','))<={'propext','Classical.choice','Quot.sound'}
(out/'PASS.txt').write_text('Seven new receiver-bridge modules accepted; inherited rebuilt0. Full NANUQ OPEN.\n')
