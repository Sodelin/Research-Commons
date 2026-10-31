"""python3 replay.py LEAN_BINARY NEW_OUTPUT DEP_OLEAN_DIR...
Replays the accepted 15-module closure, not candidates. No downloads/installations.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,os,re
if len(sys.argv)<4:raise SystemExit(__doc__)
b=Path(__file__).resolve().parent;lean=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();deps=[str(Path(x).resolve())for x in sys.argv[3:]]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert sha(b/'SOURCE-MANIFEST.json')=='4b0bc8eccc79da9e9bd1fb9401fcf738d84d018305137dd94f1c53f463a484a7'
m=json.loads((b/'SOURCE-MANIFEST.json').read_text())
for n,r in m['modules'].items():assert sha(b/(n+'.lean'))==r['source_sha256']
out.mkdir(exist_ok=False);env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out)]+deps)
for n in m['order']:
 (out/(n+'.lean')).write_bytes((b/(n+'.lean')).read_bytes())
 p=subprocess.run([str(lean),'-Ddebug.skipKernelTC=false','-M','1800','-o',n+'.olean',n+'.lean'],cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(n+'.log')).write_bytes(p.stdout)
 r={'module':n,'source_sha256':sha(out/(n+'.lean')),'exit':p.returncode}
 if not p.returncode:r['olean_sha256']=sha(out/(n+'.olean'))
 with (out/'REPLAY-EVENTS.jsonl').open('a')as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
 if p.returncode:raise SystemExit(p.returncode)
 for a in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',p.stdout.decode()):assert set(x.strip()for x in a.split(','))<={'propext','Quot.sound','Classical.choice'}
(out/'PASS.txt').write_text('15 accepted graph-syntax modules replayed. Candidate not compiled. Full NANUQ OPEN.\n')
