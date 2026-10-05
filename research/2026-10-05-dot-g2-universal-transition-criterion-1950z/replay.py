#!/usr/bin/env python3
"""Verify delivered bytes; --replay optionally rebuilds the portable Lean package."""
import argparse,gzip,hashlib,json,os,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parent
args=argparse.ArgumentParser(description=__doc__);args.add_argument('--replay',action='store_true');opt=args.parse_args()
manifest=json.loads((root/'PUBLIC-MANIFEST.json').read_bytes())
for name,row in manifest['files'].items():
 b=(root/name).read_bytes()
 if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:raise SystemExit('Mismatch: '+name)
for label in ['OWNED','CLOSURE','GUARDEDOWNED','GUARDEDCLOSURE']:
 p=root/'evidence'/('AUDIT-'+label+'.json');p=p if p.exists() else p.with_suffix('.json.gz');b=p.read_bytes();a=json.loads(gzip.decompress(b) if p.suffix=='.gz' else b)
 if a['owned_axioms'] or a['nonstandard_axiom_rows'] or a['missing_modules']:raise SystemExit('Failed recorded audit '+label)
print('Delivered files and recorded audit gates verified.')
if not opt.replay:raise SystemExit(0)
package=root/'package';out=package/'certification';out.mkdir(exist_ok=False);env=dict(os.environ,LEAN_NUM_THREADS='1')
def run(name,cmd,cwd):
 with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:r=subprocess.run(cmd,cwd=cwd,env=env,stdout=stdout,stderr=stderr)
 (out/(name+'.exit')).write_text(str(r.returncode)+'\n')
 if r.returncode:raise SystemExit('Replay failed: '+name)
run('lake-default',['lake','build'],package)
owned=json.loads((root/'SOURCE-BINDINGS.json').read_bytes())['owned_modules'];objects=package/'.lake/build/lib/lean/guards';objects.mkdir(parents=True,exist_ok=True)
for m in owned:run('guard-'+m,['lake','env','lean','-j1','-M4096','-o',str(objects/(m+'.olean')),'guards/'+m+'.lean'],package/'src')
for label in ['Owned','Closure','GuardedOwned','GuardedClosure']:
 run('audit-'+label,['lake','env','lean','-j1','-M4096','Audit'+label+'.lean'],package/'src')
 a=json.loads((out/('AUDIT-'+label.upper()+'.json')).read_bytes())
 if a['owned_axioms'] or a['nonstandard_axiom_rows'] or a['missing_modules']:raise SystemExit('Replay audit failed: '+label)
print('Requested package replay completed. Inspect the new local receipts.')
