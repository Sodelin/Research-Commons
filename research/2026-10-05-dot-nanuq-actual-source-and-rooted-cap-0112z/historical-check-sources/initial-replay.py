#!/usr/bin/env python3
"""Portable serial replay of the delivered current proof sources and kernel guards."""
import hashlib,json,os,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parent
binding=json.loads((root/'SOURCE-BINDINGS.json').read_text())
for row in binding['files']:
    b=(root/row['path']).read_bytes()
    if len(b)!=row['bytes'] or hashlib.sha256(b).hexdigest()!=row['sha256']:
        raise SystemExit('Source binding mismatch: '+row['path'])
package=root/'package'; out=package/'reproduction';out.mkdir(exist_ok=True)
env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
def run(name,args):
    with (out/(name+'.stdout')).open('wb') as stdout,(out/(name+'.stderr')).open('wb') as stderr:
        result=subprocess.run(args,cwd=package,env=env,stdout=stdout,stderr=stderr)
    (out/(name+'.exit')).write_text(str(result.returncode)+'\n')
    if result.returncode: raise SystemExit('Failed '+name+'; see reproduction logs')
run('ordinary',['lake','build'])
objects=package/'.lake/build/lib/lean/guards';objects.mkdir(parents=True,exist_ok=True)
for module in binding['owned_modules']:
    obj=objects/(module+'.olean')
    run('guard-'+module,['lake','env','lean','-j1','-M4096','-o',str(obj),'-i',str(obj.with_suffix('.ilean')),str(package/'guards'/(module+'.lean'))])
(package/'certification-twentytwo').mkdir(exist_ok=True)
for label in ['Owned','Closure','GuardedOwned','GuardedClosure']:
    run('audit-'+label,['lake','env','lean','-j1','-M4096','AuditTwentytwo'+label+'.lean'])
    report=json.loads((package/'certification-twentytwo'/('AUDIT-'+label.upper()+'.json')).read_text())
    if report['owned_axioms'] or report['nonstandard_axiom_rows'] or report['missing_modules']:
        raise SystemExit('Audit failure '+label)
run('default-after-guards',['lake','build'])
print('PASS: fresh serial owned-source/guard/audit replay. Original retained evidence was not overwritten.')
