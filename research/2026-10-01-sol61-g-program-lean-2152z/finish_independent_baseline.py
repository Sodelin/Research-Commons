#!/usr/bin/env python3
"""Finish only baseline modules independent of the resource-blocked certificate.

Never retries ThetaCertificate6, never changes source bytes, and never claims
that blocked dependent modules or the final raw source theorem were checked.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,time

R=Path(__file__).resolve().parent
S=R/'source/research/nanuq-all-level-2026-09-29/source-development/formal-full'
O=R/'build/baseline-objects'
M=R/'build/mathlib'
LOG=R/'receipts/baseline-rebuild'
previous=json.loads((R/'receipts/baseline-rebuild.json').read_text())
verified={row['module']:row for row in previous['modules']
          if row['exit_code']==0 and not row['error_or_sorryAx']}
failed={row['module'] for row in previous['modules'] if row['exit_code']!=0}
for name,row in verified.items():
    if hashlib.sha256((S/(name+'.lean')).read_bytes()).hexdigest()!=row['source_sha256']:
        raise RuntimeError('Pinned source changed: '+name)
    if not (O/(name+'.olean')).exists(): raise RuntimeError('Missing checked object: '+name)
env=os.environ.copy()
env['LEAN_PATH']=':'.join(map(str,[O,M/'.lake/build/lib/lean']+
                     [p/'.lake/build/lib/lean' for p in (M/'.lake/packages').iterdir()]))
out={'source_repository':previous['source_repository'],'source_commit':previous['source_commit'],
     'mathlib_commit':previous['mathlib_commit'],'compiler_version':previous['compiler_version'],
     'compile_parameters':['-j1','-M2048'],'status':'IN_PROGRESS',
     'expected_modules':previous['expected_modules'],'verified_modules':list(verified.values()),
     'resource_blocked':sorted(failed),'blocked_dependents':[],
     'prior_attempts':previous.get('attempts',[])+[row for row in previous['modules'] if row['exit_code']!=0],
     'excluded':previous['excluded'],'raw_final_source_theorem':'ABSENT_NOT_CLAIMED',
     'entire_G_program':'NOT_CLAIMED'}
P=R/'receipts/baseline-independent-completion.json'
def save():
    out['completed_successful_modules']=len(verified)
    temp=P.with_suffix('.tmp');temp.write_text(json.dumps(out,indent=2)+'\n');temp.replace(P)
save();start=time.monotonic()
for name in previous['order']:
    if name in verified or name in failed:continue
    if time.monotonic()-start>600:
        out['status']='BOUNDED_WINDOW_ENDED';save();break
    source=S/(name+'.lean')
    deps=[x for line in source.read_text().splitlines() if line.startswith('import ')
          for x in line.split()[1:] if (S/(x+'.lean')).exists()]
    blocked=[x for x in deps if x not in verified]
    if blocked:
        out['blocked_dependents'].append({'module':name,'unchecked_dependencies':blocked});save();continue
    print('BUILD_INDEPENDENT '+name,flush=True)
    log=LOG/(name+'.log');t=time.monotonic()
    with log.open('w')as handle:
        try:
            rc=subprocess.run([str(R/'tooling/lean-4.33.1-linux/bin/lean'),'-j1','-M2048',
                '-o',str(O/(name+'.olean')),str(source)],cwd=S,env=env,stdout=handle,
                stderr=subprocess.STDOUT,timeout=120).returncode
        except subprocess.TimeoutExpired:rc=124
    content=log.read_text()
    row={'module':name,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
      'exit_code':rc,'elapsed_seconds':round(time.monotonic()-t,3),
      'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
      'axiom_lines':[x for x in content.splitlines() if 'axioms' in x],
      'error_or_sorryAx':bool(re.search(r'\berror\b|sorryAx',content))}
    print(f'EXIT {name} {rc}',flush=True)
    if rc==0 and not row['error_or_sorryAx']:
        verified[name]=row;out['verified_modules'].append(row)
    else:
        failed.add(name);out['resource_blocked'].append(name);out['prior_attempts'].append(row)
    save()
else:
    out['status']='PARTIAL_PASS_WITH_RESOURCE_BLOCKED_DEPENDENCIES';save()
print(json.dumps({'status':out['status'],'verified':len(verified),
                 'resource_blocked':out['resource_blocked'],
                 'blocked_dependents':len(out['blocked_dependents'])}),flush=True)
