#!/usr/bin/env python3
"""Bounded fresh source rebuild, retaining exact original source bytes.

This does not establish any theorem beyond the successfully compiled source
statements, and never turns a conditional source bridge into a closure claim.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, time, sys, shutil

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / 'source/research/nanuq-all-level-2026-09-29/source-development/formal-full'
OBJECTS = ROOT / 'build/baseline-objects'
LOGS = ROOT / 'receipts/baseline-rebuild'
RECEIPT = ROOT / 'receipts/baseline-rebuild.json'
LEAN = ROOT / 'tooling/lean-4.33.1-linux/bin/lean'
MATHLIB = ROOT / 'build/mathlib'
EXCLUDED = {'GraphQuartetPortCounts', 'SourceProbe', 'ThetaProbe'}
OBJECTS.mkdir(parents=True, exist_ok=True)
LOGS.mkdir(parents=True, exist_ok=True)
modules = {p.stem:p for p in SOURCE.glob('*.lean') if p.stem not in EXCLUDED}
deps = {m: [x for line in p.read_text().splitlines() if line.startswith('import ')
            for x in line.split()[1:] if x in modules] for m,p in modules.items()}
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in deps[m]: visit(d)
    order.append(m)
for m in ['SourceFacts', 'SourceBlobFacts', 'AnchorComposition', 'CircularComposition',
          'CanonicalTheta', 'VerifiedCheckpoint']:
    visit(m)
for m in sorted(modules): visit(m)
env = os.environ.copy()
env['LEAN_PATH'] = ':'.join(map(str, [OBJECTS, MATHLIB/'.lake/build/lib/lean'] +
    [p/'.lake/build/lib/lean' for p in (MATHLIB/'.lake/packages').iterdir()]))
receipt = {'source_repository':'Sodelin/Work-on-Samuel-Alexander-Research-',
 'source_commit':'e2502c82ab9a77c00543932f775a71e5374221f7',
 'mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474',
 'compiler_version':subprocess.check_output([str(LEAN),'--version'],text=True).strip(),
 'status':'IN_PROGRESS','expected_modules':len(order),'excluded':sorted(EXCLUDED),
 'order':order,'modules':[],'raw_final_source_theorem':'ABSENT_NOT_CLAIMED',
 'entire_G_program':'NOT_CLAIMED'}
if '--resume' in sys.argv and RECEIPT.exists():
    previous=json.loads(RECEIPT.read_text())
    if previous['source_commit'] != receipt['source_commit'] or previous['mathlib_commit'] != receipt['mathlib_commit']:
        raise RuntimeError('Refusing to resume a different pinned source/dependency set')
    receipt['attempts']=previous.get('attempts',[])
    receipt['modules']=[]
    for row in previous['modules']:
        m=row['module']
        if row['source_sha256'] != hashlib.sha256(modules[m].read_bytes()).hexdigest():
            raise RuntimeError('Refusing to reuse a changed source module: '+m)
        if row['exit_code']==0 and not row['error_or_sorryAx'] and (OBJECTS/(m+'.olean')).exists():
            receipt['modules'].append(row)
        else:
            receipt['attempts'].append(row)
            old=LOGS/(m+'.log')
            if old.exists(): shutil.copyfile(old, LOGS/(m+f'.attempt{len(receipt["attempts"])}.log'))
def save():
    tmp = RECEIPT.with_suffix('.tmp')
    tmp.write_text(json.dumps(receipt,indent=2)+'\n'); tmp.replace(RECEIPT)
save()
started = time.monotonic()
for m in order:
    if any(row['module']==m for row in receipt['modules']): continue
    if time.monotonic()-started > 1800:
        receipt['status']='BOUNDED_WINDOW_ENDED';save();break
    p = modules[m]; log = LOGS/(m+'.log'); start = time.monotonic()
    print(f'BUILD {len(receipt["modules"])+1}/{len(order)} {m}',flush=True)
    limit = 1200 if 'Certificate' in m else 120
    with log.open('w') as handle:
        try:
            cp=subprocess.run([str(LEAN),'-o',str(OBJECTS/(m+'.olean')),str(p)],
                cwd=SOURCE,env=env,stdout=handle,stderr=subprocess.STDOUT,timeout=limit)
            rc=cp.returncode
        except subprocess.TimeoutExpired:rc=124
    content=log.read_text()
    row={'module':m,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
      'exit_code':rc,'elapsed_seconds':round(time.monotonic()-start,3),
      'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
      'axiom_lines':[x for x in content.splitlines() if 'axioms' in x],
      'error_or_sorryAx':bool(re.search(r'\berror\b|sorryAx',content))}
    receipt['modules'].append(row);save()
    print(f'EXIT {m} {rc} in {row["elapsed_seconds"]}s',flush=True)
    if rc or row['error_or_sorryAx']:
        receipt['status']='STOPPED_AT_FAILED_MODULE';save();break
else:
    receipt['status']='PASS_ALL_INCLUDED_MODULES';save()
print(json.dumps({'status':receipt['status'],'completed':len(receipt['modules']),
                  'expected':len(order)}),flush=True)
