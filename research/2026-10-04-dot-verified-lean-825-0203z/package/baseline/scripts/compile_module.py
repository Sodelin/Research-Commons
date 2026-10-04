#!/usr/bin/env python3
"""One canonical, serialized, immutable bounded compiler/axiom receipt route."""
from pathlib import Path
import fcntl, hashlib, json, os, re, resource, shutil, subprocess, sys, time

ROOT=Path(__file__).resolve().parents[1]
from toolchain import binary_dir
TOOL=binary_dir()
module=sys.argv[1]
limit=int(sys.argv[2]) if len(sys.argv)>2 else 90
memory=int(sys.argv[3]) if len(sys.argv)>3 else 4096
rel=Path(*module.split('.')).with_suffix('.lean')
src=ROOT/rel
if not src.exists(): src=ROOT/'Imported'/rel
data=src.read_bytes();digest=hashlib.sha256(data).hexdigest()
with (ROOT/'.build.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX)
  frozen=ROOT/'receipts/immutable'/digest/('attempt-'+str(time.time_ns()))
  frozen.mkdir(parents=True)
  frozen_source=frozen/rel;frozen_source.parent.mkdir(parents=True,exist_ok=True)
  frozen_source.write_bytes(data)
  staged=frozen/rel.with_suffix('.olean');staged.parent.mkdir(parents=True,exist_ok=True)
  output=ROOT/'.lake/build/lib/lean'/rel.with_suffix('.olean')
  roots=[ROOT/'.lake/build/lib/lean',ROOT/'deps/mathlib/.lake/build/lib/lean']
  roots+=list((ROOT/'.lake/packages').glob('*/.lake/build/lib/lean'))
  env=os.environ.copy();env['PATH']=str(TOOL)+':'+env.get('PATH','')
  env['LEAN_PATH']=':'.join(map(str,roots))
  imports=[x for line in data.decode().splitlines() if line.startswith('import ') for x in line[7:].split()]
  def dependencies():
    found={}
    for name in imports:
      for directory in roots:
        p=directory/Path(*name.split('.')).with_suffix('.olean')
        if p.exists():found[name]=hashlib.sha256(p.read_bytes()).hexdigest();break
    return found
  before=dependencies();log=frozen/rel.with_suffix('.log')
  command=['timeout',str(limit),str(TOOL/'lean'),'-j1','-M'+str(memory),'-o',str(staged),str(rel)]
  start=time.monotonic()
  with log.open('w') as f:
    completed=subprocess.run(command,cwd=frozen,env=env,stdout=f,stderr=subprocess.STDOUT)
  after=dependencies();text=log.read_text()
  audits=[' '.join(x.split()) for x in re.findall(r"'[^']+' depends on axioms: \[.*?\]|'[^']+' does not depend on any axioms",text,re.S)]
  bad=[]
  for line in audits:
    m=re.search(r'\[(.*?)\]',line)
    if m:bad += [a.strip() for a in m.group(1).split(',') if a.strip() not in {'propext','Classical.choice','Quot.sound'}]
  accepted=completed.returncode==0 and before==after and not bad
  receipt={'module':module,'status':'PASS_LOCAL_COMPONENT' if accepted else 'FAILED_ATTEMPT',
    'compiler':'Lean4.33.1 commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6',
    'mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474',
    'command':command,'exit_code':completed.returncode,'elapsed_seconds':time.monotonic()-start,
    'child_max_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    'source_sha256':digest,'source_matches_working_copy':hashlib.sha256(src.read_bytes()).hexdigest()==digest,
    'direct_import_olean_sha256':before,'imports_stable':before==after,
    'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),
    'axiom_lines':audits,'nonstandard_axioms':sorted(set(bad)),
    'immutable_snapshot':str(frozen.relative_to(ROOT))}
  if completed.returncode==0:receipt['olean_sha256']=hashlib.sha256(staged.read_bytes()).hexdigest()
  if accepted:
    output.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(staged,output)
  dest=frozen/'receipt.json';dest.write_text(json.dumps(receipt,indent=2)+'\n')
  latest=ROOT/'receipts'/rel.with_suffix('.json');latest.parent.mkdir(parents=True,exist_ok=True)
  latest.write_text(json.dumps(receipt,indent=2)+'\n')
  print(json.dumps(receipt,indent=2));print(text[-7000:])
  raise SystemExit(0 if accepted else 1)
