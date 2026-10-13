#!/usr/bin/env python3
"""Build only the exact kernel import closure, serially, with restart receipts.

Use guard.py around this command. No cache artifact is assumed authenticated:
reuse requires this runner's matching source and artifact receipt. Pinned
upstream compiler/library binaries remain trusted and are recorded separately.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
ROOTS = ['Mathlib.Data.Real.Basic', 'Mathlib.Algebra.BigOperators.Group.Finset.Basic',
         'Mathlib.Tactic.Ring', 'Mathlib.Tactic.Linarith', 'Mathlib.Tactic.Positivity']


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for part in iter(lambda:f.read(1024**2),b''):
            h.update(part)
    return h.hexdigest()


def setup(mathlib, lean_bin):
    if sha(lean_bin/'lean') != LEAN_SHA:
        raise ValueError('compiler identity changed')
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=mathlib,text=True).strip()!=PIN:
        raise ValueError('Mathlib source pin changed')
    repos = [mathlib]
    pins = []
    for row in json.loads((mathlib/'lake-manifest.json').read_text())['packages']:
        repo = mathlib/'.lake/packages'/row['name']
        if subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()!=row['rev']:
            raise ValueError('dependency source pin changed: '+row['name'])
        repos.append(repo)
        pins.append(dict(name=row['name'],revision=row['rev'],url=row['url']))
    # Tracked source modifications would silently diverge from pinned cache hashes.
    for repo in repos:
        if subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=repo,text=True):
            raise ValueError('modified pinned source: '+str(repo))
    env = os.environ.copy()
    env.update(LEAN_PATH=os.pathsep.join(str(p/'.lake/build/lib/lean') for p in repos),
               LEAN_SRC_PATH=os.pathsep.join(map(str,[*repos,lean_bin.parent/'src/lean'])),
               LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='8192', LEAN_IMPORT_WORKERS='1',
               MIMALLOC_ARENA_RESERVE='16384', RAYON_NUM_THREADS='1')
    return repos, pins, env


def source_for(name, repos):
    relative=Path(*name.split('.')).with_suffix('.lean')
    found=[repo/relative for repo in repos if (repo/relative).is_file()]
    if len(found)!=1:
        raise ValueError('missing/ambiguous source: '+name)
    return found[0]


def plan(mathlib, lean_bin, repos, env):
    done={}
    active=set()
    def visit(source):
        source=source.resolve()
        if source in done:
            return
        if source in active:
            raise ValueError('cyclic source dependencies')
        # Core Lean is the authenticated official toolchain, not rebuilt here.
        if source.is_relative_to(lean_bin.parent/'src/lean'):
            return
        active.add(source)
        out=subprocess.check_output([str(lean_bin/'lean'),'-j','1','-s','8192','--src-deps',str(source)],
                                    cwd=mathlib,env=env,text=True)
        imports=list(dict.fromkeys(str(Path(p).resolve()) for p in out.splitlines() if p))
        for dep in imports:
            visit(Path(dep))
        repo=max((p for p in repos if source.is_relative_to(p)),key=lambda p:len(p.parts))
        rel=source.relative_to(repo)
        target=repo/'.lake/build/lib/lean'/rel.with_suffix('.olean')
        done[source]=dict(source=str(source),source_sha256=sha(source),repo=str(repo),
                          module='.'.join(rel.with_suffix('').parts),target=str(target),imports=imports)
        active.remove(source)
    for name in ROOTS:
        visit(source_for(name,repos))
    return list(done.values())


def artifacts(target):
    return {str(path):sha(path) for suffix in ('.olean','.olean.private','.olean.server','.ir','.ir.sig')
            if (path:=target.with_suffix(suffix)).is_file()}


def release_own_file_cache(repos, lean_bin):
    # Advisory release only: no source, evidence or build artifact is deleted.
    if int(Path('/sys/fs/cgroup/memory.current').read_text()) < 3*1024**3:
        return
    for base in [lean_bin.parent/'lib/lean',*[p/'.lake/build' for p in repos]]:
        if not base.exists():
            continue
        for path in base.rglob('*'):
            if path.is_file():
                with path.open('rb') as f:
                    os.posix_fadvise(f.fileno(),0,0,os.POSIX_FADV_DONTNEED)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mathlib-root',type=Path,required=True)
    p.add_argument('--lean-bin',type=Path,required=True)
    p.add_argument('--state',type=Path,required=True)
    p.add_argument('--batch',type=int,default=128)
    a=p.parse_args()
    a.mathlib_root=a.mathlib_root.resolve(); a.lean_bin=a.lean_bin.resolve()
    a.state.mkdir(parents=True,exist_ok=True)
    repos,pins,env=setup(a.mathlib_root,a.lean_bin)
    planfile=a.state/'PLAN.json'
    if planfile.exists():
        stored=json.loads(planfile.read_text())
        if stored['mathlib_pin']!=PIN or stored['compiler_sha256']!=LEAN_SHA or stored['dependencies']!=pins:
            raise ValueError('state pin mismatch')
        rows=stored['modules']
    else:
        rows=plan(a.mathlib_root,a.lean_bin,repos,env)
        planfile.write_text(json.dumps(dict(mathlib_pin=PIN,compiler_sha256=LEAN_SHA,
                                          dependencies=pins,roots=ROOTS,modules=rows),indent=2)+'\n')
    fresh=reused=0
    for index,row in enumerate(rows):
        source=Path(row['source']); target=Path(row['target'])
        if sha(source)!=row['source_sha256']:
            raise ValueError('planned source changed: '+row['module'])
        receipt=a.state/(str(index).zfill(4)+'.json')
        if receipt.exists():
            old=json.loads(receipt.read_text())
            if old['exit_code']==0 and old['source_sha256']==row['source_sha256'] and old['artifacts']==artifacts(target):
                reused+=1
                continue
            raise ValueError('previous failure/artifact change needs explicit repair: '+row['module'])
        if fresh>=a.batch:
            break
        target.parent.mkdir(parents=True,exist_ok=True)
        command=[str(a.lean_bin/'lean'),'-j','1','-s','8192','-R',row['repo'],'-o',str(target),str(source)]
        started=time.monotonic()
        stdout=a.state/(str(index).zfill(4)+'.stdout')
        stderr=a.state/(str(index).zfill(4)+'.stderr')
        with stdout.open('xb') as out, stderr.open('xb') as err:
            result=subprocess.run(command,cwd=row['repo'],env=env,stdout=out,stderr=err)
        rec=dict(**row,command=command,exit_code=result.returncode,
                 seconds=time.monotonic()-started,artifacts=artifacts(target),
                 stdout_sha256=sha(stdout),stderr_sha256=sha(stderr))
        receipt.write_text(json.dumps(rec,indent=2)+'\n')
        print(json.dumps(dict(module=row['module'],index=index,exit_code=result.returncode,
                              seconds=rec['seconds'])),flush=True)
        if result.returncode:
            raise SystemExit(1)
        fresh+=1
        release_own_file_cache(repos,a.lean_bin)
    print(json.dumps(dict(status='BATCH_COMPLETE',freshly_compiled=fresh,authenticated_reuse=reused,
                          planned=len(rows),complete=fresh+reused==len(rows))),flush=True)


if __name__=='__main__':
    main()
