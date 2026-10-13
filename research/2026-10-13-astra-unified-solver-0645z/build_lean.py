#!/usr/bin/env python3
"""Freshly compile the small kernel and optional generated certificate proofs.

Run under guard.py. This compiles owned modules serially and never launches a
dependency build. A missing external object is a hard failure. It does not
compile the accepted1613 components or the unavailable physical provider.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from build_mathlib_serial import setup, sha, artifacts, LEAN_SHA, PIN

HERE=Path(__file__).resolve().parent
EXPECTED_THEOREMS={
    'squareTerm_nonnegative','square_identity_nonnegative','supported_atom_is_root',
    'joint_supported_bank_is_root','singleton_generator_identity',
    'singleton_generator_nonnegative','singleton_generator_annihilates','singleton_generator_nonzero'}
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}


def audit(text):
    if 'sorryAx' in text:
        raise ValueError('placeholder axiom in actual compiler output')
    rows={}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",text):
        values=[s.strip() for s in axioms.split(',') if s.strip()]
        if set(values)-ALLOWED_AXIOMS:
            raise ValueError('nonstandard axiom: '+name)
        rows[name]=values
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):
        rows[name]=[]
    return rows


def verify_dependency_state(state,repos):
    plan=json.loads((state/'PLAN.json').read_text())
    if plan['mathlib_pin']!=PIN or plan['compiler_sha256']!=LEAN_SHA:
        raise ValueError('dependency execution pin differs')
    rows=[]
    for index,row in enumerate(plan['modules']):
        receipt=state/(str(index).zfill(4)+'.json')
        observed=json.loads(receipt.read_text())
        target=Path(row['target'])
        if observed['exit_code']!=0 or observed['source_sha256']!=sha(Path(row['source'])):
            raise ValueError('unverified dependency source: '+row['module'])
        if not observed['artifacts'] or observed['artifacts']!=artifacts(target):
            raise ValueError('dependency object identity changed: '+row['module'])
        relative=Path(*row['module'].split('.')).with_suffix('.olean')
        selected=next((repo/'.lake/build/lib/lean'/relative for repo in repos
                       if (repo/'.lake/build/lib/lean'/relative).is_file()),None)
        if selected!=target:
            raise ValueError('dependency is shadowed by a different object: '+row['module'])
        rows.append(dict(module=row['module'],source_sha256=row['source_sha256'],
                         receipt_sha256=sha(receipt),artifacts=observed['artifacts']))
    return dict(plan_sha256=sha(state/'PLAN.json'),modules=rows,
                execution='fresh serial source compilations, authenticated reuse by kernel build')


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean-bin',type=Path,default=os.environ.get('ASTRA_LEAN_BIN'))
    p.add_argument('--mathlib-root',type=Path,default=os.environ.get('ASTRA_MATHLIB_ROOT'))
    p.add_argument('--mathlib-state',type=Path,default=os.environ.get('ASTRA_MATHLIB_STATE'))
    p.add_argument('--out',type=Path,default=os.environ.get('ASTRA_LEAN_OUTPUT'))
    p.add_argument('--extra-source',action='append',type=Path,default=[])
    a=p.parse_args()
    if not a.lean_bin or not a.mathlib_root or not a.mathlib_state or not a.out:
        p.error('--lean-bin, --mathlib-root, --mathlib-state and fresh --out are required (or ASTRA_* environment)')
    a.lean_bin=a.lean_bin.resolve(); a.mathlib_root=a.mathlib_root.resolve(); a.out=a.out.resolve()
    repos,pins,env=setup(a.mathlib_root,a.lean_bin)
    dependency_state=verify_dependency_state(a.mathlib_state,repos)
    a.out.mkdir(parents=True,exist_ok=False)
    build=a.out/'lib/lean'
    env['LEAN_PATH']=str(build)+os.pathsep+env['LEAN_PATH']
    sources=[HERE/'lean/Astra/CommonCertificateKernel.lean',HERE/'lean/AstraKernel.lean',*a.extra_source]
    rows=[]; axioms={}
    for index,source in enumerate(sources):
        source=source.resolve()
        data=source.read_bytes()
        # These controlled source files contain no such tokens even in prose;
        # the actual printed axiom audit below is the semantic placeholder check.
        if re.search(rb'\b(sorry|admit|axiom|unsafe)\b',data):
            raise ValueError('forbidden placeholder/axiom token: '+str(source))
        root=HERE/'lean' if source.is_relative_to(HERE/'lean') else source.parent
        relative=source.relative_to(root)
        saved=a.out/'source'/relative
        saved.parent.mkdir(parents=True,exist_ok=True)
        saved.write_bytes(data)
        target=build/relative.with_suffix('.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        command=[str(a.lean_bin/'lean'),'-j','1','-s','8192','-R',str(root),'-o',str(target),str(source)]
        started=time.monotonic()
        result=subprocess.run(command,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        (a.out/(str(index)+'.stdout')).write_bytes(result.stdout)
        (a.out/(str(index)+'.stderr')).write_bytes(result.stderr)
        record=dict(module='.'.join(relative.with_suffix('').parts),source=str(source),source_sha256=sha(source),
                    command=command,exit_code=result.returncode,seconds=time.monotonic()-started,
                    artifacts=artifacts(target),stdout_sha256=sha(a.out/(str(index)+'.stdout')),
                    stderr_sha256=sha(a.out/(str(index)+'.stderr')))
        rows.append(record)
        (a.out/'COMPILATION.json').write_text(json.dumps(rows,indent=2)+'\n')
        print(result.stdout.decode(),end=''); print(result.stderr.decode(),end='')
        if result.returncode:
            raise SystemExit(result.returncode)
        axioms.update(audit(result.stdout.decode()))
    expected={'Astra.CommonCertificateKernel.'+name for name in EXPECTED_THEOREMS}
    if not expected.issubset(axioms):
        raise ValueError('not every required theorem appeared in actual axiom output')
    receipt=dict(status='FRESH_KERNEL_AND_AGGREGATE_COMPILED',compiler_sha256=LEAN_SHA,
                 mathlib_revision=PIN,mathlib_dependencies=pins,compiled=rows,axioms=axioms,
                 external_execution=dependency_state,
                 axiom_allowlist=sorted(ALLOWED_AXIOMS),owned_axioms=0,placeholder_axioms=0,
                 external_components='Previously compiled pinned Mathlib/toolchain objects, not rebuilt by this command.',
                 original1613_components='Not compiled by this command; authenticated by accepted_baseline target.',
                 physical_provider='Unavailable; not axiomatized or substituted.')
    (a.out/'RESULT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(dict(status=receipt['status'],compiled_modules=[r['module'] for r in rows])))


if __name__=='__main__':
    main()
