#!/usr/bin/env python3
"""Build the exact accepted-provider closure and new adapter serially.

Requires the fully authenticated external plan. Never run concurrently with
another compiler. Run under the unchanged guard from the previous packet.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'2026-10-13-astra-unified-solver-0645z'
PREVIOUS_MANIFEST_SHA='728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5'
manifest_path=PREVIOUS/'PACKET-MANIFEST.json'
if hashlib.sha256(manifest_path.read_bytes()).hexdigest()!=PREVIOUS_MANIFEST_SHA:
    raise ValueError('published previous packet manifest differs')
PREVIOUS_PINS={r['path']:r['sha256'] for r in json.loads(manifest_path.read_text())['files']}
for script in ['build_mathlib_serial.py','build_lean.py']:
    if hashlib.sha256((PREVIOUS/script).read_bytes()).hexdigest()!=PREVIOUS_PINS[script]:
        raise ValueError('published previous runner differs: '+script)
sys.path.insert(0,str(PREVIOUS))
from build_mathlib_serial import setup,sha,artifacts,release_own_file_cache,LEAN_SHA,PIN
from build_lean import verify_dependency_state,audit
sys.path.insert(0,str(HERE))
from materialize_support import verify,selection

LOADED_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
NEW_MODULES=['Astra.PositiveSupportAdapter','Astra.EmittedSupportExamples','AstraPositiveSupport']
EXPECTED={
 'Astra.PositiveSupportAdapter.'+name for name in [
 'positive_support_card_le_pred','supplied_certificate_support_bound','threeLevels',
 'threeCoefficients_eval','quarter_emitted_support_bound','half_emitted_support_bound',
 'endpoint_emitted_support_bound']}
EXPECTED.add('DotG4.ActualPositiveGridUniqueness.positiveCertificateGrid_card_lt')

def relative(module):return Path(*module.split('.')).with_suffix('.lean')

def authenticate_artifacts(observed,target):
    actual=artifacts(target)
    if str(target) not in actual or actual!=observed:
        raise ValueError('missing or changed module artifacts: '+str(target))
    return set(actual)


def read_audit_logs(state,index,receipt):
    logs={}
    for suffix in ['stdout','stderr']:
        path=state/(str(index).zfill(4)+'.'+suffix)
        if sha(path)!=receipt[suffix+'_sha256']:
            raise ValueError('compiler log differs: '+str(path))
        logs[suffix]=path.read_text()
    actual=audit(logs['stdout']+'\n'+logs['stderr'])
    if "declaration uses 'sorry'" in logs['stdout']+logs['stderr']:
        raise ValueError('placeholder warning rejected')
    return actual


def authenticated_previous(pins):
    directory=PREVIOUS/'evidence/lake-generated-certificates-real-repair/compilation'
    path=directory/'RESULT.json'
    if sha(path)!=PREVIOUS_PINS[str(path.relative_to(PREVIOUS))]:
        raise ValueError('published previous compilation receipt differs')
    previous=json.loads(path.read_text())
    if (previous['compiler_sha256']!=LEAN_SHA or previous['mathlib_revision']!=PIN
            or previous['mathlib_dependencies']!=pins):
        raise ValueError('previous compilation context differs')
    parsed={}
    for index,row in enumerate(previous['compiled']):
        for suffix in ['stdout','stderr']:
            log=directory/f'{index}.{suffix}'
            if sha(log)!=row[suffix+'_sha256'] or sha(log)!=PREVIOUS_PINS[str(log.relative_to(PREVIOUS))]:
                raise ValueError('published previous compiler log differs')
            text=log.read_text()
            if "declaration uses 'sorry'" in text:raise ValueError('previous placeholder warning')
            parsed.update(audit(text))
    if parsed!=previous['axioms']:
        raise ValueError('previous parsed audit differs from receipt')
    return previous

def clone_artifacts(origin,target):
    copied={}
    for name,digest in origin.items():
        path=Path(name)
        if sha(path)!=digest:raise ValueError('reused object identity changed: '+name)
        stem=path.name.split('.olean')[0] if '.olean' in path.name else path.name.split('.ir')[0]
        suffix=path.name[len(stem):]
        dest=target.with_suffix(suffix)
        dest.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(path,dest)
        if sha(dest)!=digest:raise ValueError('object copy identity changed')
        copied[str(dest)]=digest
    return copied


def copied_artifact_map(origin,target):
    mapped={}
    for name,digest in origin.items():
        path=Path(name)
        suffix=next((suffix for suffix in ['.olean.private','.olean.server','.ir.sig','.olean','.ir']
                     if path.name.endswith(suffix)),None)
        if suffix is None:raise ValueError('unknown artifact suffix: '+name)
        destination=str(target.with_suffix(suffix))
        if destination in mapped:raise ValueError('duplicate artifact destination')
        mapped[destination]=digest
    if str(target) not in mapped:raise ValueError('reuse origin has no Lean object')
    return mapped


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root',type=Path,required=True)
    p.add_argument('--external-state',type=Path,required=True)
    p.add_argument('--state',type=Path,required=True)
    p.add_argument('--mathlib-root',type=Path,required=True)
    p.add_argument('--lean-bin',type=Path,required=True)
    p.add_argument('--batch',type=int,default=16)
    p.add_argument('--prepare-provider',action='store_true')
    p.add_argument('--require-complete',action='store_true')
    a=p.parse_args()
    a.source_root=a.source_root.resolve();a.state=a.state.resolve()
    a.mathlib_root=a.mathlib_root.resolve();a.lean_bin=a.lean_bin.resolve()
    verify(a.source_root)
    repos,pins,env=setup(a.mathlib_root,a.lean_bin)
    if (a.external_state/'PLAN.json').read_bytes()!=(HERE/'EXTERNAL-PLAN.json').read_bytes():
        raise ValueError('external plan differs from exact selected closure')
    external=verify_dependency_state(a.external_state,repos,a.lean_bin,pins)
    external_plan=json.loads((a.external_state/'PLAN.json').read_text())
    # The frozen helper authenticates object identity and lookup order. Bind
    # the exact selected source hash and complete log bytes here as well.
    for index,row in enumerate(external_plan['modules']):
        observed=json.loads((a.external_state/f'{index:04d}.json').read_text())
        if any(observed[key]!=row[key] for key in ['module','source','source_sha256','repo','target','imports']):
            raise ValueError('external receipt differs from selected source graph')
        if sha(Path(row['source']))!=row['source_sha256']:
            raise ValueError('external source differs from exact plan')
        authenticate_artifacts(observed['artifacts'],Path(row['target']))
        for suffix in ['stdout','stderr']:
            if sha(a.external_state/f'{index:04d}.{suffix}')!=observed[suffix+'_sha256']:
                raise ValueError('external compiler log differs')
    external_rows={r['module']:r for r in external['modules']}
    external_sources={r['module']:r for r in external_plan['modules']}
    old=authenticated_previous(pins)
    old_rows={r['module']:r for r in old['compiled']}
    old_names=['Astra.CommonCertificateKernel']+sorted(p.stem for p in (HERE/'lean').glob('Certificate_*.lean'))
    modules=[dict(r,kind='accepted1613') for r in selection()['owned']]
    for name in old_names+NEW_MODULES:
        modules.append(dict(module=name,sha256=sha(a.source_root/relative(name)),
                            kind='previous_kernel_certificate' if name in old_names else 'new_adapter'))
    a.state.mkdir(parents=True,exist_ok=True)
    plan_path=a.state/'PLAN.json'
    plan=dict(compiler_sha256=LEAN_SHA,mathlib_pin=PIN,external_plan_sha256=external['plan_sha256'],modules=modules)
    if plan_path.exists() and json.loads(plan_path.read_text())!=plan:
        raise ValueError('owned source plan changed; preserve failure and repair explicitly')
    if not plan_path.exists():plan_path.write_text(json.dumps(plan,indent=2)+'\n')
    build=a.state/'.lake/build/lib/lean'
    # Authenticate every object in the prepended path before any compiler can
    # use it. Unreceipted leftovers are preserved and rejected, never deleted.
    allowed=set(); resumed={}
    for index,row in enumerate(modules):
        receipt=a.state/f'{index:04d}.json'
        if not receipt.exists():continue
        observed=json.loads(receipt.read_text())
        name=row['module'];target=build/relative(name).with_suffix('.olean')
        if (observed['exit_code']!=0 or observed['source_sha256']!=row['sha256']
                or observed['module']!=name or observed['kind']!=row['kind']):
            raise ValueError('failed/altered receipt needs explicit repair: '+name)
        allowed.update(authenticate_artifacts(observed['artifacts'],target))
        if observed['execution']=='FRESH_SOURCE_COMPILE':
            parsed=read_audit_logs(a.state,index,observed)
            if parsed!=observed['axioms']:raise ValueError('resumed audit metadata differs: '+name)
        elif observed['execution']=='AUTHENTICATED_REUSE':
            origin=observed['origin']
            expected=external_rows[name] if name.startswith('Mathlib.') else old_rows[name]
            expected_kind=('authenticated_identical_selected_mathlib' if name.startswith('Mathlib.')
                           else 'authenticated_previous_kernel_certificate')
            if origin!={'kind':expected_kind,'receipt':expected} or observed['axioms']!={}:
                raise ValueError('resumed reuse origin differs: '+name)
            if expected['source_sha256']!=row['sha256']:
                raise ValueError('resumed reuse source differs: '+name)
            if observed['artifacts']!=copied_artifact_map(expected['artifacts'],target):
                raise ValueError('resumed copy differs from authenticated origin: '+name)
        else:raise ValueError('unknown execution mode: '+name)
        resumed[index]=observed
    actual={str(p) for p in build.rglob('*') if p.is_file()}
    if actual!=allowed:raise ValueError('unauthenticated owned search-path files: '+str(sorted(actual-allowed)))
    env['LEAN_PATH']=str(build)+os.pathsep+env['LEAN_PATH']
    fresh=reused=0;axioms={}
    for index,row in enumerate(modules):
        name=row['module'];source=a.source_root/relative(name);target=build/relative(name).with_suffix('.olean')
        if sha(source)!=row['sha256']:raise ValueError('selected source changed: '+name)
        receipt=a.state/f'{index:04d}.json'
        if index in resumed:
            observed=resumed[index]
            axioms.update(observed.get('axioms',{}));reused+=1;continue
        if fresh>=a.batch or (a.prepare_provider and row['kind']=='new_adapter'):break
        if row['kind']=='new_adapter' and re.search(rb'\b(sorry|admit|axiom|unsafe)\b',source.read_bytes()):
            raise ValueError('owned placeholder/axiom token rejected: '+name)
        saved=a.state/'source'/relative(name);saved.parent.mkdir(parents=True,exist_ok=True)
        saved.write_bytes(source.read_bytes())
        origin=None
        if name.startswith('Mathlib.'):
            if external_sources[name]['source_sha256']!=row['sha256']:
                raise ValueError('owned Mathlib selection differs from prepared upstream source')
            origin=dict(kind='authenticated_identical_selected_mathlib',receipt=external_rows[name])
        elif name in old_rows:
            candidate=old_rows[name]
            if candidate['source_sha256']!=row['sha256'] or candidate['exit_code']!=0:
                raise ValueError('prior kernel/certificate source identity differs')
            if all(Path(path).is_file() for path in candidate['artifacts']):
                origin=dict(kind='authenticated_previous_kernel_certificate',receipt=candidate)
        if origin:
            origin_artifacts=origin['receipt']['artifacts']
            if not origin_artifacts or not any(path.endswith('.olean') for path in origin_artifacts):
                raise ValueError('reuse origin has no Lean object: '+name)
            copied=clone_artifacts(origin['receipt']['artifacts'],target)
            authenticate_artifacts(copied,target)
            observed=dict(module=name,source=str(source),source_sha256=row['sha256'],kind=row['kind'],
                          execution='AUTHENTICATED_REUSE',origin=origin,exit_code=0,artifacts=copied,
                          runner_sha256=LOADED_SHA,axioms={})
            receipt.write_text(json.dumps(observed,indent=2)+'\n');reused+=1
            continue
        target.parent.mkdir(parents=True,exist_ok=True)
        command=[str(a.lean_bin/'lean'),'-j','1','-s','8192','-R',str(a.source_root),'-o',str(target),str(source)]
        stdout=a.state/f'{index:04d}.stdout';stderr=a.state/f'{index:04d}.stderr'
        started=time.monotonic()
        with stdout.open('xb') as out,stderr.open('xb') as err:
            result=subprocess.run(command,cwd=a.source_root,env=env,stdout=out,stderr=err)
        text=stdout.read_text()+'\n'+stderr.read_text()
        observed=dict(module=name,source=str(source),source_sha256=row['sha256'],kind=row['kind'],
                      execution='FRESH_SOURCE_COMPILE',command=command,exit_code=result.returncode,
                      seconds=time.monotonic()-started,artifacts=artifacts(target),
                      stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),runner_sha256=LOADED_SHA)
        if not result.returncode:
            try:
                observed['axioms']=audit(text)
                if "declaration uses 'sorry'" in text:raise ValueError('placeholder warning rejected')
                authenticate_artifacts(observed['artifacts'],target)
                axioms.update(observed['axioms'])
            except ValueError as error:
                observed.update(compiler_exit_code=0,exit_code=2,audit_failure=str(error))
        receipt.write_text(json.dumps(observed,indent=2)+'\n')
        print(json.dumps(dict(module=name,index=index,exit_code=observed['exit_code'],
                              compiler_exit_code=result.returncode,seconds=observed['seconds'])),flush=True)
        if observed['exit_code']:raise SystemExit(1)
        fresh+=1
        release_own_file_cache(repos+[a.state],a.lean_bin)
    complete=fresh+reused==len(modules)
    summary=dict(status='BATCH_COMPLETE',freshly_compiled=fresh,authenticated_reuse=reused,
                 planned=len(modules),complete=complete)
    if complete:
        if not EXPECTED.issubset(axioms):raise ValueError('required theorem missing from actual axiom output')
        result=dict(status='EXACT_ACCEPTED_PROVIDER_AND_SUPPORT_ADAPTER_VERIFIED',
                    modules=modules,axioms=axioms,owned_axioms=0,placeholder_axioms=0,
                    compiler_sha256=LEAN_SHA,mathlib_pin=PIN,external_execution=external,
                    full1613_aggregate_compiled=False,physical_representative_claimed=False)
        (a.state/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(summary),flush=True)
    if a.require_complete and not complete:
        raise SystemExit('Exact provider preparation is incomplete; no adapter completion claimed.')

if __name__=='__main__':main()
