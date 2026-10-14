#!/usr/bin/env python3
"""Export authenticated final source/receipt/log evidence, excluding binaries."""
import argparse
import collections
import json
from pathlib import Path

import build_support_namespace as support
import audit_support_namespace as interface

HERE=Path(__file__).resolve().parent
FINAL_LIMITS=dict(cpu_seconds=600,wall_seconds=900,address_space_bytes=6*1024**3,
                  file_bytes=1024**3,disk_floor=8*1024**3,ram_floor=1024**3,
                  cgroup_stop=4*1024**3)


def copy(source,target,expected=None):
    digest=support.sha(source)
    if expected is not None and digest!=expected:
        raise ValueError('evidence identity differs: '+str(source))
    target.parent.mkdir(parents=True,exist_ok=True)
    with target.open('xb') as handle:handle.write(source.read_bytes())
    if support.sha(target)!=digest:raise ValueError('evidence copy differs')
    return digest


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['source-root','state','external-state','mathlib-root','lean-bin','lake-output','out']:
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    for name in interface.ARGUMENTS+['lake_output','out']:
        setattr(args,name,getattr(args,name).resolve())
    source_readback=support.verify(args.source_root)
    result_path=args.state/'RESULT.json'
    complete=json.loads(result_path.read_text())
    plan=json.loads((args.state/'PLAN.json').read_text())
    if (complete['status']!='EXACT_ACCEPTED_PROVIDER_AND_SUPPORT_ADAPTER_VERIFIED'
            or complete['modules']!=plan['modules']):
        raise ValueError('complete exact owned plan is required')
    guarded=json.loads((args.lake_output/'RECEIPT.json').read_text())
    if guarded['exit_code']!=0 or guarded['stop'] is not None:
        raise ValueError('final Lake invocation did not pass')
    guard_pin=support.PREVIOUS_PINS['guard.py']
    if (guarded.get('runner_sha256')!=guard_pin
            or support.sha(support.PREVIOUS/'guard.py')!=guard_pin):
        raise ValueError('final guard is not the pinned reviewed implementation')
    if guarded.get('limits')!=FINAL_LIMITS:
        raise ValueError('final guard limits differ from the approved profile')
    if guarded.get('cwd')!=str(HERE) or guarded['command']!=interface.lake_command(args):
        raise ValueError('receipt must bind this packet and exact native Lake adapter invocation')
    if support.sha(args.lean_bin/'lake')!=interface.LAKE_SHA:
        raise ValueError('selected Lake executable changed')
    for suffix in ['stdout','stderr']:
        if support.sha(args.lake_output/suffix)!=guarded['outputs'][suffix]['sha256']:
            raise ValueError('final guarded output changed')
    # Reauthenticate complete receipt origins as well as object and log hashes.
    # This mode cannot compile missing modules, and catches changed reuse origins.
    auth_command,authenticated=interface.authenticate_complete(args)
    complete=json.loads(result_path.read_text())
    plan=json.loads((args.state/'PLAN.json').read_text())

    audit_dir=args.state/'interface-audit'
    audited=json.loads((audit_dir/'RESULT.json').read_text())
    if audited['exit_code']!=0 or audited['status']!='EXACT_SELECTED_INTERFACE_CHECKED':
        raise ValueError('explicit selected-interface audit did not pass')
    binding=audited['binding']
    required_binding=dict(owned_plan_sha256=support.sha(args.state/'PLAN.json'),
        owned_result_sha256=support.sha(result_path),
        external_plan_sha256=support.sha(args.external_state/'PLAN.json'),
        source_sha256=support.sha(interface.SOURCE),
        runner_sha256=support.sha(HERE/'audit_support_namespace.py'),
        authenticator_sha256=support.sha(HERE/'build_support_namespace.py'),
        owned_receipts_sha256=interface.ledger_digest(args.state,plan),
        lakefile_sha256=support.sha(HERE/'lakefile.namespace.lean'),lake_sha256=interface.LAKE_SHA,
        arguments={name:str(getattr(args,name)) for name in interface.ARGUMENTS},
        compiler_sha256=support.LEAN_SHA,mathlib_pin=support.PIN,
        namespace_sha256=plan['namespace_sha256'],
        environment=plan['namespace_resolution']['selected_environment'])
    if any(binding.get(key)!=value for key,value in required_binding.items()):
        raise ValueError('interface audit binding differs from final sources/receipts')
    if support.sha(audit_dir/'source.lean')!=binding['source_sha256']:
        raise ValueError('saved interface source differs from the executed source')
    if json.loads((audit_dir/'INVOCATION.json').read_text())['binding']!=binding:
        raise ValueError('saved interface invocation differs from its result')
    if audited['resource_control']['helper_sha256']!=support.sha(HERE/'serial_compile.py'):
        raise ValueError('executed interface helper differs from captured configuration')
    expected_output=interface.output_binding(args,binding,audit_dir/'RESULT.json')
    observed=[]
    for line in (args.lake_output/'stdout').read_text().splitlines():
        try:row=json.loads(line)
        except json.JSONDecodeError:continue
        if isinstance(row,dict) and row.get('status')=='FINAL_INTERFACE_EXECUTION_BINDING':
            observed.append(row)
    if observed!=[expected_output]:
        raise ValueError('guarded Lake output does not bind the final interface execution')
    support.authenticate_artifacts(audited['artifacts'],audit_dir/'ProviderInterfaceAudit.olean')
    if interface.check_logs(audit_dir,audited)!=audited['axioms']:
        raise ValueError('interface axiom output differs')
    if not support.EXPECTED.issubset(complete['axioms']):
        raise ValueError('complete adapter axiom audit missing')
    for name in support.EXPECTED:
        if complete['axioms'][name]!=audited['axioms'][name]:
            raise ValueError('separate interface and adapter axiom outputs disagree')

    # Capture may proceed only into a fresh directory. A partial export is
    # preserved on failure and must not be mistaken for the final manifest.
    args.out.mkdir(parents=True,exist_ok=False)
    interface.save(args.out/'CAPTURE-AUTHENTICATION.json',dict(command=auth_command,
        stdout=authenticated.stdout,stderr=authenticated.stderr,exit_code=authenticated.returncode,
        owned_receipts_sha256=binding['owned_receipts_sha256']))
    for name in ['PLAN.json','RESULT.json','NAMESPACE-RESOLUTION.json']:
        copy(args.state/name,args.out/name)
    for name in ['RECEIPT.json','stdout','stderr']:
        copy(args.lake_output/name,args.out/'lake'/name)
    for name in ['INVOCATION.json','RESULT.json','source.lean','stdout','stderr']:
        copy(audit_dir/name,args.out/'interface'/name)
    execution_modes=collections.Counter();owned=[]
    for index,selected in enumerate(plan['modules']):
        stem=f'{index:04d}';path=args.state/(stem+'.json')
        receipt=json.loads(path.read_text())
        if (receipt['exit_code']!=0 or receipt['module']!=selected['module']
                or receipt['kind']!=selected['kind']
                or receipt['source_sha256']!=selected['sha256']):
            raise ValueError('owned module receipt differs')
        relative=support.relative(receipt['module'])
        target=args.state/'.lake/build/lib/lean'/relative.with_suffix('.olean')
        support.authenticate_artifacts(receipt['artifacts'],target)
        copy(path,args.out/'owned'/(stem+'.json'))
        copy(args.state/'source'/relative,args.out/'compiled-source'/relative,selected['sha256'])
        mode=receipt['execution'];execution_modes[mode]+=1
        if mode=='FRESH_SOURCE_COMPILE':
            if support.read_audit_logs(args.state,index,receipt)!=receipt['axioms']:
                raise ValueError('owned compiled axiom metadata differs')
            for suffix in ['stdout','stderr']:
                copy(args.state/(stem+'.'+suffix),args.out/'owned'/(stem+'.'+suffix),
                     receipt[suffix+'_sha256'])
        elif mode!='AUTHENTICATED_REUSE':
            raise ValueError('unknown owned execution mode')
        owned.append(dict(index=index,module=receipt['module'],execution=mode,
                          receipt_sha256=support.sha(path)))

    previous_path=support.PREVIOUS/'evidence/MATHLIB-SOURCE-EXECUTION.json'
    previous_sha='75c4ac16fb140e4a5b4e07f01f4dd6c3833b366be6cd1f812a3c608c458edda7'
    if support.sha(previous_path)!=previous_sha:
        raise ValueError('published previous external archive differs')
    previous={row['receipt']['module']:row['receipt']
              for row in json.loads(previous_path.read_text())['compiled_modules']}
    external=[];previous_reuse=0
    for index,row in enumerate(complete['external_execution']['modules']):
        path=args.external_state/f'{index:04d}.json'
        if support.sha(path)!=row['receipt_sha256']:
            raise ValueError('external execution receipt changed')
        receipt=json.loads(path.read_text());outputs={}
        if receipt['module']!=row['module'] or receipt['exit_code']!=0:
            raise ValueError('external receipt selection differs')
        for suffix in ['stdout','stderr']:
            log=args.external_state/f'{index:04d}.{suffix}'
            if support.sha(log)!=receipt[suffix+'_sha256']:
                raise ValueError('external compiler log changed')
            outputs[suffix]=log.read_text()
        mode='FRESH_IN_THIS_SUPPORT_PACKET'
        if receipt['module'] in previous:
            if receipt!=previous[receipt['module']]:
                raise ValueError('earlier external reuse receipt differs')
            previous_reuse+=1;mode='AUTHENTICATED_REUSE_FROM_PUBLISHED_PREVIOUS_PACKET'
        external.append(dict(index=index,execution=mode,receipt=receipt,**outputs))
    if previous_reuse!=len(previous):raise ValueError('published external reuse set incomplete')
    interface.save(args.out/'EXTERNAL-EXECUTION.json',dict(
        previous_archive_sha256=previous_sha,authenticated_previous_reuse=previous_reuse,
        fresh_in_support_packet=len(external)-previous_reuse,modules=external,
        commands_may_use_different_recorded_elaboration_options=True))
    for name in ['build_support_namespace.py','audit_support_namespace.py','capture_final_namespace.py',
                 'namespace_resolution.py','serial_compile.py','lakefile.namespace.lean','lean-toolchain',
                 'materialize_support.py','PROVIDER-SELECTION.json','EXTERNAL-PLAN.json']:
        copy(HERE/name,args.out/'configuration'/name)
    for name in ['SOURCE-SELECTION.json','BASELINE-SOURCE-SELECTION.json','lakefile.lean',
                 'lean-toolchain','Accepted1613.lean','AstraUnified.lean','AstraSupportUnified.lean']:
        copy(args.source_root/name,args.out/'materialized-package'/name)
    interface.save(args.out/'CAPTURE.json',dict(source_readback=source_readback,
        status='COMPLETE_SELECTED_SUPPORT_ADAPTER_AND_INTERFACE_EVIDENCE',
        runner_sha256=support.sha(Path(__file__)),owned=owned,
        owned_receipt_execution_modes=dict(execution_modes),
        final_lake_guard_sha256=support.sha(args.lake_output/'RECEIPT.json'),
        full1613_aggregate_freshly_compiled=False,physical_representative_claimed=False,
        native_code_universally_verified=False,binaries_included=False,
        remote_publication_verified=False))
    files=[dict(path=str(path.relative_to(args.out)),bytes=path.stat().st_size,
                sha256=support.sha(path)) for path in sorted(args.out.rglob('*')) if path.is_file()]
    interface.save(args.out/'FILES.json',dict(files=files))
    print(json.dumps(dict(status='FINAL_CAPTURE_COMPLETE',files=len(files),
                          manifest_sha256=support.sha(args.out/'FILES.json'))),flush=True)


if __name__=='__main__':main()
