#!/usr/bin/env python3
"""Check the explicit provider/adapter interface after complete authentication.

Run serially under the packet's guarded Lake target. This is a separate Lean
module; it never changes the accepted provider or adapter source bodies.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

import build_support as support
from serial_compile import compile_one,toolchain_inputs

HERE=Path(__file__).resolve().parent
LOADED_SHA=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SOURCE=HERE/'audits/ProviderInterfaceAudit.lean'
LAKE_SHA='60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3'
ARGUMENTS=['source_root','external_state','state','mathlib_root','lean_bin']


def save(path,value):
    with path.open('x') as handle:
        json.dump(value,handle,indent=2);handle.write('\n')


def ledger_digest(state,plan):
    rows=[dict(index=index,sha256=support.sha(state/f'{index:04d}.json'))
          for index in range(len(plan['modules']))]
    return hashlib.sha256(json.dumps(rows,sort_keys=True).encode()).hexdigest()


def lake_command(args):
    return ['env','MIMALLOC_ARENA_RESERVE=16384','LEAN_NUM_THREADS=1',
            'LEAN_STACK_SIZE_KB=8192','LEAN_IMPORT_WORKERS=1',
            'ASTRA_SUPPORT_SOURCES='+str(args.source_root),
            'ASTRA_SUPPORT_EXTERNAL_STATE='+str(args.external_state),
            'ASTRA_SUPPORT_STATE='+str(args.state),
            'ASTRA_MATHLIB_ROOT='+str(args.mathlib_root),
            'ASTRA_LEAN_BIN='+str(args.lean_bin),
            str(args.lean_bin/'lake'),'build','adapter']


def authenticate_complete(args):
    if not (args.state/'RESULT.json').is_file():
        raise ValueError('complete provider/adapter receipt is required before interface audit')
    command=[sys.executable,'-B',str(HERE/'build_support.py')]
    for name in ARGUMENTS:
        command.extend(['--'+name.replace('_','-'),str(getattr(args,name))])
    command.append('--authenticate-only')
    completed=subprocess.run(command,cwd=HERE,capture_output=True,text=True)
    if completed.returncode:
        sys.stdout.write(completed.stdout);sys.stderr.write(completed.stderr)
        raise SystemExit('complete source/object/log authentication failed')
    return command,completed


def output_binding(args,binding,receipt_path):
    return dict(status='FINAL_INTERFACE_EXECUTION_BINDING',
                receipt_sha256=support.sha(receipt_path),binding=binding,
                expected_lake_command=lake_command(args),expected_lake_cwd=str(HERE))


def check_logs(directory,receipt):
    texts=[]
    for suffix in ['stdout','stderr']:
        path=directory/suffix
        if support.sha(path)!=receipt[suffix+'_sha256']:
            raise ValueError('interface compiler log changed: '+suffix)
        texts.append(path.read_text())
    text='\n'.join(texts)
    if "declaration uses 'sorry'" in text:
        raise ValueError('interface placeholder warning rejected')
    parsed=support.audit(text)
    if not support.EXPECTED.issubset(parsed):
        raise ValueError('interface audit is missing a required theorem')
    return parsed


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ['source-root','external-state','state','mathlib-root','lean-bin']:
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args()
    for name in ARGUMENTS:
        setattr(args,name,getattr(args,name).resolve())
    result_path=args.state/'RESULT.json'

    # This mode has a zero fresh-module budget. A missing or altered receipt
    # fails before this script can launch its separate interface compiler.
    auth_command,authenticated=authenticate_complete(args)
    complete=json.loads(result_path.read_text())
    if complete['status']!='EXACT_ACCEPTED_PROVIDER_AND_SUPPORT_ADAPTER_VERIFIED':
        raise ValueError('unexpected completion receipt')
    plan=json.loads((args.state/'PLAN.json').read_text())
    if plan['modules']!=complete['modules']:
        raise ValueError('completed owned plan differs')
    if support.sha(args.lean_bin/'lake')!=LAKE_SHA:
        raise ValueError('selected Lake executable changed')

    _,_,env=support.setup(args.mathlib_root,args.lean_bin)
    build=args.state/'.lake/build/lib/lean'
    env['LEAN_PATH']=str(build)+os.pathsep+env['LEAN_PATH']
    inputs=toolchain_inputs(args.lean_bin)
    for row in complete['external_execution']['modules']:
        inputs.update(row['artifacts'])
    for index in range(len(plan['modules'])):
        row=json.loads((args.state/f'{index:04d}.json').read_text())
        inputs.update(row['artifacts'])
    directory=args.state/'interface-audit'
    target=directory/'ProviderInterfaceAudit.olean'
    command=[str(args.lean_bin/'lean'),'-j','1','-s','8192',
             '-R',str(HERE),'-o',str(target),str(SOURCE)]
    binding=dict(compiler_sha256=support.LEAN_SHA,mathlib_pin=support.PIN,
                 source_sha256=support.sha(SOURCE),command=command,
                 owned_plan_sha256=support.sha(args.state/'PLAN.json'),
                 owned_result_sha256=support.sha(result_path),
                 external_plan_sha256=support.sha(args.external_state/'PLAN.json'),
                 owned_receipts_sha256=ledger_digest(args.state,plan),
                 lakefile_sha256=support.sha(HERE/'lakefile.lean'),lake_sha256=LAKE_SHA,
                 arguments={name:str(getattr(args,name)) for name in ARGUMENTS},
                 runner_sha256=LOADED_SHA,
                 authenticator_sha256=support.sha(HERE/'build_support.py'))
    receipt_path=directory/'RESULT.json'
    if directory.exists():
        if not receipt_path.is_file():
            raise ValueError('preserve and repair incomplete interface invocation explicitly')
        receipt=json.loads(receipt_path.read_text())
        if receipt['exit_code']!=0 or receipt['binding']!=binding:
            raise ValueError('preserve and repair failed/changed interface invocation explicitly')
        support.authenticate_artifacts(receipt['artifacts'],target)
        if support.sha(directory/'source.lean')!=binding['source_sha256']:
            raise ValueError('saved interface source differs')
        if json.loads((directory/'INVOCATION.json').read_text())['binding']!=binding:
            raise ValueError('saved interface invocation binding differs')
        if check_logs(directory,receipt)!=receipt['axioms']:
            raise ValueError('saved interface axiom metadata differs')
        print(json.dumps(dict(status='SELECTED_INTERFACE_AUTHENTICATED_REUSE',
                              receipt_sha256=support.sha(receipt_path))),flush=True)
        print(json.dumps(output_binding(args,binding,receipt_path)),flush=True)
        return

    directory.mkdir()
    (directory/'source.lean').write_bytes(SOURCE.read_bytes())
    save(directory/'INVOCATION.json',dict(binding=binding,
        authentication_command=auth_command,
        authentication_stdout=authenticated.stdout,
        authentication_stderr=authenticated.stderr,
        execution='FRESH_INTERFACE_SOURCE_COMPILE'))
    code,resource_control=compile_one(command,cwd=HERE,env=env,
        stdout=directory/'stdout',stderr=directory/'stderr',input_files=inputs,
        target=target,index=len(plan['modules']),module='audits.ProviderInterfaceAudit')
    receipt=dict(binding=binding,execution='FRESH_INTERFACE_SOURCE_COMPILE',
                 compiler_exit_code=code,exit_code=code,
                 artifacts=support.artifacts(target),
                 stdout_sha256=support.sha(directory/'stdout'),
                 stderr_sha256=support.sha(directory/'stderr'),
                 resource_control=resource_control)
    if not code:
        try:
            support.authenticate_artifacts(receipt['artifacts'],target)
            receipt['axioms']=check_logs(directory,receipt)
            receipt['status']='EXACT_SELECTED_INTERFACE_CHECKED'
        except ValueError as error:
            receipt.update(exit_code=2,audit_failure=str(error))
    save(receipt_path,receipt)
    print(json.dumps(dict(status=receipt.get('status','INTERFACE_AUDIT_FAILED'),
                          compiler_exit_code=code,exit_code=receipt['exit_code'],
                          source_sha256=binding['source_sha256'])),flush=True)
    if not receipt['exit_code']:
        print(json.dumps(output_binding(args,binding,receipt_path)),flush=True)
    raise SystemExit(receipt['exit_code'])


if __name__=='__main__':main()
