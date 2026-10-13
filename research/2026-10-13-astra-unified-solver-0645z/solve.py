#!/usr/bin/env python3
"""One entry point for existing exact source search and new COMMON certificates.

Outputs are preserved in an absent directory. Exact source checking is delegated
to the authenticated existing backend; certificate success alone remains UNKNOWN
for source existence. Run under guard.py for a process-group resource guard.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from certificates import MAX_BYTES, Refused, checked, common_packet, digest, fields, generate_singleton, loads, wire

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
ADAPTER=ROOT/'applications/practical-solver/certified_bounds.py'
# Identity of the existing public source/semantic-checker dispatcher, not a
# replacement implementation. Set to its exact incoming source on publication.
ADAPTER_SHA='4d7caca77386cba972e7af3266e583ae0970833811014c9b17eda01732b798fa'


def dispatch(request, out, backend_python=None, rust_binary=None, parity_binary=None, parity_sources=None):
    fields(request, ['schema','task','input'])
    if request['schema'] != 'unified_research_solver_v1':
        raise Refused('unsupported solver schema')
    base=dict(schema='unified_research_solver_result_v1',request_sha256=digest(request),
              universal_native_correctness_claimed=False, general_G3_resolved=False)
    if request['task']=='native_rc1':
        from native_bridge import consume
        result=consume(request['input'],out/'native',parity_binary,parity_sources)
        return {**base,'status':result['status'],'native_result':result,
                'source_feasibility_certified':False}
    if request['task']=='source_search':
        if hashlib.sha256(ADAPTER.read_bytes()).hexdigest()!=ADAPTER_SHA:
            raise Refused('existing source adapter identity changed; review before reuse')
        spec=importlib.util.spec_from_file_location('accepted_bounds',ADAPTER)
        module=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        result=module.consume(request['input'],out/'source',backend_python)
        return {**base,'status':result['status'],'source_result':result,
                'source_feasibility_certified':result['source_feasibility_certified']}
    if request['task']=='generate_singleton':
        result=generate_singleton(request['input'])
    elif request['task']=='check_certificate':
        result=checked(request['input'])
    elif request['task']=='common_menu':
        result=common_packet(request['input'])
        from external_encoding import fixed_queries
        queries=fixed_queries(request['input'])
        (out/'EXTERNAL-QUERIES.json').write_text(json.dumps(queries,indent=2,sort_keys=True)+'\n')
        base['fixed_external_queries']=dict(path='EXTERNAL-QUERIES.json',sha256=digest(queries),
                                            actual_source_binding_checked=False)
    else:
        raise Refused('unknown solver task')
    certs=([result['certificate']] if result.get('status')=='GENERATED_AND_CHECKED' else
               [request['input']] if request['task']=='check_certificate' else
               [row['certificate'] for row in request['input']['pairs']]
               if request['task']=='common_menu' else [])
    if certs:
        from emit_lean import render
        emitted=[]
        seen=set()
        for cert in certs:
            ident=digest(cert)
            if ident in seen:
                continue
            seen.add(ident)
            source=render(cert)
            name=f'Certificate_{ident}.lean'
            (out/name).write_text(source)
            emitted.append(dict(path=name,sha256=hashlib.sha256(source.encode()).hexdigest(),
                                certificate_sha256=ident, compiled=False))
        base['Lean_certificate_sources']=emitted
    if rust_binary:
        native=[]
        binary=Path(rust_binary).resolve()
        for i, cert in enumerate(certs):
            submitted=wire(cert)
            (out/f'certificate-{i}.wire').write_text(submitted)
            r=subprocess.run([str(binary)],input=submitted,text=True,capture_output=True,timeout=5)
            (out/f'native-{i}.stdout').write_text(r.stdout)
            (out/f'native-{i}.stderr').write_text(r.stderr)
            expected=f"CHECKED_RATIONAL_CERTIFICATE support_cap={cert['level']-1} source_existence=false\n"
            native.append(dict(exit_code=r.returncode,stdout=r.stdout,
                               wire_sha256=hashlib.sha256(submitted.encode()).hexdigest(),
                               agree=r.returncode==0 and r.stdout==expected))
        base['native']=dict(binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),checks=native)
        if not all(r['agree'] for r in native):
            return {**base,'status':'UNKNOWN','reason':'Python/Rust certificate disagreement','certificate_result':result}
    return {**base,'status':result['status'],'certificate_result':result,'source_feasibility_certified':False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--request',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--backend-python')
    p.add_argument('--rust-binary')
    p.add_argument('--parity-binary')
    p.add_argument('--parity-sources',type=Path)
    a=p.parse_args()
    a.output.mkdir(parents=True,exist_ok=False)
    try:
        with a.request.open('rb') as incoming:
            raw=incoming.read(MAX_BYTES+1)
        (a.output/'REQUEST.json').write_bytes(raw)
        request=loads(raw)
        result=dispatch(request,a.output,a.backend_python,a.rust_binary,a.parity_binary,a.parity_sources)
    except subprocess.TimeoutExpired:
        result=dict(schema='unified_research_solver_result_v1',status='UNKNOWN',
                    reason='native certificate checker time limit',source_feasibility_certified=False)
    except (Refused,ValueError,TypeError,KeyError,OSError) as error:
        result=dict(schema='unified_research_solver_result_v1',status='REFUSED_REQUEST',
                    reason=str(error),source_feasibility_certified=False)
    (a.output/'RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['status','source_feasibility_certified'] if k in result}))
    return 2 if result['status']=='UNKNOWN' else 1 if result['status']=='REFUSED_REQUEST' else 0


if __name__=='__main__':
    raise SystemExit(main())
