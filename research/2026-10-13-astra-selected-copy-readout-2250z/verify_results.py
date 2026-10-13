#!/usr/bin/env python3
"""Authenticate the final bounded runs and every row's original identities.

Read-only except an exclusive verification report. No native execution, tests,
Lean, Rust, or graph computation occurs here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import selected_readout as subject


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def guard(path, code):
    value=json.loads((path/'RECEIPT.json').read_text())
    require(value['exit_code']==code and value['stop'] is None,'guard outcome differs')
    require(value['runner_sha256']=='f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3',
            'frozen guard identity differs')
    require(value['limits']==dict(cpu_seconds=15,wall_seconds=20,address_space_bytes=256*1024**2,
        file_bytes=16*1024**2,disk_floor=8*1024**3,ram_floor=1024**3,cgroup_stop=4*1024**3),
        'test profile differs')
    for key in ['stdout','stderr']:
        require(value['outputs'][key]==dict(bytes=(path/key).stat().st_size,sha256=sha(path/key)),
                'guard output differs')
    return value


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();c,encoding,bridge=subject.providers()
    tests=subject.HERE/'evidence/contract-tests-v2';cli=subject.HERE/'evidence/dot2200-complete-cli-v2'
    tg,cg=guard(tests,0),guard(cli,2)
    tests_stdout=[json.loads(line) for line in (tests/'stdout').read_text().splitlines()]
    require(tests_stdout[0]['executed_source_pins']=={
        'selected_readout.py':sha(subject.HERE/'selected_readout.py'),
        'test_selected.py':sha(subject.HERE/'test_selected.py')},'executed test source differs')
    require('Ran 10 tests' in (tests/'stderr').read_text() and (tests/'stderr').read_text().rstrip().endswith('OK'),
            'bounded controls did not pass')
    require(tests_stdout[1]['cases']==60,'independent polynomial differential count differs')
    request_path=subject.HERE/'examples/dot2200-selected.json'
    raw=request_path.read_bytes();request=c.loads(raw)
    require((cli/'readout/REQUEST.json').read_bytes()==raw,'actual primary input differs')
    original=subject.HERE/'examples/DOT-COMMON-MENU.json'
    require(sha(original)=='65658e0a779c7b7a3601f64866731890eb5dc8699291e2bd9bb1a5f6c83da13c','original menu bytes differ')
    require(request['menu']==c.loads(original.read_bytes())['input'],'primary does not preserve original menu')
    queries=encoding.fixed_queries(request['menu'])
    require(len(queries['queries'])==48,'primary query selection differs')
    result=json.loads((cli/'readout/RESULT.json').read_text())
    require(result['adapter_sha256']==sha(subject.HERE/'selected_readout.py'),'actual CLI source differs')
    require(result['status']=='UNKNOWN' and result['readout_complete'] is True
        and result['all_supplied_moments_match'] is True,'formal completion differs')
    require(result['original_input_bytes_sha256']==sha(request_path)
        and result['canonical_request_sha256']==c.digest(request)
        and result['fixed_external_queries_sha256']==c.digest(queries),'input/query identities differ')
    require(result['physical_source_decision']=='UNKNOWN' and not result['source_feasibility_certified']
        and not result['native_refinement_proved'] and not result['full_padded_native_table_generated'],
        'unproved physical scope promoted')
    require(len(result['rows'])==48,'partial result')
    ledger=[]
    for i,(query,row) in enumerate(zip(queries['queries'],result['rows'])):
        path=cli/'readout'/f'row-{i:03d}'
        require(row==json.loads((path/'READOUT.json').read_text()),'row artifact differs')
        require(row['row_index']==i and row['transport']['full_padded_row']==query,'fixed padded row changed')
        require(row['same_tuple']==result['same_tuple'],'row-specific source/parameter/PMF tuple')
        require(row['transport']==subject.copy_transport(query,request['source'],c),'copy/subtype transport differs')
        require(row['formal_normalized_moment']==query['normalized_moment']
            and row['formal_mixed_event_probability']==query['required_event_probability']
            and row['matches_supplied_moment'] is True,'exact supplied values differ')
        require(not row['physical_row_equality_proved'],'formal readout promoted to Lean row proof')
        for field,name in [('native_request_sha256','REQUEST.rc1'),('native_response_sha256','RESPONSE.rc1'),
                           ('native_result_sha256','RESULT.json')]:
            require(row[field]==sha(path/name),'native artifact differs')
        native=json.loads((path/'RESULT.json').read_text())
        require(native['status']=='CHECKED_SYMBOLIC_FORWARD_TABLE' and native['certificate_checked'] is True
            and native['runtime']['binary_sha256']==bridge.BINARY_SHA
            and native['runtime']['restored_manifest_sha256']==bridge.MANIFEST_SHA,'native replay binding differs')
        for operation in ['solve','check']:
            receipt=json.loads((path/(operation+'.execution.json')).read_text())
            require(receipt==native[operation+'_execution'] and receipt['exit_code']==0
                and not receipt['timed_out'],'native operation did not pass')
            for channel in ['stdout','stderr']:
                q=path/(operation+'.'+channel)
                require(receipt[channel]==dict(bytes=q.stat().st_size,sha256=sha(q)),'native operation log differs')
        require((path/'check.stdout').read_bytes()==b'RC1 CHECK ACCEPT\n','native checker did not accept')
        require((path/'solve.stdout').read_bytes()==(path/'RESPONSE.rc1').read_bytes(),'native result transport differs')
        require([r['configuration'] for r in row['configurations']]==request['menu']['configurations'],
                'joint configuration input records differ')
        ledger.append(dict(pair=query['directed_pair'],level=query['level'],external_row_sha256=query['row_sha256'],
            certificate_sha256=query['certificate_sha256'],readout_sha256=sha(path/'READOUT.json'),
            native_request_sha256=row['native_request_sha256'],native_response_sha256=row['native_response_sha256'],
            event_probability=row['formal_mixed_event_probability'],normalized_moment=row['formal_normalized_moment']))
    report=dict(schema='selected_native_common_verification_v1',status='AUTHENTICATED_FORMAL_READOUT_EXECUTION',
        verifier_sha256=sha(Path(__file__)),adapter_sha256=sha(subject.HERE/'selected_readout.py'),
        test_source_sha256=sha(subject.HERE/'test_selected.py'),test_guard_sha256=sha(tests/'RECEIPT.json'),
        cli_guard_sha256=sha(cli/'RECEIPT.json'),cli_result_sha256=sha(cli/'readout/RESULT.json'),
        test_count=10,independent_sympy_exact_cases=60,complete_ordered_pairs=16,complete_formal_rows=48,
        actual_native_solve_and_replay_checks=96,fresh_native_compiles=0,
        native_build='authenticated reuse of pinned recovered core',
        guard_cli_child_exit=2,guard_wrapper_exit=1,cli_unknown_is_intentional=True,
        original_menu_raw_sha256=sha(original),same_tuple=result['same_tuple'],row_ledger=ledger,
        new_lean_composition_compiled=False,full_padded_table_contract_executed=False,
        physical_source_decision='UNKNOWN',native_refinement_proved=False,
        finite_tests_establish_universal_correctness=False,
        v1='Preserved derived variant added protected edges; it is not exact original-menu execution.')
    with args.output.open('x') as stream:json.dump(report,stream,indent=2);stream.write('\n')
    print(json.dumps(dict(status=report['status'],rows=48,verification_sha256=sha(args.output))))


if __name__=='__main__':main()
