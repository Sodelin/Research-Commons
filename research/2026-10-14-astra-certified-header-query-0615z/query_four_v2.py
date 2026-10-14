#!/usr/bin/env python3
"""Unexecuted fixed four-header query proposal. Never compiles a Lean module."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

ROOT = Path('/workspace/Research-Commons')
HERE = Path(__file__).resolve().parent
OUT = Path('/workspace/scratch/astra-certified-header-query-0615-v2')
INPUTS_SHA = '0188968f24d51edf55cb3f9335e7c2a16bdd4148d63a007bf78a0d966ce2f7e0'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def pause():
    for directory in [HERE, ROOT/'research/2026-10-13-astra-positive-support-adapter-0830z']:
        if (directory/'PAUSE-BUILDS').exists():
            raise RuntimeError('PAUSE-BUILDS refuses the next source query')


def main():
    pause()
    config = json.loads((HERE/'RUN-CONFIG-v2.json').read_text())
    assert config['runner_sha256'] == sha(__file__)
    assert sha(HERE/'INPUTS.json') == INPUTS_SHA == config['inputs_sha256']
    assert sha(HERE/'evidence/INIT-MULTIPLICITY-OBSERVATION.json') == 'ce09367d4ca53f945cde7a887f355f232d7d640da032a8c4d733ed4607f683a9'
    assert config['guard_sha256'] == GUARD_SHA == sha(config['guard_command'][2])
    parent = (Path('/proc')/str(os.getppid())/'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
    assert parent == config['guard_command'], 'requires the exact configured frozen outer guard'
    assert Path.cwd() == ROOT
    for name, limit in [('RLIMIT_AS', 6*1024**3), ('RLIMIT_CPU', 120), ('RLIMIT_FSIZE',64*1024**2)]:
        assert resource.getrlimit(getattr(resource,name)) == (limit,limit), name
    assert not OUT.exists() and not OUT.is_symlink()
    inputs = json.loads((HERE/'INPUTS.json').read_text())
    assert inputs['query_count'] == len(inputs['new_queries']) == 4
    assert len(inputs['reused_query_source_bindings']) == 1641
    for path, expected in inputs['pinned_inputs'].items():
        assert sha(ROOT/path) == expected, path
    assert sha(inputs['compiler']['path']) == inputs['compiler']['sha256']
    materialized = Path(inputs['new_source_root'])
    assert sha(materialized/'MATERIALIZATION.json') == inputs['materialization_sha256']
    receipt = json.loads((materialized/'MATERIALIZATION.json').read_text())
    selected = {r['module']:r for r in receipt['sources']}
    assert len(selected) == 1644
    reuse = []
    for row in inputs['reused_query_source_bindings']:
        assert selected[row['module']]['sha256'] == row['source_sha256'] == sha(row['new_source'])
        assert sha(ROOT/row['historical_request']) == row['request_sha256']
        assert sha(ROOT/row['historical_receipt']) == row['receipt_sha256']
        prior = json.loads((ROOT/row['historical_receipt']).read_text())
        assert prior['request_sha256'] == row['request_sha256'] and prior['exit_code'] == 0 and prior['error'] is None
        reuse.append(row)
    # Every selected owned Mathlib body retains the previous complete-upstream
    # namespace source route. This is source equivalence, never object reuse.
    routes = []
    for name, row in selected.items():
        if name.startswith('Mathlib.'):
            upstream = Path('/workspace/scratch/astra-mathlib-0645')/row['destination']
            assert sha(upstream) == row['sha256'] == sha(materialized/row['destination'])
            routes.append(dict(module=name, upstream=str(upstream), source_sha256=row['sha256']))
    assert len(routes) == 11
    pause()
    OUT.mkdir()
    save(OUT/'INVOCATION.json',dict(started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
         runner_sha256=sha(__file__),inputs_sha256=INPUTS_SHA,run_config_sha256=sha(HERE/'RUN-CONFIG-v2.json'),
         parent_guard_command=parent,compiler_invocations_for_elaboration=0,planned_header_queries=4))
    save(OUT/'REUSED-SOURCE-QUERY-BINDINGS.json',dict(status='PRIOR_QUERY_SOURCE_BYTES_REBOUND_NOT_REQUERIED',sources=reuse,objects_authenticated=False))
    save(OUT/'NAMESPACE-SOURCE-ROUTES.json',dict(routes=routes,objects_authenticated=False))
    results=[]
    try:
        for index, row in enumerate(inputs['new_queries']):
            pause()
            assert sha(row['source']) == row['source_sha256']
            for dep in row['expected_dependencies']:
                assert sha(dep['path']) == dep['sha256'], dep['path']
            directory=OUT/f'{index:04d}'
            directory.mkdir()
            with (directory/'source.lean').open('xb') as stream:stream.write(Path(row['source']).read_bytes())
            save(directory/'REQUEST.json',row)
            started=time.monotonic();code=None;error=None
            try:
                with (directory/'stdout.log').open('xb') as stdout, (directory/'stderr.log').open('xb') as stderr:
                    child=subprocess.run(row['command'],cwd=row['cwd'],env=row['environment'],stdout=stdout,stderr=stderr,timeout=10,check=False)
                    code=child.returncode
            except BaseException as caught:
                error=dict(type=type(caught).__name__,message=str(caught))
                raise
            finally:
                record=dict(index=index,module=row['module'],request_sha256=sha(directory/'REQUEST.json'),
                    source_sha256_before=row['source_sha256'],source_sha256_after=sha(row['source']),
                    exit_code=code,error=error,elapsed_seconds=time.monotonic()-started,
                    outputs={name:dict(bytes=(directory/name).stat().st_size,sha256=sha(directory/name)) for name in ['stdout.log','stderr.log'] if (directory/name).exists()})
                save(directory/'RECEIPT.json',record)
                results.append(dict(index=index,module=row['module'],receipt_sha256=sha(directory/'RECEIPT.json')))
            assert code == 0 and record['source_sha256_after'] == row['source_sha256']
            assert set(record['outputs']) == {'stdout.log','stderr.log'}
            assert all(r['bytes'] <= 4*1024**2 for r in record['outputs'].values())
            actual=(directory/'stdout.log').read_text().splitlines()
            assert all(line and Path(line).is_absolute() for line in actual)
            expected={d['path'] for d in row['expected_dependencies']}
            init=row['expected_dependencies'][0]
            assert init['module'] == 'Init'
            # The pinned same-version 1710-query corpus emits Init exactly
            # twice and every other dependency once. Preserve every line.
            assert actual.count(init['path']) == 2
            assert len(actual) == len(expected) + 1
            assert all(actual.count(path) == (2 if path == init['path'] else 1) for path in expected)
            assert set(actual) == expected, dict(actual=actual,expected=sorted(expected))
            deps={d['path']:d for d in row['expected_dependencies']}
            for path in actual:assert sha(path)==deps[path]['sha256']
            save(directory/'IMPORTS.json',dict(actual_order=actual,literal_imports=row['literal_imports'],dependencies=[deps[path] for path in actual],source_resolution_only=True))
        save(OUT/'RESULT.json',dict(status='FOUR_SOURCE_HEADER_QUERIES_PASS_NOT_ELABORATION',queries=results,
             prior_library_sources_rebound=1641,prior_queries_repeated=0,source_compilations=0,objects_authenticated=0,
             current_plan_mutated=False,lake_executed=False,types_or_axioms_audited=False))
        print(json.dumps(dict(status='FOUR_SOURCE_HEADER_QUERIES_PASS_NOT_ELABORATION',queries=4,prior_library_sources_rebound=1641)))
    except BaseException as caught:
        save(OUT/'FAILED.json',dict(status='FAILED_PARTIAL_PRESERVED_NO_RETRY',error_type=type(caught).__name__,error=str(caught),query_receipts=results))
        raise


if __name__ == '__main__':
    main()
