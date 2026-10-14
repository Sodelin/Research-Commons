#!/usr/bin/env python3
"""Only controls unreached by v1; genuine source backend, labelled faults."""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
RUNTIME_SHA = '07c9e49cd05eea2ac9fe590a0f3b01c922da08deefc55f1c5ca01da4711e7f4b'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--backend-python', required=True)
    args = parser.parse_args()
    out = args.output.absolute()  # The runtime also resolves its output absolutely.
    out.mkdir(parents=True, exist_ok=False)
    raw = (HERE / 'runtime.py').read_bytes()
    assert sha(raw) == RUNTIME_SHA
    tree = ast.parse(raw)
    pins = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == 'PINS')
    assert all(sha((ROOT / path).read_bytes()) == pin for path, pin in pins.items())
    submitted = (BASE / 'examples/finite-witness.json').read_bytes()
    assert sha(submitted) == '554d649258730ddfb7f016437bbe04d5f3d86e944676e245ed698d8157c0aca1'
    save(out / 'EXECUTED-SOURCES.json', dict(runtime_sha256=RUNTIME_SHA,
         test_sha256=sha(Path(__file__).read_bytes()), provider_pins=pins,
         request_sha256=sha(submitted), started_utc=datetime.now(timezone.utc).isoformat(),
         changes_since_v1='Only test output comparison made absolute; guard CPU30 matches unchanged backend child contract.',
         earlier_eight_groups_repeated=False))
    spec = importlib.util.spec_from_file_location('astra_runtime_remaining', HERE / 'runtime.py')
    runtime = importlib.util.module_from_spec(spec); spec.loader.exec_module(runtime)
    original_save = runtime.save
    fault_out = out / 'genuine-source-parent-persistence-fault'
    injected = []
    def injected_save(path, value):
        if path == fault_out / 'RESULT.json':
            injected.append(True)
            raise OSError('labelled test injection: final parent persistence failure')
        return original_save(path, value)
    cases = []
    try:
        runtime.save = injected_save
        result = runtime.run(submitted, fault_out, backend_python=args.backend_python)
        runtime.save = original_save
        save(out / 'genuine-source-parent-persistence-fault.returned.json', result)
        child = result['delegate']['result']
        assert child == json.loads((fault_out / 'delegate/RESULT.json').read_bytes())
        assert child['status'] == 'CERTIFIED_SOURCE_WITNESS' and child['source_feasibility_certified']
        inner = child['source_result']
        assert inner['solver_called'] and inner['checker_called']
        assert inner['semantic_check']['status'] == 'PASS_SOURCE_AND_CERTIFICATE_RECOMPUTATION'
        assert inner['scope'] == 'One actual strict original source and one physical assignment fit every supplied row; exact software recomputation, no Lean claim.'
        assert injected == [True] and not (fault_out / 'RESULT.json').exists()
        assert result['status'] == 'UNKNOWN' and result['source_feasibility_certified'] is False
        assert result['delegate']['returned'] and 'persistence_error' in result
        cases.append(dict(name='genuine-source-and-parent-persistence-regression', passed=True,
                     actual_source_backend=True, semantic_checker_pass=True, parent_status='UNKNOWN',
                     parent_certified=False, child_certified=True, original_child_scope=inner['scope'],
                     injection='Only final parent RESULT.json write failed, exactly once.'))
        solver = runtime.load('solve', {})
        original_dispatch = solver.dispatch
        def timeout_dispatch(*unused, **options):
            raise subprocess.TimeoutExpired(['labelled-test-injection-no-process'], 1)
        solver.dispatch = timeout_dispatch
        try:
            result = runtime.run(submitted, out / 'labelled-timeout')
        finally:
            solver.dispatch = original_dispatch
        save(out / 'labelled-timeout.returned.json', result)
        assert result['status'] == 'UNKNOWN' and not result['source_feasibility_certified']
        assert result['delegate']['invoked'] and not result['delegate']['returned']
        cases.append(dict(name='labelled-runtime-timeout', passed=True,
                     actual_subprocess_created_for_timeout_case=False, request_preserved=result['request_preserved']))
    except Exception as error:
        save(out / 'FAILED.json', dict(cases=cases, error=repr(error), traceback=traceback.format_exc()))
        raise
    finally:
        runtime.save = original_save
        save(out / 'CONTROL-PROGRESS.json', dict(cases=cases))
    assert sha((HERE / 'runtime.py').read_bytes()) == RUNTIME_SHA
    assert all(sha((ROOT / path).read_bytes()) == pin for path, pin in pins.items())
    save(out / 'TEST-RESULT.json', dict(status='PASS', cases=cases,
         runtime_sha256=RUNTIME_SHA, native_invocations=0, compiler_invocations=0,
         historical_replay_used=False, finished_utc=datetime.now(timezone.utc).isoformat()))
    print(json.dumps(dict(status='PASS', cases=len(cases), genuine_source_backend=True)))


if __name__ == '__main__':
    main()
