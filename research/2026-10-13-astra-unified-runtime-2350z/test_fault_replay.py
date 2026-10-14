#!/usr/bin/env python3
"""Labelled fault controls with authenticated historical child-result replay.

Does not rerun a source backend, native binary, compiler or successful v1 corpus.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
HISTORY = ROOT / 'research/2026-10-13-astra-native-acquisition-0815z/evidence/unified-cases/finite-witness'
RUNTIME_SHA = '07c9e49cd05eea2ac9fe590a0f3b01c922da08deefc55f1c5ca01da4711e7f4b'
PINS = {
    'REQUEST.json': '554d649258730ddfb7f016437bbe04d5f3d86e944676e245ed698d8157c0aca1',
    'RESULT.json': 'a7b9b942fb643a98c6a3b7e2792c794f91460a9b725ed92eb1b07505d008aff5',
    'source/checker.execution.json': 'e496427efeff636bcb698f1257cec19e358cd0e6228e052ad09c274096c3a68c',
    'source/checker.stdout': '36719393d75f3e1ce6294b6ea994a8cce278233b786d69de3a4cf884703fe2c3',
    'source/solver.execution.json': '4d8cb72ca6331cab3b05d7f45d5f9d5826288612e02da7f4cfaf7d94fddf0eb3',
    'source/backend/RESULT.json': '2535253f20f17045309bf2a829ab6f1ed42782062ed941703a8fb5b57d9a207f',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.absolute()  # Compare like absolute paths in the injected save.
    out.mkdir(parents=True, exist_ok=False)
    assert sha((HERE / 'runtime.py').read_bytes()) == RUNTIME_SHA
    for name, expected in PINS.items():
        raw = (HISTORY / name).read_bytes()
        assert sha(raw) == expected
        target = out / 'historical-evidence' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(raw)
    request_raw = (HISTORY / 'REQUEST.json').read_bytes()
    request = json.loads(request_raw)
    historical = json.loads((HISTORY / 'RESULT.json').read_bytes())
    assert historical['status'] == 'CERTIFIED_SOURCE_WITNESS' and historical['source_feasibility_certified']
    for name in ['solver', 'checker']:
        receipt = json.loads((HISTORY / ('source/' + name + '.execution.json')).read_bytes())
        assert receipt['invoked'] and receipt['returncode'] == 0 and not receipt['timeout']
    assert json.loads((HISTORY / 'source/checker.stdout').read_bytes())['status'] == 'PASS_SOURCE_AND_CERTIFICATE_RECOMPUTATION'
    save(out / 'EXECUTED-SOURCES.json', dict(runtime_sha256=RUNTIME_SHA,
         test_sha256=sha(Path(__file__).read_bytes()), historical_evidence_pins=PINS,
         historical_root=str(HISTORY.relative_to(ROOT)), source_backend_run=False,
         native_invocations=0, compiler_invocations=0,
         testing_scope='Parent handling of authenticated historical child replay and labelled failures; not a fresh source witness.'))
    spec = importlib.util.spec_from_file_location('astra_runtime_fault_control', HERE / 'runtime.py')
    runtime = importlib.util.module_from_spec(spec); spec.loader.exec_module(runtime)
    solver = runtime.load('solve', {})
    original_dispatch, original_save, original_emit = solver.dispatch, runtime.save, runtime.emit
    cases = []

    def historical_dispatch(submitted, *unused, **options):
        assert submitted == request
        return copy.deepcopy(historical)

    try:
        solver.dispatch = historical_dispatch
        normal = runtime.run(request_raw, out / 'labelled-historical-replay')
        save(out / 'labelled-historical-replay.returned.json', normal)
        assert normal['status'] == 'CERTIFIED_SOURCE_WITNESS' and normal['source_feasibility_certified']
        assert normal['delegate']['result'] == historical
        cases.append(dict(name='historical-child-replay-scope', passed=True, actual_backend_execution=False,
                          scope=historical['source_result']['scope']))

        fault_out = out / 'labelled-persistence-fault'
        injection_count = []
        def injected_save(path, value):
            if path == fault_out / 'RESULT.json':
                injection_count.append(True)
                raise OSError('labelled test injection: final parent persistence failure')
            return original_save(path, value)
        runtime.save = injected_save
        failed = runtime.run(request_raw, fault_out)
        save(out / 'labelled-persistence-fault.returned.json', failed)
        runtime.save = original_save
        assert injection_count == [True] and not (fault_out / 'RESULT.json').exists()
        assert failed['status'] == 'UNKNOWN' and failed['source_feasibility_certified'] is False
        assert failed['delegate']['returned'] and failed['delegate']['result'] == historical
        assert json.loads((fault_out / 'delegate/RESULT.json').read_bytes()) == historical
        assert failed['delegate']['result']['source_feasibility_certified'] is True
        cases.append(dict(name='parent-persistence-flag-regression', passed=True,
                          parent_status='UNKNOWN', parent_certified=False, historical_child_certified=True,
                          actual_backend_execution=False, injection_count=1))

        def timeout_dispatch(*unused, **options):
            raise subprocess.TimeoutExpired(['labelled-injection-no-process'], 1)
        solver.dispatch = timeout_dispatch
        timed = runtime.run(request_raw, out / 'labelled-timeout')
        save(out / 'labelled-timeout.returned.json', timed)
        assert timed['status'] == 'UNKNOWN' and not timed['source_feasibility_certified']
        assert timed['delegate']['invoked'] and not timed['delegate']['returned']
        cases.append(dict(name='labelled-timeout', passed=True, actual_subprocess_created=False))

        solver.dispatch = original_dispatch
        menu = json.loads((ROOT / 'research/2026-10-13-astra-unified-solver-0645z/examples/correlated-menu.json').read_bytes())
        certificate = menu['input']['pairs'][0]['certificate']
        submitted = dict(schema='unified_research_solver_v1', task='check_certificate', input=certificate)
        def emission_failure(*unused, **options):
            raise OSError('labelled test injection: optional support emission unavailable')
        runtime.emit = emission_failure
        emitted = runtime.run(json.dumps(submitted).encode(), out / 'labelled-emission-fault', emit_support=True)
        save(out / 'labelled-emission-fault.returned.json', emitted)
        assert emitted['status'] == 'CHECKED_RATIONAL_CERTIFICATE' and not emitted['source_feasibility_certified']
        assert emitted['support_emission']['status'] == 'UNKNOWN' and not emitted['support_emission']['compiled']
        cases.append(dict(name='labelled-optional-emission-failure', passed=True,
                          genuine_certificate_delegate=True, parent_certificate_status_retained=True))
    finally:
        solver.dispatch, runtime.save, runtime.emit = original_dispatch, original_save, original_emit
        save(out / 'CONTROL-PROGRESS.json', dict(cases=cases))
    assert sha((HERE / 'runtime.py').read_bytes()) == RUNTIME_SHA
    save(out / 'TEST-RESULT.json', dict(status='PASS', cases=cases, source_backend_run=False,
          native_invocations=0, compiler_invocations=0,
          note='All injected/reused cases are labelled; v1 fresh source backend remains unavailable under its inherited CPU limit.'))
    print(json.dumps(dict(status='PASS', cases=len(cases), source_backend_run=False)))


if __name__ == '__main__':
    main()
