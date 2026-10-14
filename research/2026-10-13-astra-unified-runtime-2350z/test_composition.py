#!/usr/bin/env python3
"""Bounded new-entry composition controls; no compiler or old corpus runner."""
import argparse
import ast
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import traceback

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
SELECTED = ROOT / 'research/2026-10-13-astra-selected-copy-readout-2250z'
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
    parser.add_argument('--old-checker', type=Path, required=True)
    parser.add_argument('--new-checker', type=Path, required=True)
    parser.add_argument('--parity-binary', type=Path, required=True)
    parser.add_argument('--parity-sources', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    raw = (HERE / 'runtime.py').read_bytes()
    assert sha(raw) == RUNTIME_SHA
    tree = ast.parse(raw)
    pins = next(ast.literal_eval(n.value) for n in tree.body if isinstance(n, ast.Assign)
                and isinstance(n.targets[0], ast.Name) and n.targets[0].id == 'PINS')
    initial = {p: sha((ROOT / p).read_bytes()) for p in pins}
    assert initial == pins
    fixture_paths = [BASE / 'examples/correlated-menu.json', BASE / 'examples/singleton-generator.json',
                     BASE / 'examples/finite-witness.json', BASE / 'examples/native-affine-witness.json',
                     SELECTED / 'examples/dot2200-selected.json']
    inputs = {str(p.relative_to(ROOT)): sha(p.read_bytes()) for p in fixture_paths}
    binaries = {str(p): sha(p.read_bytes()) for p in [args.old_checker, args.new_checker, args.parity_binary]}
    assert binaries[str(args.old_checker)] == '1a508f23613bb527e5605c806fb8215ed6a16adeed4c4147658236790064d805'
    assert binaries[str(args.new_checker)] == '3d7678fac5ba8138b28a08e40c6ca8ac2b3a6e13267350d48480997e53f27ef7'
    assert binaries[str(args.parity_binary)] == '235520d47eaa95873729f2aa60b6f596f41859f1b1807ee58aeb1bd2ab0f876a'
    snapshot = dict(runtime_sha256=RUNTIME_SHA, test_sha256=sha(Path(__file__).read_bytes()),
                    provider_pins=initial, fixture_pins=inputs, executable_pins=binaries,
                    started_utc=datetime.now(timezone.utc).isoformat())
    save(args.output / 'EXECUTED-SOURCES.json', snapshot)
    spec = importlib.util.spec_from_file_location('astra_runtime_under_test', HERE / 'runtime.py')
    runtime = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(runtime)
    cases = []

    def invoke(name, submitted, **options):
        encoded = submitted if isinstance(submitted, bytes) else json.dumps(submitted, indent=2).encode() + b'\n'
        if len(encoded) <= runtime.MAX_BYTES:
            (args.output / (name + '.request.json')).write_bytes(encoded)
        result = runtime.run(encoded, args.output / name, **options)
        save(args.output / (name + '.returned.json'), result)
        return result

    def case(name, action):
        try:
            detail = action()
            row = dict(name=name, passed=True, detail=detail)
        except Exception as error:
            row = dict(name=name, passed=False, error=repr(error), traceback=traceback.format_exc())
            cases.append(row)
            save(args.output / 'FAILED.json', dict(cases=cases))
            raise
        cases.append(row)
        save(args.output / (name + '.control.json'), row)

    menu = json.loads((BASE / 'examples/correlated-menu.json').read_bytes())
    certificate = menu['input']['pairs'][0]['certificate']
    certificate_request = dict(schema='unified_research_solver_v1', task='check_certificate', input=certificate)
    generator = (BASE / 'examples/singleton-generator.json').read_bytes()
    selected_raw = (SELECTED / 'examples/dot2200-selected.json').read_bytes()

    def literal_certificate():
        raw = b' \n' + json.dumps(certificate_request, indent=3).encode() + b' \n'
        request = args.output / 'literal-cli.request.json'; request.write_bytes(raw)
        out = args.output / 'literal-cli'
        command = [sys.executable, '-B', str(HERE / 'runtime.py'), '--request', str(request),
                   '--output', str(out), '--rust-binary', str(args.old_checker), '--emit-support']
        completed = subprocess.run(command, capture_output=True, text=True, timeout=8)
        save(args.output / 'literal-cli.execution.json', dict(command=command, exit_code=completed.returncode,
             stdout=completed.stdout, stderr=completed.stderr))
        result = json.loads((out / 'RESULT.json').read_bytes())
        assert completed.returncode == 0 and result['status'] == 'CHECKED_RATIONAL_CERTIFICATE'
        assert (out / 'REQUEST.json').read_bytes() == raw
        assert result['primary_request_sha256'] == sha(raw)
        assert result['primary_request_sha256'] != result['canonical_request_sha256']
        assert result['delegate']['result']['request_sha256'] == result['canonical_request_sha256']
        assert result['support_emission']['compiled'] is False
        assert result['native_checker']['generation_supported'] is False
        assert result['delegate']['result']['native']['checks'][0]['agree'] is True
        return dict(status=result['status'], raw_bytes_preserved=True, old_checker_observed=True,
                    support_sources=len(result['support_emission']['sources']))
    case('literal-certificate-cli', literal_certificate)

    def generator_profiles():
        new = invoke('new-generator', generator, rust_binary=args.new_checker, native_generation=True)
        assert new['status'] == 'GENERATED_AND_CHECKED'
        assert new['delegate']['result']['native_generation']['agree'] is True
        old = invoke('old-generator-refused-capability', generator, rust_binary=args.old_checker, native_generation=True)
        assert old['status'] == 'UNKNOWN' and old['delegate'] is None
        return dict(new_generation_agrees=True, old_capability_unknown_before_delegate=True)
    case('checker-capabilities', generator_profiles)

    def unknown_executable():
        # Existing test source is deliberately not an approved binary; it must never execute.
        result = invoke('unknown-executable', certificate_request, rust_binary=Path(__file__))
        assert result['status'] == 'UNKNOWN' and result['delegate'] is None
        return dict(executable_invoked=False)
    case('unknown-checker-identity', unknown_executable)

    def transport():
        bad = invoke('duplicate-json', b'{"schema":"x","schema":"y"}')
        assert bad['status'] == 'REFUSED_REQUEST' and bad['request_preserved']
        for name, raw in [('oversize-bytes', b'x' * (runtime.MAX_BYTES + 1)),
                          ('oversize-utf8', '\u00e9' * (runtime.MAX_BYTES // 2 + 1))]:
            result = runtime.run(raw, args.output / name)
            assert result['status'] == 'REFUSED_REQUEST' and not (args.output / name).exists()
            save(args.output / (name + '.returned.json'), result)
        existing = args.output / 'existing'; existing.mkdir(); (existing / 'sentinel').write_bytes(b'preserve')
        result = runtime.run(generator, existing)
        assert result['status'] == 'REFUSED_REQUEST' and list(existing.iterdir()) == [existing / 'sentinel']
        assert (existing / 'sentinel').read_bytes() == b'preserve'
        return dict(duplicate_refused=True, byte_and_utf8_gate_before_directory=True, existing_directory_unchanged=True)
    case('bounded-transport-and-output', transport)

    def unknown_route():
        for name, request in [('unsupported-schema', dict(schema='not_supported')),
                              ('unsupported-task', dict(schema='unified_research_solver_v1', task='not_supported', input={}))]:
            result = invoke(name, request)
            assert result['status'] == 'UNKNOWN' and result['delegate'] is None
        return dict(unsupported_is_unknown=True)
    case('unsupported-routing', unknown_route)

    def selected():
        result = invoke('selected-complete', selected_raw, parity_binary=args.parity_binary,
                        parity_sources=args.parity_sources, emit_support=True)
        child = result['delegate']['result']; output = args.output / 'selected-complete'
        assert result['status'] == 'UNKNOWN' and result['source_feasibility_certified'] is False
        assert child['readout_complete'] and child['all_supplied_moments_match'] and len(child['rows']) == 48
        assert child['physical_source_decision'] == 'UNKNOWN' and not child['physical_source_admission_verified']
        assert not child['full_padded_native_table_generated'] and not child['native_refinement_proved']
        assert (output / 'REQUEST.json').read_bytes() == selected_raw == (output / 'delegate/REQUEST.json').read_bytes()
        assert result['primary_request_sha256'] == child['original_input_bytes_sha256']
        assert result['canonical_request_sha256'] == child['canonical_request_sha256']
        emission = result['support_emission']
        assert len(emission['certificate_references']) == 16 and len(emission['sources']) == 3
        assert emission['compiled'] is False
        for emitted in emission['sources']:
            ident = emitted['manifest']['mathematical_interface']['certificate_sha256']
            assert all(sha((output / emitted['path'] / name).read_bytes()) == data['sha256']
                       for name, data in emitted['manifest']['files'].items())
            assert emitted['path'] == 'support/' + ident
        return dict(readouts=48, original_pair_references=16, unique_support_wrappers=3,
                    physical_source_decision='UNKNOWN', sources_compiled=False)
    case('selected-readout-and-deduplicated-emission', selected)

    def selected_unavailable():
        result = invoke('selected-unavailable', selected_raw)
        assert result['status'] == 'UNKNOWN' and not result['delegate']['result']['readout_complete']
        assert result['delegate']['returned']
        return dict(runtime_unavailable_is_unknown=True)
    case('selected-unavailable', selected_unavailable)

    def native_route():
        result = invoke('native-rc1', (BASE / 'examples/native-affine-witness.json').read_bytes(),
                        parity_binary=args.parity_binary, parity_sources=args.parity_sources)
        child = result['delegate']['result']
        assert child['status'] == 'CERTIFIED_AFFINE_WITNESS' and result['status'] == child['status']
        assert child['native_result']['certificate_checked'] and not result['source_feasibility_certified']
        return dict(original_rc1_contract_preserved=True, physical_source_certified=False)
    case('original-native-rc1-route', native_route)

    def persistence_fault():
        out = args.output / 'source-persistence-fault'
        original_save = runtime.save
        def injected_save(path, value):
            if path == out / 'RESULT.json':
                raise OSError('labelled test injection: final parent persistence failure')
            return original_save(path, value)
        runtime.save = injected_save
        try:
            result = invoke('source-persistence-fault', (BASE / 'examples/finite-witness.json').read_bytes(),
                            backend_python=args.backend_python)
        finally:
            runtime.save = original_save
        child = result['delegate']['result']; original = json.loads((out / 'delegate/RESULT.json').read_bytes())
        assert child == original and child['status'] == 'CERTIFIED_SOURCE_WITNESS'
        inner = child['source_result']
        assert child['source_feasibility_certified'] and inner['solver_called'] and inner['checker_called']
        assert inner['scope'] == 'One actual strict original source and one physical assignment fit every supplied row; exact software recomputation, no Lean claim.'
        assert result['status'] == 'UNKNOWN' and result['source_feasibility_certified'] is False
        assert 'persistence_error' in result and not (out / 'RESULT.json').exists()
        return dict(injection='Only final parent RESULT.json write fails; genuine backend and semantic checker run.',
                    parent_status='UNKNOWN', parent_certified=False, preserved_child_status=child['status'],
                    preserved_child_scope=inner['scope'], genuine_child_execution=True)
    case('parent-persistence-regression-with-real-source-child', persistence_fault)

    def timeout_fault():
        solver = runtime.load('solve', {})
        original_dispatch = solver.dispatch
        def injected_dispatch(*unused, **options):
            raise subprocess.TimeoutExpired(['labelled-test-injection-no-process'], 1)
        solver.dispatch = injected_dispatch
        try:
            result = invoke('timeout-injection', certificate_request)
        finally:
            solver.dispatch = original_dispatch
        assert result['status'] == 'UNKNOWN' and result['delegate']['invoked'] and not result['delegate']['returned']
        return dict(injection='Synthetic dispatcher timeout; no subprocess is created for this case.',
                    status='UNKNOWN', request_preserved=result['request_preserved'])
    case('labelled-runtime-timeout', timeout_fault)
    assert sha((HERE / 'runtime.py').read_bytes()) == RUNTIME_SHA
    assert {p: sha((ROOT / p).read_bytes()) for p in pins} == initial
    report = dict(status='PASS', cases=cases, executed_sources=snapshot,
                  finished_utc=datetime.now(timezone.utc).isoformat(),
                  native_builds=0, compiler_invocations=0, universal_native_correctness_proved=False,
                  physical_selected_row_refinement_proved=False)
    save(args.output / 'TEST-RESULT.json', report)
    print(json.dumps(dict(status='PASS', cases=len(cases), runtime_sha256=RUNTIME_SHA)))


if __name__ == '__main__':
    main()
