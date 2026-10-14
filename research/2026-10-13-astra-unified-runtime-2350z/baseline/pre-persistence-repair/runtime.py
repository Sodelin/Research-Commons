#!/usr/bin/env python3
"""Thin pinned runtime delegation; no new decoder, mathematics or native compiler."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
MAX_BYTES = 262144
MAX_BINARY_BYTES = 128 * 1024 * 1024
PINS = {
    "research/2026-10-13-astra-unified-solver-0645z/solve.py": "cebe79e7fcebe554faaf38580b831770f5c877affc41020b891d830532080b9e",
    "research/2026-10-13-astra-unified-solver-0645z/certificates.py": "ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3",
    "research/2026-10-13-astra-unified-solver-0645z/emit_lean.py": "27264a92409966415094b902df8226e7a86f305c0cef148325c7f6f60795ae37",
    "research/2026-10-13-astra-unified-solver-0645z/external_encoding.py": "78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69",
    "research/2026-10-13-astra-unified-solver-0645z/native_bridge.py": "b298ae551bc488aab45560434a5f9dc2bead15a4c0b0328199577e63ac808f39",
    "research/2026-10-13-astra-selected-copy-readout-2250z/selected_readout.py": "2a2862a1b8b91c821c1552dc62d6e5dea4957881fe35d6d68865c30c00c17115",
    "research/2026-10-13-astra-emitted-support-2110z/emit_support.py": "6e7dc1faea63642464b802b59aceed7c809ea2f5148abb62bca36dab9b11bfdd",
    "research/2026-10-13-astra-positive-support-adapter-0830z/lean/Astra/PositiveSupportAdapter.lean": "29782b7ff42fefd5b1634e20ea1f0c695714e5cd625c2730a255bbda656ab479",
    "applications/practical-solver/certified_bounds.py": "4d7caca77386cba972e7af3266e583ae0970833811014c9b17eda01732b798fa",
    "research/2026-10-13-astra-unified-solver-0645z/evidence/rust-binary/RECEIPT.json": "0127eb87cc30ddbd2c2fdf8ba6ab00ebbccbd624a7891b2caa1478decef00a09",
    "research/2026-10-13-astra-unified-solver-0645z/evidence/rust-generator-binary/RECEIPT.json": "53aec2cbf164eaab1818591a2fe5ac63fb2198206aa0369759a67ae3c8bc087f",
    "research/2026-10-13-astra-unified-solver-0645z/evidence/unified-emitter-real-repair-cases/certificate/RESULT.json": "ac6d5a61c8aaf2b23e26f0185500f0b09b84df9042b07101c1aaf569c953dc84",
    "research/2026-10-13-astra-native-acquisition-0815z/evidence/SUCCESSOR-CORRESPONDENCE.json": "3774b0f2584881de81f6efe5f79ac0bca9c12665dc4fd9d7882f290bf47a8028"
}
SOURCES = {
    'certificates': 'research/2026-10-13-astra-unified-solver-0645z/certificates.py',
    'solve': 'research/2026-10-13-astra-unified-solver-0645z/solve.py',
    'emit_lean': 'research/2026-10-13-astra-unified-solver-0645z/emit_lean.py',
    'external_encoding': 'research/2026-10-13-astra-unified-solver-0645z/external_encoding.py',
    'native_bridge': 'research/2026-10-13-astra-unified-solver-0645z/native_bridge.py',
    'selected_readout': 'research/2026-10-13-astra-selected-copy-readout-2250z/selected_readout.py',
    'emit_support': 'research/2026-10-13-astra-emitted-support-2110z/emit_support.py',
}
CHECKERS = {
    '1a508f23613bb527e5605c806fb8215ed6a16adeed4c4147658236790064d805': {
        'profile': 'certificate-checker-original',
        'generation': False,
        'receipt': 'research/2026-10-13-astra-unified-solver-0645z/evidence/rust-binary/RECEIPT.json',
        'observation': 'research/2026-10-13-astra-unified-solver-0645z/evidence/unified-emitter-real-repair-cases/certificate/RESULT.json',
    },
    '3d7678fac5ba8138b28a08e40c6ca8ac2b3a6e13267350d48480997e53f27ef7': {
        'profile': 'certificate-checker-and-singleton-generator',
        'generation': True,
        'receipt': 'research/2026-10-13-astra-unified-solver-0645z/evidence/rust-generator-binary/RECEIPT.json',
        'observation': 'research/2026-10-13-astra-native-acquisition-0815z/evidence/SUCCESSOR-CORRESPONDENCE.json',
    },
}


class Refused(ValueError):
    pass


class Unavailable(RuntimeError):
    pass


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def pinned(relative, observed):
    path = ROOT / relative
    raw = path.read_bytes()
    if sha(raw) != PINS[relative]:
        raise Unavailable('selected provider identity changed: ' + relative)
    observed[relative] = PINS[relative]
    return path


def load(name, observed):
    path = pinned(SOURCES[name], observed)
    # Dependencies use the original module names. Refuse a shadowed module
    # instead of replacing an already-loaded provider inside this process.
    if name in sys.modules:
        module = sys.modules[name]
        if Path(getattr(module, '__file__', '')).resolve() != path.resolve():
            raise Unavailable('loaded provider origin differs: ' + name)
        return module
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    sys.path.insert(0, str(BASE))
    try:
        spec.loader.exec_module(module)
    except BaseException:
        sys.modules.pop(name, None)
        raise
    finally:
        sys.path.pop(0)
    pinned(SOURCES[name], observed)
    return module


def checker(binary, generation, observed):
    if binary is None:
        if generation:
            raise Unavailable('native generation requires an approved generator executable')
        return None
    path = Path(binary)
    if path.is_symlink() or not path.is_file():
        raise Unavailable('native checker must be an available regular nonsymlink file')
    with path.open('rb') as stream:
        raw = stream.read(MAX_BINARY_BYTES + 1)
    if len(raw) > MAX_BINARY_BYTES:
        raise Unavailable('native checker exceeds bounded runtime file size')
    ident = sha(raw)
    if ident not in CHECKERS:
        raise Unavailable('native checker is not an approved executed profile')
    profile = CHECKERS[ident]
    receipt_path = pinned(profile['receipt'], observed)
    receipt = json.loads(receipt_path.read_text())
    if receipt.get('exit_code') != 0 or receipt.get('stop') is not None:
        raise Unavailable('approved checker build receipt is not a closed success')
    observation = json.loads(pinned(profile['observation'], observed).read_text())
    if profile['generation']:
        agreement = observation['exact_native_generation_agreement']
        passed = observation['status'] == 'PASS' and agreement['agree'] and agreement['exit_code'] == 0
        observed_binary = agreement['binary_sha256']
    else:
        passed = (observation['status'] == 'CHECKED_RATIONAL_CERTIFICATE' and
                  all(row['agree'] and row['exit_code'] == 0 for row in observation['native']['checks']))
        observed_binary = observation['native']['binary_sha256']
    if not passed or observed_binary != ident:
        raise Unavailable('approved checker observation does not bind this executable')
    if generation and not profile['generation']:
        raise Unavailable('approved older checker has no singleton-generation capability')
    return dict(profile=profile['profile'], binary_sha256=ident,
                build_receipt=profile['receipt'], build_receipt_sha256=PINS[profile['receipt']],
                execution_observation=profile['observation'],
                execution_observation_sha256=PINS[profile['observation']],
                generation_supported=profile['generation'],
                source_to_binary_relationship='previous observed controlled build; compiler and OS trusted')


def save(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def candidates(request, result):
    """Find existing supplied/generated certificate records without changing them."""
    if result.get('status') == 'REFUSED_REQUEST':
        return []
    if request['schema'] == 'selected_native_common_readout_v1':
        if 'conditional_arithmetic' not in result:
            return []
        return [('menu.pairs[' + str(i) + '].certificate', row['certificate'])
                for i, row in enumerate(request['menu']['pairs'])]
    task = request['task']
    if task == 'check_certificate':
        return [('input', request['input'])]
    if task == 'common_menu':
        return [('input.pairs[' + str(i) + '].certificate', row['certificate'])
                for i, row in enumerate(request['input']['pairs'])]
    cert = result.get('certificate_result', {}).get('certificate')
    return [('delegate.certificate_result.certificate', cert)] if cert is not None else []


def emit(certificates, output, api, observed):
    if not certificates:
        return dict(status='NOT_APPLICABLE', sources=[], compiled=False)
    pinned('research/2026-10-13-astra-positive-support-adapter-0830z/lean/Astra/PositiveSupportAdapter.lean', observed)
    load('emit_lean', observed)
    emitter = load('emit_support', observed)
    folder = output / 'support'
    folder.mkdir()
    emitted = {}
    refs = []
    for location, certificate in certificates:
        ident = api.digest(certificate)
        refs.append(dict(location=location, certificate_sha256=ident))
        if ident not in emitted:
            manifest = emitter.emit(certificate, folder / ident)
            emitted[ident] = dict(path='support/' + ident, manifest=manifest,
                emission_manifest_sha256=sha((folder / ident / 'EMISSION.json').read_bytes()))
    return dict(status='EMITTED_UNCOMPILED', certificate_references=refs,
                sources=list(emitted.values()), compiled=False,
                physical_source_certified=False, native_refinement_proved=False)


def run(raw, output, *, backend_python=None, rust_binary=None, parity_binary=None,
        parity_sources=None, native_generation=False, emit_support=False):
    result = dict(schema='astra_unified_runtime_result_v1', status='UNKNOWN',
                  source_feasibility_certified=False, universal_native_correctness_claimed=False,
                  general_G3_resolved=False, request_preserved=False,
                  delegate=None, support_emission=None)
    # This gate precedes directory creation and persistence, including direct API use.
    try:
        if type(raw) not in (bytes, str) or len(raw) > MAX_BYTES:
            raise Refused('request exceeds bounded transport or is not literal bytes/text')
        encoded = raw if isinstance(raw, bytes) else raw.encode('utf-8')
        if len(encoded) > MAX_BYTES:
            raise Refused('request exceeds bounded UTF8 transport')
    except (Refused, UnicodeError) as error:
        return {**result, 'status': 'REFUSED_REQUEST', 'reason': str(error),
                'request_preserved': False}
    try:
        out = Path(output).absolute()
        if out.exists() or out.is_symlink():
            raise Refused('output directory must be absent')
        out.mkdir(parents=True, exist_ok=False)
    except (Refused, TypeError, ValueError) as error:
        return {**result, 'status': 'REFUSED_REQUEST', 'reason': str(error),
                'request_preserved': False}
    except OSError as error:
        return {**result, 'reason': 'output unavailable: ' + str(error),
                'request_preserved': False}
    observed = {}
    try:
        (out / 'REQUEST.json').write_bytes(encoded)
        result.update(request_preserved=True, primary_request_bytes=len(encoded),
                      primary_request_sha256=sha(encoded))
        result['runtime_sha256'] = sha(Path(__file__).read_bytes())
        api = load('certificates', observed)
        if api.MAX_BYTES != MAX_BYTES:
            raise Unavailable('selected transport bound differs')
        api.require(type(native_generation) is bool and type(emit_support) is bool,
                    'runtime option flags must be booleans')
        request = api.loads(encoded)
        api.require(type(request) is dict and type(request.get('schema')) is str,
                    'request object and schema string required')
        result['canonical_request_sha256'] = api.digest(request)
        schema = request['schema']
        child_dir = out / 'delegate'
        if schema == 'selected_native_common_readout_v1':
            if native_generation or rust_binary is not None:
                raise Unavailable('certificate-checker options do not apply to selected native readouts')
            for name in ['external_encoding', 'native_bridge']:
                load(name, observed)
            selected = load('selected_readout', observed)
            result['delegate'] = dict(provider='selected_readout.run', result_path='delegate/RESULT.json',
                                      invoked=True, returned=False)
            child = selected.run(encoded, child_dir, parity_binary, parity_sources)
            result['delegate'].update(result=child, returned=True)
        elif schema == 'unified_research_solver_v1':
            api.fields(request, ['schema', 'task', 'input'])
            api.require(type(request['task']) is str, 'solver task must be a string')
            task = request['task']
            if task not in ('native_rc1', 'source_search', 'generate_singleton', 'check_certificate', 'common_menu'):
                raise Unavailable('unsupported unified runtime task')
            solver = load('solve', observed)
            if task == 'source_search':
                pinned('applications/practical-solver/certified_bounds.py', observed)
            elif task == 'native_rc1':
                load('native_bridge', observed)
            else:
                load('emit_lean', observed)
                if task == 'common_menu':
                    load('external_encoding', observed)
                result['native_checker'] = checker(rust_binary,
                    native_generation and task == 'generate_singleton', observed)
            child_dir.mkdir()
            result['delegate'] = dict(provider='solve.dispatch', result_path='delegate/RESULT.json',
                                      invoked=True, returned=False)
            child = solver.dispatch(request, child_dir, backend_python, rust_binary,
                                    parity_binary, parity_sources, native_generation)
            result['delegate'].update(result=child, returned=True)
            save(child_dir / 'RESULT.json', child)
            result['delegate']['result_sha256'] = sha((child_dir / 'RESULT.json').read_bytes())
            if task not in ('source_search', 'native_rc1') and rust_binary is not None:
                after = checker(rust_binary, native_generation and task == 'generate_singleton', observed)
                if after != result['native_checker']:
                    raise Unavailable('native checker identity changed during execution')
        else:
            raise Unavailable('unsupported runtime request schema')
        # Preserve the entire original semantic contract, even if a later check fails.
        result['delegate']['result_sha256'] = sha((child_dir / 'RESULT.json').read_bytes())
        identity = child.get('canonical_request_sha256', child.get('request_sha256'))
        if identity is not None and identity != result['canonical_request_sha256']:
            raise Unavailable('delegate request identity differs from the primary parsed request')
        result.update(status=child['status'],
                      source_feasibility_certified=child.get('source_feasibility_certified', False))
        # Do not strip the source_search backend's actual checked class/witness scope.
        # Selected readouts remain physical UNKNOWN exactly as returned by their provider.
        if emit_support:
            try:
                result['support_emission'] = emit(candidates(request, child), out, api, observed)
            except Exception as error:
                result['support_emission'] = dict(status='UNKNOWN', reason=str(error), compiled=False)
    except (Unavailable, OSError, subprocess.TimeoutExpired, MemoryError) as error:
        result.update(status='UNKNOWN', reason=str(error), source_feasibility_certified=False)
    except (ValueError, TypeError, KeyError) as error:
        result.update(status='REFUSED_REQUEST', reason=str(error), source_feasibility_certified=False)
    except Exception as error:
        result.update(status='UNKNOWN', reason=type(error).__name__ + ': ' + str(error),
                      source_feasibility_certified=False)
    if result['delegate'] is not None and not result['delegate']['returned']:
        result['delegate']['failure'] = result.get('reason', 'delegate did not return a result')
    result['authenticated_provider_sources'] = observed
    result['trust_boundaries'] = [
        'Delegated backend/compiler/executable/OS trust retains each original result scope.',
        'Selected readout extraction/evaluation is finite tested code, not native-to-typed refinement.',
        'Support emission proves nothing until separately compiled and audited; physical row premises remain separate.',
        'No protected bounded representative or arbitrary-input G3 closure is added.',
    ]
    try:
        save(out / 'RESULT.json', result)
    except OSError as error:
        result.update(status='UNKNOWN', persistence_error=str(error))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--request', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--backend-python')
    parser.add_argument('--rust-binary', type=Path)
    parser.add_argument('--parity-binary', type=Path)
    parser.add_argument('--parity-sources', type=Path)
    parser.add_argument('--native-generation', action='store_true')
    parser.add_argument('--emit-support', action='store_true')
    args = parser.parse_args()
    try:
        with args.request.open('rb') as stream:
            raw = stream.read(MAX_BYTES + 1)
        result = run(raw, args.output, backend_python=args.backend_python, rust_binary=args.rust_binary,
                     parity_binary=args.parity_binary, parity_sources=args.parity_sources,
                     native_generation=args.native_generation, emit_support=args.emit_support)
    except OSError as error:
        result = dict(status='UNKNOWN', reason='request unavailable: ' + str(error))
    print(json.dumps({key:result[key] for key in
          ['status', 'reason', 'source_feasibility_certified', 'primary_request_sha256'] if key in result}))
    return 2 if result['status'] == 'UNKNOWN' else 1 if result['status'] == 'REFUSED_REQUEST' else 0


if __name__ == '__main__':
    raise SystemExit(main())
