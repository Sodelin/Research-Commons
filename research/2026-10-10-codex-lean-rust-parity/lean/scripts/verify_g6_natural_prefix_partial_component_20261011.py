#!/usr/bin/env python3
"""Authenticate one completed kernel component in the preserved failed141 run.

Read-only artifact checks plus a new attributed report. No Builder import,
compiler, evaluator, native producer, cache write, or root/audit acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re

from check_core import bundle, save, sha

ROOT = Path(__file__).resolve().parents[1]
MODULE = 'G6OriginalCommonPrefix'
SOURCE = 'a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917'
COMPILER = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
NATIVE = '6f8ad181b1b3b832d74cf0f88255b519a3512252c343d3e0cde0c540cbfe7aac'
STORAGE = 'd774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810'
CORE = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('workspace', type=Path)
    parser.add_argument('--run', required=True, type=Path)
    args = parser.parse_args()
    work = args.workspace.resolve(strict=True)
    run = args.run.resolve(strict=True)
    assert run.is_relative_to(work / '.build/runs')
    final = json.loads((run / 'FINAL-RECEIPT.json').read_bytes())
    assert final['status'] == 'INCOMPLETE_TARGET_FAILURES_PRESERVED'
    assert final['kernel_checking'] and final['trust_level'] == 0
    assert final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable']
    assert final['compiler_sha256'] == COMPILER and final['native_runtime_digest'] == NATIVE
    assert sha(work / 'scripts/build_connected.py') == sha(run / 'BUILDER.py') == CORE
    graph = json.loads((work / 'DEPENDENCY-GRAPH.json').read_bytes())
    assert sha(work / 'DEPENDENCY-GRAPH.json') == sha(run / 'DEPENDENCY-GRAPH.json') == final['graph_sha256']
    target_name, = final['targets_requested']
    target = graph['targets'][target_name]
    result_path = run / 'targets' / re.sub('[^A-Za-z0-9_-]', '_', target_name) / 'RESULT.json'
    target_result = json.loads(result_path.read_bytes())
    assert target_result['status'] == 'FAILED_OR_BLOCKED'
    components = {r['module']: r for r in target_result['component_receipts']}
    rec = components[MODULE]
    assert rec['status'] == 'PASS_FRESH_KERNEL_CHECK' and rec['exit_code'] == 0
    assert rec['source_sha256'] == target['modules'][MODULE]['sha256'] == SOURCE
    assert rec['compiler_sha256'] == COMPILER and rec['native_runtime_digest'] == NATIVE
    assert rec['source_and_imports_stable'] and rec['native_runtime_stat_stable']
    assert rec['native_initialized_libraries_bound'] and rec['native_initialized_libraries']
    assert rec['cap_memory_mib'] == 4096 and rec['cap_seconds'] == 180
    assert all(flag in rec['command'] for flag in ['-j1', '-t0', '-M4096', '-Ddebug.skipKernelTC=false'])
    assert sha(Path(rec['command'][0])) == COMPILER
    source = work / 'source-store' / (SOURCE + '.lean')
    frozen = Path(rec['working_directory']) / (MODULE + '.lean')
    assert sha(source) == sha(frozen) == SOURCE
    imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.]*)', source.read_text(), re.M)
    assert imports == target['modules'][MODULE]['imports']
    assert set(imports) == set(rec['direct_import_bindings'])
    import_checks = []
    for name in imports:
        binding = rec['direct_import_bindings'][name]
        parent = components[name]
        assert parent['source_sha256'] == target['modules'][name]['sha256']
        assert sha(work / 'source-store' / (parent['source_sha256'] + '.lean')) == parent['source_sha256']
        assert bundle(Path(binding['path'])) == binding['artifacts'] == parent['object_artifacts']
        assert bundle(Path(parent['cached_object'])) == parent['object_artifacts']
        assert json.loads((Path(parent['cached_object']).parent / 'receipt.json').read_bytes()) == parent
        import_checks.append({'module': name, 'source_sha256': parent['source_sha256'],
            'actual_import': binding, 'parent_cached_object': parent['cached_object'],
            'parent_receipt_sha256': sha(Path(parent['cached_object']).parent / 'receipt.json')})
    key_data = {'module': MODULE, 'source': SOURCE, 'compiler': COMPILER,
        'mathlib': rec['mathlib_commit'], 'trust': 0, 'kernel_check': True,
        'imports': rec['direct_import_artifacts'], 'native_runtime_digest': NATIVE,
        'artifact_boundary': 'olean-private-server-ilean-ir-native-v3'}
    key = hashlib.sha256(json.dumps(key_data, sort_keys=True).encode()).hexdigest()
    cache = work / '.build/cache' / key
    cache_receipt = cache / 'receipt.json'
    assert sha(cache_receipt) == '1210456fa737c8a7ad7c8caab999d60a01b391aad3e4ad10514b27877c204a05'
    assert json.loads(cache_receipt.read_bytes()) == rec
    attempt = Path(rec['receipt_directory'])
    assert sha(attempt / 'receipt.json') == 'da44ad2f402aa07ad514da7765848eeb76ce84b25b4736b97b69a04c3c3ee344'
    actual_receipt = json.loads((attempt / 'receipt.json').read_bytes())
    assert rec == {**actual_receipt, 'cached_object': str(cache / 'artifact.olean'),
        'fresh_storage_qualification': 'same-FS hardlinks to immutable successful attempt outputs; no original object or receipt changed'}
    expected = rec['object_artifacts']
    attempt_object = attempt / (MODULE + '.olean')
    installed = result_path.parent / 'objects' / (MODULE + '.olean')
    assert bundle(attempt_object) == bundle(cache / 'artifact.olean') == bundle(installed) == expected
    object_rows = []
    for suffix in expected:
        paths = [p.with_suffix(suffix) if suffix in ['.olean', '.ilean', '.ir'] else Path(str(p) + suffix[6:])
            for p in [attempt_object, cache / 'artifact.olean', installed]]
        assert len({(p.stat().st_dev, p.stat().st_ino) for p in paths}) == 1
        object_rows.append({'suffix': suffix, 'sha256': expected[suffix], 'bytes': paths[0].stat().st_size,
            'paths': [str(p) for p in paths], 'same_inode': True})
    assert sha(work / 'scripts/storage_wrapper.py') == sha(run / 'COMPRESSED-STDERR-STORAGE-WRAPPER.py') == STORAGE
    spec = importlib.util.spec_from_file_location('frozen_prefix_capture_authentication', work / 'scripts/storage_wrapper.py')
    storage = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(storage)
    capture = rec['stderr_storage']
    assert json.loads((attempt / 'STDERR-CAPTURE.json').read_bytes()) == capture
    assert capture['complete'] and capture['eof'] and not capture['truncated'] and capture['reason'] is None
    inspected = storage.inspect_capture(capture['gzip_path'], capture['raw_sha256'], capture['raw_bytes'])
    assert inspected['gzip_sha256'] == capture['gzip_sha256'] and inspected['gzip_bytes'] == capture['gzip_bytes']
    assert capture['raw_sha256'] == rec['stderr_sha256']
    assert inspected['native_used'] == sorted(rec['native_initialized_libraries'])
    assert storage.native_evidence_known(inspected, inspected['native_used'], rec['native_initialized_libraries'])
    assert sha(attempt / 'stdout') == rec['stdout_sha256']
    assert 'sorryAx' not in inspected['text'] + (attempt / 'stdout').read_text(errors='replace')
    native_pins = json.loads((run / 'NATIVE-RUNTIME-PINS.json').read_bytes())
    native_final = json.loads((run / 'NATIVE-RUNTIME-FINAL-REHASH.json').read_bytes())
    assert native_pins['native_runtime_digest'] == NATIVE and native_final['stable']
    current_hashes = {}
    for path, identity in native_pins['libraries'].items():
        p = Path(path)
        assert sha(p) == identity['sha256'] and p.stat().st_size == identity['bytes']
        s = p.stat()
        assert [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns] == identity['stat_identity']
        current_hashes[path] = identity['sha256']
    assert current_hashes == native_final['hashes']
    assert hashlib.sha256(json.dumps(current_hashes, sort_keys=True).encode()).hexdigest() == NATIVE
    assert all(native_pins['libraries'][p] == identity for p, identity in rec['native_initialized_libraries'].items())
    report = {'status': 'PASS_KERNEL_COMPONENT_AUTHENTICATION_ONLY_TARGET_INCOMPLETE',
        'workspace': str(work), 'actual_run': str(run), 'module': MODULE, 'source_sha256': SOURCE,
        'graph_sha256': final['graph_sha256'], 'cache_key': key,
        'cache_receipt': str(cache_receipt), 'cache_receipt_sha256': sha(cache_receipt),
        'attempt_receipt': str(attempt / 'receipt.json'), 'attempt_receipt_sha256': sha(attempt / 'receipt.json'),
        'target_result_sha256': sha(result_path), 'final_receipt_sha256': sha(run / 'FINAL-RECEIPT.json'),
        'object_companions': object_rows, 'direct_import_checks': import_checks,
        'compiler_sha256': COMPILER, 'native_runtime_digest': NATIVE,
        'current_native_files_rehashed': len(current_hashes), 'initialized_native_files': len(inspected['native_used']),
        'native_inventory_sha256': sha(run / 'NATIVE-RUNTIME-PINS.json'),
        'native_final_rehash_sha256': sha(run / 'NATIVE-RUNTIME-FINAL-REHASH.json'),
        'complete_capture': capture, 'stdout_sha256': rec['stdout_sha256'],
        'ordinary_caps': {'memory_mib': 4096, 'seconds': 180, 'trust': 0, 'kernel_type_checking': True},
        'exact_key_recipe_reproduced_from_unchanged_core': CORE,
        'storage_wrapper_sha256': STORAGE, 'verifier_sha256': sha(Path(__file__)),
        'qualification': 'One actual successful component from the incomplete141 target may be transported only at its exact source/compiler/native/import/object/cache key. This is partial component provenance, not a root theorem or complete ownership audit acceptance. A corrected factorization still requires a fresh target aggregate and full141-module owned audit.',
        'root_or_audit_accepted': False, 'coherent_union_executed': False,
        'compiler_evaluator_or_native_producer_invoked': False, 'original_inputs_modified': False}
    output = ROOT / ('G6-NATURAL-COMMON-A080-PARTIAL-COMPONENT-ADMISSION-' + run.name + '.json')
    assert not output.exists()
    save(output, report)
    print(json.dumps({'status': report['status'], 'output': str(output), 'sha256': sha(output),
        'cache_key': key, 'native_files': len(current_hashes), 'object_companions': len(object_rows)}))


if __name__ == '__main__':
    main()
