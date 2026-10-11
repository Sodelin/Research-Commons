#!/usr/bin/env python3
"""Independent standard-library saved-byte reader; never imports target code."""
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T003502.004915Z')
R = W / '.build/runs/20261011T003950.153734Z'
F = W / 'lossless-export/main-fcad-failed-20261011T003950.153734Z'
TARGET = 'extraction/g6-natural-common-forest-factorization-fcadb6c4'
TD = R / 'targets/extraction_g6-natural-common-forest-factorization-fcadb6c4'
PREFIX = 'a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917'
FCAD = 'fcadb6c4029b06eed32c8d037f294e373d1f91be692807fa477ccbc8edd75f2c'
CORE = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'


def demand(ok, why):
    if not ok:
        raise AssertionError(why)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def pin(path, expected=None):
    path = Path(path)
    h = hashlib.sha256()
    size = 0
    with path.open('rb') as f:
        for b in iter(lambda: f.read(65536), b''):
            h.update(b)
            size += len(b)
    demand(expected is None or h.hexdigest() == expected, 'pin ' + str(path))
    return {'path': str(path), 'sha256': h.hexdigest(), 'bytes': size}


def load(path):
    return json.loads(Path(path).read_bytes())


def compare_decoded(encoded, original, expected_sha, expected_bytes):
    h = hashlib.sha256()
    count = 0
    with gzip.open(encoded, 'rb') as z, Path(original).open('rb') as f:
        while True:
            b = z.read(65536)
            if not b:
                demand(f.read(1) == b'', 'complete raw original comparison')
                break
            demand(b == f.read(len(b)), 'every gzip-restored byte matches original')
            count += len(b)
            h.update(b)
    demand(count == expected_bytes and h.hexdigest() == expected_sha, 'restored EOF/size/hash')
    return {'decoded_sha256': h.hexdigest(), 'decoded_bytes': count, 'all_original_bytes_compared': True}


def c3(node, bases):
    parents = bases[node]
    if not parents:
        return [node]
    seqs = [c3(b, bases)[:] for b in parents] + [parents[:]]
    out = [node]
    while any(seqs):
        seqs = [s for s in seqs if s]
        candidate = next((s[0] for s in seqs if all(s[0] not in t[1:] for t in seqs)), None)
        demand(candidate is not None, 'valid static C3')
        out.append(candidate)
        for seq in seqs:
            if seq and seq[0] == candidate:
                seq.pop(0)
    return out


def artifact_path(olean, suffix):
    return olean.with_suffix(suffix) if suffix in ['.olean', '.ilean', '.ir'] else Path(str(olean) + suffix[6:])


def bundle(olean, expected):
    known = ['.olean', '.olean.private', '.olean.server', '.ilean', '.ir']
    present = {suffix for suffix in known if artifact_path(olean, suffix).is_file()}
    demand(present == set(expected), 'complete companion inventory ' + str(olean))
    return {suffix: pin(artifact_path(olean, suffix), expected[suffix]) for suffix in expected}


def check():
    refs = []
    for rel, sha in [
        ('design/history/g6-natural-prefix-final-repair-static-qc-20261011T0037Z-solver_design_recovery/A080-FINAL-REPAIR-SOURCE-STATIC-QC-ATTEMPT1.json', '9c37a0628ddf31b35d3621115abaf92e349125cc1c3359c3f21e1f90e7e1efbf'),
        ('design/history/g6-natural-prefix-final-repair-static-qc-20261011T0037Z-solver_design_recovery/V6-PREPARER-STATIC-QC-ATTEMPT1.json', 'a4111766f0a95da647979b058061fe211e2b037748b68a7a8bcda0df02bd24a0'),
        ('design/history/g6-natural-prefix-final-repair-static-qc-20261011T0037Z-solver_design_recovery/A080-NATURAL141-PREPARATION-SAVED-QC-ATTEMPT2.json', '7bb8f30c7333370c939439c5043b0051be3f6cc1d24013a2873a4412622a3607'),
        ('quality/G6-NATURAL141-A080-PREPARED-ROOT-REVIEW-20261011T0037Z.json', '4d529cc1dd6b2e8144e45ff239b0aefb6d8050756c5b0c074c982bceb8c9d395'),
        ('design/history/g6-natural-prefix-a227-failure-saved-qc-20261011T0034Z-solver_design_recovery/THIRD-LIVE-A227-FAILURE-SAVED-QC-ATTEMPT1.json', '7638bd9e9e5e80b8c3cfa1dc6a46efc36c8adbc7cf93f126e9bddffbadf8e2b7')]:
        refs.append(pin(P / rel, sha))
    approval_pin = pin(P / 'quality/G6-NATURAL141-A080-RUN-APPROVAL-20261011T0037Z.json', '203983064a914135616a318a27a95176b3d129dc9d3adcf132899f41d94d1a00')
    approval = load(approval_pin['path'])
    for row in approval['evidence']:
        pin(row['path'], row['sha256'])
    capture_binding = load(W / 'PREPARATION.json')['additional_storage_input_pins']['capture_gate']
    demand(Path(capture_binding['path']).is_absolute() and Path(capture_binding['path']).is_relative_to(P), 'absolute actual capture gate')
    capture_gate = pin(capture_binding['path'], capture_binding['sha256'])
    demand(capture_gate['sha256'] == 'fd10483a0b482556f201805b50a38a65194ae2babeed3451298d8158b59697a9', 'unchanged capture gate')

    mp = pin(F / 'PRESERVATION-MANIFEST.json', '1939fe2afec3c55f50406556c07a9181acb44881091897659bb1962803f6c83b')
    demand(pin(P / 'lean/G6-NATURAL-COMMON-FACTORIZATION-MAIN-FCAD-FAILED-20261011T003950.153734Z-RESULT.json', mp['sha256'])['bytes'] == mp['bytes'], 'packet result is exact preservation manifest')
    m = load(mp['path'])
    demand(m['workspace'] == str(W) and m['actual_run'] == str(R) and m['complete_lossless_export_original'] == str(F), 'exact fixed saved context/run/export')
    demand(m['status'] == 'INCOMPLETE_TARGET_FAILURES_PRESERVED' and not m['packet_distribution_complete'] and m['lossless_distribution'] == 'FIXED_SHMEM_EXPORT_ONLY_EXPLICIT_CAPACITY_BOUNDARY', 'explicit complete fixed-shmem fallback, no complete materialized overlay claim')
    demand(not m['compiled_artifact_bytes_distributed'] and not m['original_attempts_overwritten'], 'no artifact distribution or attempt overwrite')
    rows = m['preserved_files']
    demand(len(rows) == len({r['path'] for r in rows}) == 55, '55 unique evidence rows')
    checked = []
    compressed = []
    for row in rows:
        rel = Path(row['path'])
        demand(not rel.is_absolute() and '..' not in rel.parts, 'safe relative evidence path')
        encoded = F / rel
        original = Path(row['original_path'])
        ep = pin(encoded, row['sha256'])
        op = pin(original, row['original_sha256'])
        demand(ep['bytes'] == row['bytes'], 'encoded length')
        with encoded.open('rb') as f:
            demand(f.read(4) != b'\x7fELF', 'no distributed ELF')
        item = {'row': row, 'fixed_stage': ep, 'original': op}
        if row.get('encoding') == 'gzip':
            demand(row['restored_sha256'] == row['original_sha256'] and row['restored_bytes'] == op['bytes'], 'restored identity binding')
            item['restoration_comparison'] = compare_decoded(encoded, original, row['restored_sha256'], row['restored_bytes'])
            compressed.append(row)
        else:
            demand(row.get('encoding') is None and encoded.read_bytes() == original.read_bytes(), 'every unchanged exported/original byte')
        checked.append(item)
    dp = pin(F / 'COMPRESSED-DISTRIBUTIONS.json', m['compressed_distributions_manifest_sha256'])
    d = load(dp['path'])
    demand(d['status'] == 'PASS_LOSSLESS_RAW_BYTE_DISTRIBUTION' and d['original_run_unchanged'] and d['distributions'] == compressed, 'exact gzip-restoration distribution')
    demand(sum(r['bytes'] for r in rows) + dp['bytes'] == m['measured_export_bytes_before_manifest'] == 1145887, 'exact55 rows plus distribution size')
    demand({str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()} == {r['path'] for r in rows} | {'PRESERVATION-MANIFEST.json', 'COMPRESSED-DISTRIBUTIONS.json'}, 'complete57-file fixed export inventory')
    cap = m['overlay_capacity_preflight']
    demand(cap['transient_reserve_bytes'] == 8388608 and cap['measured_payload_bytes'] == 1145887 and not cap['source_or_evidence_deleted'], 'same8MiB reserve/no deletion')
    demand(cap['free_before_bytes'] < cap['transient_reserve_bytes'] + cap['measured_payload_bytes'] + cap['manifest_and_result_reserve_bytes'], 'actual recorded capacity requires stated fallback')

    runtime = load(R / 'NATIVE-RUNTIME-PINS.json')
    final_native = load(R / 'NATIVE-RUNTIME-FINAL-REHASH.json')
    native_now = []
    for path, ident in runtime['libraries'].items():
        p = Path(path)
        q = pin(p, ident['sha256'])
        s = p.stat()
        demand(q['bytes'] == ident['bytes'] and [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns] == ident['stat_identity'], 'all current native bytes/stat identities')
        native_now.append(q)
    hashes = {k: v['sha256'] for k, v in runtime['libraries'].items()}
    demand(len(native_now) == 28 and final_native['stable'] and final_native['hashes'] == hashes, '28 initial/final native identities')
    demand(digest(json.dumps(hashes, sort_keys=True).encode()) == runtime['native_runtime_digest'], 'independent complete native digest')
    attempt_rows = []
    for name, module, source, status, exit_code, raw_bytes, gz_bytes, printed_standard in [
        ('00001-G6OriginalCommonPrefix', 'G6OriginalCommonPrefix', PREFIX, 'PASS_FRESH_KERNEL_CHECK', 0, 12548379, 289659, 3),
        ('00002-G6NaturalCommonForestFactorization', 'G6NaturalCommonForestFactorization', FCAD, 'FAILED_OR_RESOURCE', 1, 12594015, 291297, None)]:
        a = R / 'attempts' / name
        ap = pin(a / 'receipt.json')
        rec = load(ap['path'])
        cp = pin(a / 'STDERR-CAPTURE.json')
        capture = load(cp['path'])
        demand(rec['stderr_storage'] == capture and capture['complete'] and capture['eof'] and not capture['truncated'] and capture['reason'] is None, 'complete bound actual capture')
        gp = pin(a / 'stderr.raw.gz', capture['gzip_sha256'])
        demand(capture['gzip_path'] == gp['path'] and capture['gzip_bytes'] == gp['bytes'] == gz_bytes, 'encoded capture identity')
        raw = gzip.decompress((a / 'stderr.raw.gz').read_bytes())
        demand(len(raw) == capture['raw_bytes'] == raw_bytes and digest(raw) == capture['raw_sha256'] == rec['stderr_sha256'], 'complete decoded gzip EOF/hash/size')
        demand(not (a / 'stderr').exists(), 'no claimed separate raw live capture')
        names = re.findall(rb'calling init:\s*(\S+)', raw)
        resolved = {str(Path(n.decode()).resolve()) for n in names}
        demand(len(names) == len(resolved) == 10 and resolved == set(rec['native_initialized_libraries']), 'all10 actual initialized names')
        demand(all(rec['native_initialized_libraries'][k] == runtime['libraries'][k] for k in resolved), 'all10 full byte/stat native identities bound')
        demand(rec['native_runtime_digest'] == runtime['native_runtime_digest'] and rec['native_initialized_libraries_bound'], 'same bound native digest')
        demand(len(rec['native_loader_outputs']) == 1 and rec['native_loader_outputs'][0] == {'path': gp['path'], 'sha256': gp['sha256'], 'encoding': 'gzip', 'raw_sha256': digest(raw), 'raw_bytes': len(raw)}, 'exact one raw/encoded native evidence frame')
        sp = pin(a / 'stdout', rec['stdout_sha256'])
        stdout = (a / 'stdout').read_text()
        axes = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", stdout, re.S)
        errors = [(int(x), int(y)) for x, y in re.findall(r'^' + module + r'\.lean:(\d+):(\d+): error', stdout, re.M)]
        demand(rec['status'] == status and rec['exit_code'] == capture['exit_code'] == exit_code, 'actual module/capture exit/status')
        demand(rec['cap_memory_mib'] == 4096 and rec['cap_seconds'] == 180 and all(x in rec['command'] for x in ['-j1', '-t0', '-M4096', '-Ddebug.skipKernelTC=false']), 'strict4GiB180s kernel flags')
        demand(rec['source_and_imports_stable'] and rec['native_runtime_stat_stable'], 'stable actual input boundaries')
        source_pin = pin(a / ('work/' + module + '.lean'), source)
        demand(rec['source_sha256'] == source_pin['sha256'], 'exact actual source')
        imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.]*)', Path(source_pin['path']).read_text(), re.M)
        demand(set(imports) == set(rec['direct_import_bindings']), 'literal actual import set')
        imports_checked = []
        for module_name, binding in rec['direct_import_bindings'].items():
            bp = bundle(Path(binding['path']), binding['artifacts'])
            demand(bp['.olean']['sha256'] == binding['sha256'] == rec['direct_import_sha256'][module_name] and binding['artifacts'] == rec['direct_import_artifacts'][module_name], 'actual import complete byte bundle')
            imports_checked.append({'module': module_name, 'bindings': bp})
        if printed_standard is not None:
            demand(not errors and 'sorryAx' not in stdout + raw.decode(errors='replace') and len(axes) == printed_standard, 'actual prefix success with no diagnostics/sorry')
            demand(all({x.strip() for x in axs.split(',')} == {'propext', 'Classical.choice', 'Quot.sound'} for _, axs in axes), 'three actual public standard-axiom prints')
        else:
            demand(len(errors) == 31 and stdout.count('sorryAx') == 3, 'exact first fcad31 errors and3 diagnostic sorry prints preserved')
            demand(not (a / (module + '.olean')).exists() and 'object_artifacts' not in rec, 'no successful fcad object')
        attempt_rows.append({'attempt': ap, 'capture_descriptor': cp, 'encoded_capture': gp, 'decoded_bytes': len(raw), 'decoded_sha256': digest(raw), 'full_gzip_EOF': True, 'raw_comparison_qualification': 'Complete independently decoded identity; no separate uncompressed live file exists.', 'native_initialized_paths': sorted(resolved), 'stdout': sp, 'error_locations': errors, 'printed_axiom_records': [{'name': n, 'axioms': axs} for n, axs in axes], 'source': source_pin, 'actual_import_bundles': imports_checked})

    final = load(R / 'FINAL-RECEIPT.json')
    demand(final == m['final_receipt'] and final['status'] == 'INCOMPLETE_TARGET_FAILURES_PRESERVED' and not final['targets_passed'] and final['counts'] == {'cache_reuse': 139, 'fresh_components': 1}, 'exact incomplete overall result139 reused1 freshprefix')
    demand(final['trust_level'] == 0 and final['kernel_checking'] and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable'], 'strict complete run identity')
    demand({a.name for a in (R / 'attempts').iterdir()} == {'00001-G6OriginalCommonPrefix', '00002-G6NaturalCommonForestFactorization'}, 'exact2 actual component attempts; no aggregate/owned audit')
    target = load(TD / 'RESULT.json')
    demand(target['status'] == 'FAILED_OR_BLOCKED' and target['error'] == 'Component failed G6NaturalCommonForestFactorization' and len(target['component_receipts']) == 140, '140 admitted component entries then failedfcad')
    components = {row['module']: row for row in target['component_receipts']}
    demand(len(components) == 140 and 'G6NaturalCommonForestFactorization' not in components, '140 unique successes only')
    actual_prefix = load(R / 'attempts/00001-G6OriginalCommonPrefix/receipt.json')
    prefix_rec = components['G6OriginalCommonPrefix']
    demand(prefix_rec == {**actual_prefix, 'cached_object': prefix_rec['cached_object'], 'fresh_storage_qualification': 'same-FS hardlinks to immutable successful attempt outputs; no original object or receipt changed'}, 'prefix target/cache augmentation exact')
    prior = [r for r in components.values() if r['module'] != 'G6OriginalCommonPrefix']
    demand(len(prior) == 139 and all(not r['receipt_directory'].startswith(str(R)) and r['status'] == 'PASS_FRESH_KERNEL_CHECK' and r['exit_code'] == 0 for r in prior), '139 authenticated earlier successes; currentprefix only fresh')
    graph = load(W / 'DEPENDENCY-GRAPH.json')
    gm = graph['targets'][TARGET]['modules']
    graph_pin = pin(W / 'DEPENDENCY-GRAPH.json', final['graph_sha256'])
    inherited = []
    for name, rec in components.items():
        demand(rec['source_sha256'] == gm[name]['sha256'], 'actual admitted source exact graph')
        source = pin(W / ('source-store/' + rec['source_sha256'] + '.lean'), rec['source_sha256'])
        literal_imports = re.findall(r'^import\s+([A-Za-z_][A-Za-z0-9_.]*)', Path(source['path']).read_text(), re.M)
        demand(literal_imports == gm[name]['imports'], 'all140 admitted literal source imports')
        cache_receipt = pin(Path(rec['cached_object']).parent / 'receipt.json')
        demand(load(cache_receipt['path']) == rec, 'all140 current cache receipts exact target records')
        objects = bundle(Path(rec['cached_object']), rec['object_artifacts'])
        inherited.append({'module': name, 'source': source, 'cache_receipt': cache_receipt, 'cache_object_bundle': objects})

    key_data = {'module': 'G6OriginalCommonPrefix', 'source': PREFIX, 'compiler': prefix_rec['compiler_sha256'], 'mathlib': prefix_rec['mathlib_commit'], 'trust': 0, 'kernel_check': True, 'imports': prefix_rec['direct_import_artifacts'], 'native_runtime_digest': prefix_rec['native_runtime_digest'], 'artifact_boundary': 'olean-private-server-ilean-ir-native-v3'}
    key = digest(json.dumps(key_data, sort_keys=True).encode())
    demand(key == '54ae5d6ce3d15200690415bbd1279d656cc4bfd4afa654a9d4a8f01f81bb95a9' and prefix_rec['cached_object'] == str(W / ('.build/cache/' + key + '/artifact.olean')), 'independent strict component key')
    companions = []
    for suffix, sha in prefix_rec['object_artifacts'].items():
        paths = [artifact_path(x, suffix) for x in [R / 'attempts/00001-G6OriginalCommonPrefix/G6OriginalCommonPrefix.olean', Path(prefix_rec['cached_object']), TD / 'objects/G6OriginalCommonPrefix.olean']]
        pins = [pin(x, sha) for x in paths]
        demand(len({(x.stat().st_dev, x.stat().st_ino) for x in paths}) == 1 and len({x['bytes'] for x in pins}) == 1, 'actual fresh attempt/cache/install same-inode immutable companion')
        companions.append({'suffix': suffix, 'pins': pins, 'same_inode': True})
    component_report = pin(P / 'lean/G6-NATURAL-COMMON-A080-PARTIAL-COMPONENT-ADMISSION-20261011T003950.153734Z.json', 'ebd08bc411237ab09b4cd454891c4f85b9589fec99254ad6b491b26b7d7c2c1d')
    cr = load(component_report['path'])
    demand(cr['cache_key'] == key and cr['source_sha256'] == PREFIX and cr['complete_capture'] == actual_prefix['stderr_storage'] and not cr['root_or_audit_accepted'] and not cr['coherent_union_executed'], 'partial report exact and qualified')
    demand(pin(cr['cache_receipt'], cr['cache_receipt_sha256'])['sha256'] == '1210456fa737c8a7ad7c8caab999d60a01b391aad3e4ad10514b27877c204a05', 'exact prefix cache receipt identity')
    pin(W / 'scripts/build_connected.py', CORE)
    pin(R / 'BUILDER.py', CORE)

    equivalence = load(W / 'PARENT-WRAPPER-EQUIVALENCE.json')
    parent_pins = []
    for role in ['namespace', 'authenticated']:
        before = equivalence['accepted_' + role]
        after = equivalence['actual_' + role]
        replacement = equivalence[role + '_exact_replacement']
        parent_pins += [pin(before['path'], before['sha256']), pin(after['path'], after['sha256'])]
        a = Path(before['path']).read_text()
        b = Path(after['path']).read_text()
        demand(a.count(replacement['old']) == replacement['occurrences'] == 1 and a.replace(replacement['old'], replacement['new'], 1) == b, 'full parent source equality except one context-pin literal')
    scripts = W / 'scripts'
    classes = {}
    for filename in ['storage_wrapper.py', 'build_with_authenticated_overlay.py', 'build_with_mathlib_overlay.py']:
        classes[filename] = {c.name: c for c in ast.walk(ast.parse((scripts / filename).read_text())) if isinstance(c, ast.ClassDef)}
    demand([ast.unparse(x) for x in classes['storage_wrapper.py']['StorageBuilder'].bases] == ['parent', 'StorageInvocation'] and [ast.unparse(x) for x in classes['storage_wrapper.py']['StorageInvocation'].bases] == ['core.Builder'], 'frozen storage class bases')
    demand([ast.unparse(x) for x in classes['build_with_authenticated_overlay.py']['OverlayBuilder'].bases] == ['original.OverlayBuilder'] and [ast.unparse(x) for x in classes['build_with_mathlib_overlay.py']['OverlayBuilder'].bases] == ['core.Builder'], 'frozen parent class bases')
    mro = c3('StorageBuilder', {'StorageBuilder': ['Auth', 'StorageInvocation'], 'Auth': ['Namespace'], 'Namespace': ['Core'], 'StorageInvocation': ['Core'], 'Core': ['object'], 'object': []})
    demand(mro == ['StorageBuilder', 'Auth', 'Namespace', 'StorageInvocation', 'Core', 'object'], 'same-core C3 preserves authenticated invocation')
    facade = P / 'lean/scripts/run_proof_extensions_with_storage_20261011.py'
    pin(facade, '1ecc750032bbe5d0c44ae11dd1ca330db7e607a890c56b2a4c4516b202446b6c')
    demand('builder_module.OverlayBuilder, builder_module.original.core, policy' in facade.read_text(), 'same core explicitly passed')
    storage_pins = load(R / 'COMPRESSED-STDERR-STORAGE-PINS.json')
    demand(storage_pins['same_core_module_object'] and storage_pins['adapter_sha256'] == actual_prefix['storage_wrapper_sha256'] and storage_pins['authenticated_parent_sha256'] == equivalence['actual_authenticated']['sha256'] and storage_pins['namespace_parent_sha256'] == equivalence['actual_namespace']['sha256'], 'actual recorded source composition')
    gd = W / 'guard-runs/natural-20261011T003949.356147Z'
    prelaunch = [pin(row['path'], row['sha256']) for row in load(gd / 'PRE-PHASE-INPUT-PINS.json').values()]
    guard = load(gd / 'RECEIPT.json')
    plan = load(W / 'RESOURCE-AND-RUN-PLAN.json')
    demand(guard['exit_code'] == 1 and guard['abort_reason'] is None and guard['monitor_error'] is None and not guard['resource_caps_kernel_flags_core_or_audit_changed'], 'ordinary proof failure/no guard abort or policy change')
    demand(guard['peak_nonreclaimable_estimate_bytes'] < plan['memory_abort_bytes'] and guard['peak_distinct_inode_allocation_bytes'] < plan['scratch_abort_bytes'], 'saved resource peaks within guards')
    demand(guard['config_sha256'] == pin(W / 'RESOURCE-AND-RUN-PLAN.json')['sha256'] and guard['monitor_sha256'] == pin(W / 'scripts/guard_natural_common_20261011.py')['sha256'], 'actual monitor/plan identity')
    compiler = pin(actual_prefix['command'][0], actual_prefix['compiler_sha256'])
    demand(compiler['sha256'] == final['compiler_sha256'] == final['compiler_final_sha256'], 'compiler byte identity without execution')
    return {'status': 'PASS_SAVED_TWO_COMPLETE_CAPTURES_PARTIAL_PREFIX_COMPONENT_AND_FCAD_FAILURE_PRESERVATION_QC', 'actual_run_approval': approval_pin, 'capture_gate': capture_gate, 'prior_saved_qc': refs, 'manifest': mp, 'distribution_manifest': dp, 'preserved_file_comparisons': checked, 'file_counts': {'preserved_rows': 55, 'manifest_files': 2, 'fixed_export_files': 57, 'gzip_restoration_rows': len(compressed), 'measured_payload_before_preservation_manifest_bytes': 1145887, 'exported_ELFs': 0, 'complete_materialized_packet_distribution': False}, 'actual_attempts': attempt_rows, 'current_all_native_pins': native_now, 'current_compiler_pin': compiler, 'current_admitted_component_source_cache_pins': inherited, 'graph': graph_pin, 'prefix_strict_key': {'key': key, 'recipe': key_data, 'partial_report': component_report, 'same_inode_companions': companions}, 'prelaunch_pins': prelaunch, 'parent_source_equivalence': equivalence, 'parent_byte_pins': parent_pins, 'independent_static_C3': mro, 'outcome': {'prior_authenticated_reuses': 139, 'fresh_successful_prefix_components': 1, 'actual_failed_fcad_components': 1, 'fresh_aggregate_or_full_owned_audit': False, 'complete141_accepted': False, 'manifest141_count_semantics': '141 is selected executable closure, not completed-module count.145 includes4 nonexecuted protected guard records.'}, 'resource_observation': {'guard': pin(gd / 'RECEIPT.json'), 'peak_nonreclaimable_estimate_bytes': guard['peak_nonreclaimable_estimate_bytes'], 'peak_distinct_inode_allocation_bytes': guard['peak_distinct_inode_allocation_bytes'], 'no_resource_abort': True}, 'qualification': ['Prefix is one authenticated strict kernel component; its cache transport is qualified at exact source/compiler/native/import/object/key only. No fresh root theorem or complete ownership audit acceptance.', 'Both live captures independently fully decoded to EOF with exact raw/encoded hashes; already gzip bytes were distributed unchanged. No separate raw live capture file is claimed.', 'All55 original/fixed-stage rows and every restored raw byte were compared. Historical fixed-shmem fallback remains explicit; no complete materialized overlay export is claimed.', 'The first fcad source failed; three diagnostic sorryAx prints and31 errors are retained. Target aggregate and full-owned audit were never reached.', 'Accepted1504 and separate168/117, all previous failures/versions and runtime/application/source-fit scopes remain unchanged. No master closure, provenance/refinement, general storage capacity or future-union claim.']}


def main():
    report = {'schema': 'g6_natural_main_fcad_partial_failure_saved_qc_v1', 'contributor': 'Codex / solver_design_recovery', 'observed_utc': datetime.now(timezone.utc).isoformat(), 'reviewer_sha256': digest(Path(__file__).read_bytes()), 'target_modules_imported_or_producers_started': 0, 'mathematical_acceptance_promoted': False}
    try:
        report.update(check())
    except Exception as e:
        report.update(status='FAIL_SAVED_QC', error_type=type(e).__name__, error=str(e))
    out = Path(sys.argv[1])
    with out.open('x') as f:
        json.dump(report, f, indent=2, sort_keys=True, ensure_ascii=False)
        f.write('\n')
    print(json.dumps({'status': report['status'], 'receipt': str(out), 'sha256': digest(out.read_bytes())}))
    return 1 if report['status'] == 'FAIL_SAVED_QC' else 0


if __name__ == '__main__':
    raise SystemExit(main())
