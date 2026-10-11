#!/usr/bin/env python3
"""Independent saved-byte/JSON/source reader; no target imports or execution."""
import ast
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
R = W/'.build/runs/20261011T014055.249073Z'
E = W/'lossless-export/proof141-20261011T014055.249073Z'
TARGET = 'extraction/g6-natural-common-forest-factorization-3fc98f89'
TD = R/'targets/extraction_g6-natural-common-forest-factorization-3fc98f89'
MODULE = 'G6NaturalCommonForestFactorization'
SOURCE = '3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4'
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}
OLD_ALIAS = '_private.UnifiedLean.G6.PrivateRegisterCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
NEW_ALIAS = '_private.UnifiedLean.Source.SourceInitializedCalendar.0.UnifiedLean.Source.SourceCalendarCompiler.calendarTail.match_1.splitter'
ALIAS_ROW = 'UnifiedLean.Source.SourceCalendarCompiler.calendarTail.eq_def'

def require(ok, reason):
    if not ok:
        raise AssertionError(reason)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pin(path, expected=None):
    path = Path(path)
    h = hashlib.sha256()
    n = 0
    with path.open('rb') as f:
        for b in iter(lambda: f.read(65536), b''):
            h.update(b)
            n += len(b)
    require(expected is None or h.hexdigest() == expected, 'pin ' + str(path))
    return {'path': str(path), 'bytes': n, 'sha256': h.hexdigest()}

def load(path):
    return json.loads(Path(path).read_bytes())

def imported(text):
    text = re.sub(r'/\-.*?\-/|--[^\n]*', '', text, flags=re.S)
    return [n for m in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)', text, re.M) for n in m.group(1).split()]

def companion(base, suffix):
    return base.with_suffix(suffix) if suffix in ('.olean', '.ilean', '.ir') else Path(str(base) + suffix[len('.olean'):])

def same_inode(a, b):
    x, y = Path(a).stat(), Path(b).stat()
    require((x.st_dev, x.st_ino) == (y.st_dev, y.st_ino), 'same inode ' + str(a))

def c3(name, bases):
    parents = bases[name]
    if not parents:
        return [name]
    seqs = [c3(b, bases)[:] for b in parents] + [parents[:]]
    out = [name]
    while any(seqs):
        seqs = [s for s in seqs if s]
        item = next((s[0] for s in seqs if all(s[0] not in t[1:] for t in seqs)), None)
        require(item is not None, 'valid static C3')
        out.append(item)
        for s in seqs:
            if s and s[0] == item:
                s.pop(0)
    return out

def check():
    manifest_pin = pin(E/'PRESERVATION-MANIFEST.json', '6db53e2eba1679cae6841cf1e2c6ffc37cd3d985873d0f8d73a8e2c17094bf30')
    pin(W/'G6-NATURAL-COMMON-FACTORIZATION-PROOF141-20261011T014055.249073Z-RESULT.json', manifest_pin['sha256'])
    manifest = load(manifest_pin['path'])
    require(manifest['workspace'] == str(W) and manifest['actual_run'] == str(R) and manifest['evidence'] == str(E), 'exact fixed context/run/export')
    require(manifest['status'] == 'PASS_ALL_REQUESTED_TARGETS' and manifest['packet_distribution_complete'] is False and manifest['lossless_distribution'] == 'FIXED_SHMEM_EXPORT_ONLY_EXPLICIT_CAPACITY_BOUNDARY', 'complete fixed-shmem export with historical packet capacity fallback')
    require(not manifest['compiled_artifact_bytes_distributed'] and not manifest['original_attempts_overwritten'], 'no object distribution/attempt overwrite')
    rows = manifest['preserved_files']
    require(len(rows) == len({x['path'] for x in rows}) == 71, '71 unique preserved rows')
    preserved, compressed = [], []
    for row in rows:
        rel = Path(row['path'])
        require(not rel.is_absolute() and '..' not in rel.parts, 'relative saved evidence path')
        encoded, original = E/rel, Path(row['original_path'])
        ep, op = pin(encoded, row['sha256']), pin(original, row['original_sha256'])
        require(ep['bytes'] == row['bytes'], 'exact stored bytes')
        require(encoded.open('rb').read(4) != b'\x7fELF', 'no exported ELF')
        item = {'stored': ep, 'original': op}
        if row.get('encoding') == 'gzip':
            h, count = hashlib.sha256(), 0
            with gzip.open(encoded, 'rb') as z, original.open('rb') as raw:
                while True:
                    block = z.read(65536)
                    if not block:
                        require(raw.read(1) == b'', 'all original restored bytes and EOF')
                        break
                    require(block == raw.read(len(block)), 'every restored byte identical original')
                    h.update(block)
                    count += len(block)
            require(h.hexdigest() == row['restored_sha256'] == op['sha256'] and count == row['restored_bytes'] == op['bytes'], 'restored raw identity')
            item['restored_bytes'] = count
            item['restored_sha256'] = h.hexdigest()
            compressed.append(row)
        else:
            require(encoded.read_bytes() == original.read_bytes(), 'uncompressed original byte equality')
        preserved.append(item)
    distribution_pin = pin(E/'COMPRESSED-DISTRIBUTIONS.json', 'dc4feb95d5ffd497fa15e577c92cdc1c17cf5c3b88945a0d3979b568e2ce4d06')
    distribution = load(distribution_pin['path'])
    require(distribution['distributions'] == compressed and len(compressed) == 17 and distribution['original_run_unchanged'], '17 exact gzip distribution rows')
    require(sum(x['bytes'] for x in rows) + distribution_pin['bytes'] == manifest['measured_export_bytes_before_manifest'] == 4630159, '71 rows+distribution payload size')
    require({str(p.relative_to(E)) for p in E.rglob('*') if p.is_file()} == {x['path'] for x in rows} | {'COMPRESSED-DISTRIBUTIONS.json', 'PRESERVATION-MANIFEST.json'}, 'complete73file fixed export')
    cap = manifest['overlay_capacity_preflight']
    require(cap['transient_reserve_bytes'] == 8388608 and cap['measured_payload_bytes'] == 4630159 and not cap['source_or_evidence_deleted'] and cap['free_before_bytes'] < cap['transient_reserve_bytes'] + cap['measured_payload_bytes'] + cap['manifest_and_result_reserve_bytes'], 'historical exact capacity requires fixed fallback')

    cert_pin = pin(W/'G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-CERTIFICATE-20261011T014055.249073Z.json', '15525987280d430dcb83585aaf76f5a33042ece6f1a781eeb2ed51949bd78934')
    cert = load(cert_pin['path'])
    require(cert['preservation_manifest_sha256'] == manifest_pin['sha256'] and not cert['full_1504_owned_metadata_retention_claimed'] and not cert['coherent_union_executed'] and cert['historical_evidence_or_scientific_gates_promoted'] is False, 'separate141 certificate, no1504-retention/union/historical promotion')
    refs = [pin(W/'design-qc/natural-v10-preparation-20261011T0144Z-solver_design_recovery/V10-ACTUAL-PREPARATION-SAVED-QC-ATTEMPT1.json','fcfda31e794fb4d48ed9c42558c95f4adaf5cb2b4bcf745a84c82472eade023c'),pin(Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')/'design-qc/factor-3fc-and-v10-source-20261011T0132Z-solver_design_recovery/FACTOR-3FC-AND-V10-STATIC-QC-ATTEMPT2.json','a7ecbf6ce59c8ed585589c9e8439de98340f06796b8a95d49cc077a186fb74ab')]
    graph_pin = pin(W/'DEPENDENCY-GRAPH.json', cert['graph_sha256'])
    graph = load(graph_pin['path'])
    selected, guards = graph['targets'][TARGET], graph['targets']['context/protected-mathlib-providers']
    modules = {**selected['modules'], **guards['modules']}
    require(len(selected['modules']) == len(selected['order']) == 141 and selected['roots']==[MODULE] and len(guards['modules'])==4 and len(modules)==145 and not set(selected['modules'])&set(guards['modules']),'141 executed/145 staged/four protected guard-only records')
    require(guards['status']=='PROTECTED_NAMESPACE_CONTEXT_ONLY_NOT_EXECUTED','guard-only records not executed')
    parent_pin = pin(P/'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json', '1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2')
    parent = load(parent_pin['path'])
    closure = load(W/'SOURCE-CLOSURE.json')
    require(len(closure) == 145 and {x['module'] for x in closure} == set(modules), 'all145 current source records')
    for row in closure:
        require((row['sha256'], row['imports']) == (modules[row['module']]['sha256'], modules[row['module']]['imports']), 'current source/graph metadata')
        pin(row['scratch_source'], row['sha256'])
        pin(row['preserved_source'], row['sha256'])
        require(imported(Path(row['scratch_source']).read_text()) == row['imports'], 'literal source normal/public imports')
        if row['module'] not in (MODULE,'G6OriginalCommonPrefix','G6OriginalParallelArmTransport'):
            require(parent['source_pins'][row['module']] == row['sha256'], 'accepted exact parent/guard source')
        elif row['module']=='G6OriginalParallelArmTransport':
            require(row['sha256']=='f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc','separately accepted f40 source')
        elif row['module']=='G6OriginalCommonPrefix':
            require(row['sha256']=='a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917','qualified prefix source')
    freeze_pin = pin(Path(cert['source_freeze']['path']),'d54d69c760f24b6e6a2e6fb7310c6b6d5a489250663bfafb82b0adda62d9da9f')
    freeze = load(freeze_pin['path'])
    for source in freeze['sources']:
        for rel in (source['path'],source['immutable_version']):
            path=Path(rel);pin(path if path.is_absolute() else P.parents[1]/rel,source['sha256'])
        pin(E/'sources'/f"{source['module']}.lean",source['sha256'])
    require(cert['source_provider_partition']=={'accepted1504':138,'separately_accepted_parallel_arm':1,'new_source_versions':2},'exact parent/source partition')
    final_pin = pin(R/'FINAL-RECEIPT.json', 'f27804291024a65bb6721872c7e6bdbca8521c212f7d434f1debc1bd4d1e20dd')
    final = load(final_pin['path'])
    require(final == manifest['final_receipt'] and final['status'] == 'PASS_ALL_REQUESTED_TARGETS' and final['targets_requested'] == final['targets_passed'] == [TARGET] and final['counts'] == {'cache_reuse':140, 'fresh_components':1} and final['trust_level'] == 0 and final['kernel_checking'] and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable'], 'actual140 reused1fresh strict kernel/final PASS')
    result = load(TD/'RESULT.json')
    require((result['status'], result['roots'], result['closure_modules'], result['declarations'], result['theorems']) == ('PASS', 1, 141, 3486, 2293), 'target result audit counts')
    components = result['component_receipts']
    require(len(components) == 141 and {x['module'] for x in components} == set(selected['modules']), 'all141 actual component records')
    fresh = [x for x in components if x['receipt_directory'].startswith(str(R)+'/')]
    require(len(fresh) == 1 and fresh[0]['module'] == MODULE, 'exact one fresh root')
    root_raw = load(R/f'attempts/00001-{MODULE}/receipt.json')
    require(fresh[0] == {**root_raw, 'cached_object':fresh[0]['cached_object'], 'fresh_storage_qualification':'same-FS hardlinks to immutable successful attempt outputs; no original object or receipt changed'}, 'fresh receipt exact cache/storage annotation only')
    require(all(result[k]['receipt_directory'].startswith(str(R)+'/') for k in ('aggregate_receipt', 'audit_receipt')), 'fresh aggregate and full owned audit')
    expected_attempts = {f'00001-{MODULE}', '00002-Connected_extraction_g6-natural-common-forest-factorization-3fc98f89', '00003-OwnedAudit'}
    require({p.name for p in (R/'attempts').iterdir()} == expected_attempts, 'exact three actual attempts')
    for rec in components + [result['aggregate_receipt'], result['audit_receipt']]:
        require(rec['exit_code'] == 0 and rec['source_and_imports_stable'] and rec['compiler_sha256'] == final['compiler_sha256'] and rec['native_runtime_digest'] == final['native_runtime_digest'] and '-Ddebug.skipKernelTC=false' in rec['command'], 'component/aggregate/audit source/native/kernel binding')

    compiled = {}
    def bind(path, expected):
        path = str(path)
        if path in compiled:
            require(compiled[path]['sha256'] == expected, 'consistent repeated compiled identity')
        else:
            compiled[path] = pin(path, expected)
        return compiled[path]
    def bundle(path, expected):
        path = Path(path)
        inventory = {s for s in ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir') if companion(path, s).is_file()}
        require(inventory == set(expected), 'complete artifact companion inventory '+str(path))
        return {s: bind(companion(path,s), h) for s,h in expected.items()}
    for rec in components:
        require(rec['source_sha256'] == selected['modules'][rec['module']]['sha256'], 'actual component exact source')
        cache_path = Path(rec['cached_object']).parent/'receipt.json'
        require(load(cache_path) == rec, 'actual cache receipt exact target record')
        bundle(rec['cached_object'], rec['object_artifacts'])
        for name, imp in rec['direct_import_bindings'].items():
            require(imp['sha256'] == imp['artifacts']['.olean'] == rec['direct_import_sha256'][name] and imp['artifacts'] == rec['direct_import_artifacts'][name], 'full direct-import receipt identity')
            bundle(imp['path'], imp['artifacts'])
    key_data = {'module':MODULE,'source':SOURCE,'compiler':fresh[0]['compiler_sha256'],'mathlib':fresh[0]['mathlib_commit'],'trust':0,'kernel_check':True,'imports':fresh[0]['direct_import_artifacts'],'native_runtime_digest':fresh[0]['native_runtime_digest'],'artifact_boundary':'olean-private-server-ilean-ir-native-v3'}
    strict_key = digest(json.dumps(key_data,sort_keys=True).encode())
    require(strict_key == '66ae958e71b9cd1d067b951d28ea3244b775120e281195ebf56a41d1a43a3c94' and Path(fresh[0]['cached_object']).parent.name == strict_key, 'independent canonical strict fresh cache key')
    for suffix, sha in fresh[0]['object_artifacts'].items():
        paths = [companion(x,suffix) for x in (R/f'attempts/00001-{MODULE}/{MODULE}.olean', Path(fresh[0]['cached_object']), TD/f'objects/{MODULE}.olean')]
        for p in paths:
            bind(p,sha)
            same_inode(paths[0],p)

    post_pin = pin(W/'POST-RUN-TRANSPORT-REHASH-20261011T014055.249073Z.json', '1b5b4731b6e6d2856b552f38a1ce9b83876bf627018404a221d3e48b5e893acd')
    post = load(post_pin['path'])
    require(post['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION' and post['final_receipt_sha256'] == final_pin['sha256'] and post['selected_modules_verified'] == len(post['records']) == 141 and post['original_staged_cache_files_rehashed'] == 300 and post['installed_companion_files_rehashed'] == post['installed_same_filesystem_hardlinks'] == 141 and post['installed_exdev_copies'] == 0 and not post['compiler_or_evaluator_invoked'] and not post['accepted_inputs_modified'], 'saved posttransport exact counts/scope')
    for row in post['records']:
        require(row['source_sha256'] == selected['modules'][row['module']]['sha256'], 'post actual source identity')
        pin(row['original_receipt'],row['original_receipt_sha256'])
        for role in ('original_object','staged_object','installed_object'):
            bundle(row[role],row['object_artifacts'])
        for suffix in row['object_artifacts']:
            same_inode(companion(Path(row['staged_object']),suffix),companion(Path(row['installed_object']),suffix))
    transport = load(W/'CACHE-TRANSPORT-PRE-USE-PLAN.json')
    require(len(transport['entries']) == 144 and not transport['compiler_launched'], '144 exact pre-use warm aliases incl four guards and qualified prefix')
    transport_count = 0
    for row in transport['entries']:
        require(modules[row['module']]['sha256']==row['source_sha256'],'pre-use exact current accepted or qualified-prefix source')
        for file in row['files']:
            pin(file['source'], file['sha256'])
            pin(file['destination'], file['sha256'])
            require(Path(file['source']).stat().st_size == file['bytes'], 'exact transport size')
            same_inode(file['source'],file['destination'])
            transport_count += 1
    require(transport_count == 300, 'all300 old artifact+receipt sameinode transports')
    actual_imports = load(TD/'ACTUAL-IMPORTED-ARTIFACTS.json')
    own_imports = [x for x in actual_imports if x['module'] in selected['modules']]
    require({x['module'] for x in own_imports} == set(selected['modules']), 'actual imported complete selected closure')
    for row in own_imports:
        bp = bind(row['path'],row['sha256'])
        require(bp['bytes'] == row['bytes'], 'actual imported selected full artifact bytes')

    runtime = load(R/'NATIVE-RUNTIME-PINS.json')
    native = []
    for path, row in runtime['libraries'].items():
        pp = pin(path,row['sha256'])
        s = Path(path).stat()
        require(pp['bytes'] == row['bytes'] and [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns] == row['stat_identity'], 'current full native byte/stat identity')
        native.append(pp)
    hashes = {k:v['sha256'] for k,v in runtime['libraries'].items()}
    final_native = load(R/'NATIVE-RUNTIME-FINAL-REHASH.json')
    require(len(native) == 28 and final_native['stable'] and final_native['hashes'] == hashes and digest(json.dumps(hashes,sort_keys=True).encode()) == runtime['native_runtime_digest'] == final['native_runtime_digest'], '28 native identities/digest actual initial/final/current')
    compiler_pin = pin(Path(fresh[0]['command'][0]),final['compiler_sha256'])
    captures = []
    for row in post['live_capture_records']:
        rec_pin = pin(row['receipt'],row['receipt_sha256'])
        rec = load(row['receipt'])
        attempt = Path(row['receipt']).parent
        descriptor_pin = pin(attempt/'STDERR-CAPTURE.json',row['descriptor_sha256'])
        cap = load(descriptor_pin['path'])
        require(cap == rec['stderr_storage'] and cap['complete'] and cap['eof'] and not cap['truncated'] and cap['reason'] is None and cap['exit_code'] == rec['exit_code'] == 0, 'complete live gzip frame actual exit0')
        gzip_pin = pin(attempt/'stderr.raw.gz',cap['gzip_sha256'])
        require(gzip_pin['path'] == cap['gzip_path'] and gzip_pin['bytes'] == cap['gzip_bytes'] == row['gzip_bytes'] and gzip_pin['bytes'] <= 1048576, 'encoded capture path/hash/bounds')
        raw = gzip.decompress(Path(gzip_pin['path']).read_bytes())
        require(digest(raw) == cap['raw_sha256'] == row['raw_sha256'] == rec['stderr_sha256'] and len(raw) == cap['raw_bytes'] == row['raw_bytes'] and len(raw) <= 33554432, 'full decoded gzip EOF/rawhash/size/bounds')
        require(not (attempt/'stderr').exists(), 'no separate raw live artifact claimed')
        names = re.findall(rb'calling init:\s*(\S+)',raw)
        resolved = {str(Path(n.decode()).resolve()) for n in names}
        require(len(names) == len(resolved) == 10 and resolved == set(row['initialized_libraries']) == set(rec['native_initialized_libraries']) and rec['native_initialized_libraries_bound'], '10 actual known initialized names')
        require(all(rec['native_initialized_libraries'][x] == runtime['libraries'][x] for x in resolved), 'all actual initialized native full identities')
        require(rec['native_loader_outputs'] == [{'path':gzip_pin['path'],'sha256':gzip_pin['sha256'],'encoding':'gzip','raw_sha256':digest(raw),'raw_bytes':len(raw)}], 'exact actual encoded/raw native evidence frame')
        stdout_pin = pin(attempt/'stdout',rec['stdout_sha256'])
        stdout = Path(stdout_pin['path']).read_text()
        require('sorryAx' not in stdout + raw.decode(errors='replace') and not re.search(r'^.*\.lean:\d+:\d+: error',stdout,re.M), 'full stdout/decoded stderr no sorry/diagnostic errors')
        require(rec['cap_memory_mib'] == 4096 and rec['cap_seconds'] == 180 and all(x in rec['command'] for x in ('-j1','-t0','-M4096','-Ddebug.skipKernelTC=false')) and rec['source_and_imports_stable'] and rec['native_runtime_stat_stable'], 'unchanged4GiB180s strict actual command/stability')
        source_pin = pin(attempt/('work/'+rec['module']+'.lean'),rec['source_sha256'])
        require(set(imported(Path(source_pin['path']).read_text())) == set(rec['direct_import_bindings']), 'literal fresh source/import set')
        for imp in rec['direct_import_bindings'].values():
            bundle(imp['path'],imp['artifacts'])
        if rec['kind'] == 'complete-owned-audit':
            require('object_artifacts' not in rec and rec['module'] == 'OwnedAudit' and result['audit_receipt'] == {**rec, 'audit_output':str(attempt/'work/AUDIT-RESULT.json')}, 'raw owned audit authenticated execution receipt plus exact target audit_output annotation only')
        else:
            bundle(attempt/(rec['module']+'.olean'),rec['object_artifacts'])
        axes = [{'name':n,'axioms': [v.strip() for v in a.split(',') if v.strip()]} for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",stdout,re.S)]
        if rec['module'] == MODULE:
            require(len(axes) == 8 and all(set(x['axioms']) == FOUNDATIONS for x in axes), 'eight actual authored theorem axiom prints')
        captures.append({'receipt':rec_pin,'descriptor':descriptor_pin,'gzip':gzip_pin,'decoded_bytes':len(raw),'decoded_sha256':digest(raw),'full_gzip_eof':True,'native_initialized_paths':sorted(resolved),'stdout':stdout_pin,'source':source_pin,'actual_axiom_prints':axes})
    require(len(captures) == post['live_capture_count'] == 3 and post['fresh_same_inode_attempt_cache_companions_verified'] == 1, '3 full captures, one fresh alias companion')

    storage_pin = pin(W/'scripts/storage_wrapper.py','d774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810')
    core_pin = pin(W/'scripts/build_connected.py','13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc')
    classes = {}
    for filename in ('storage_wrapper.py','build_with_authenticated_overlay.py','build_with_mathlib_overlay.py'):
        classes[filename] = {n.name:n for n in ast.walk(ast.parse((W/'scripts'/filename).read_text())) if isinstance(n,ast.ClassDef)}
    require([ast.unparse(x) for x in classes['storage_wrapper.py']['StorageBuilder'].bases] == ['parent','StorageInvocation'] and [ast.unparse(x) for x in classes['storage_wrapper.py']['StorageInvocation'].bases] == ['core.Builder'], 'exact nested frozen storage class bases')
    require([ast.unparse(x) for x in classes['build_with_authenticated_overlay.py']['OverlayBuilder'].bases] == ['original.OverlayBuilder'] and [ast.unparse(x) for x in classes['build_with_mathlib_overlay.py']['OverlayBuilder'].bases] == ['core.Builder'], 'exact frozen authenticated/namespace bases')
    mro = c3('StorageBuilder',{'StorageBuilder':['Auth','StorageInvocation'],'Auth':['Namespace'],'Namespace':['Core'],'StorageInvocation':['Core'],'Core':['object'],'object':[]})
    require(mro == ['StorageBuilder','Auth','Namespace','StorageInvocation','Core','object'], 'static same-core C3 preserves authenticated/namespace before storage/core')
    storage_composition = load(R/'COMPRESSED-STDERR-STORAGE-PINS.json')
    require(storage_composition['same_core_module_object'] and storage_composition['adapter_sha256'] == storage_pin['sha256'], 'actual same-core composition pins')
    plan = load(W/'RESOURCE-AND-RUN-PLAN.json')
    prep = load(W/'PREPARATION.json')
    policy_pins = [pin(plan['monitor_path'],'8a190dfa60b0151c1ad622fab21eefac866b44145a1d0d3665b31f66a1979a9b'), pin(plan['launcher'],'1ecc750032bbe5d0c44ae11dd1ca330db7e607a890c56b2a4c4516b202446b6c')]
    for row in prep['additional_storage_input_pins'].values():
        pin(row['path'],row['sha256'])
    equivalence = load(prep['runtime_parent_derivation']['path'])
    for role in ('namespace','authenticated'):
        old,new,rep = equivalence['accepted_'+role],equivalence['actual_'+role],equivalence[role+'_exact_replacement']
        pin(old['path'],old['sha256'])
        pin(new['path'],new['sha256'])
        a,b = Path(old['path']).read_text(),Path(new['path']).read_text()
        require(a.count(rep['old']) == rep['occurrences'] == 1 and a.replace(rep['old'],rep['new'],1) == b, 'entire actual parent sources only one exact hash literal differs')

    audit_pin = pin(R/'attempts/00003-OwnedAudit/work/AUDIT-RESULT.json','6df3d6c8f923bd4d0ee05af2bab474bbed334bf2184879aa5b0354458d217021')
    audit = load(audit_pin['path'])
    require(audit['selected_modules']==selected['order'] and not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules'] and audit['declaration_count']==len(audit['declarations'])==3486 and audit['theorem_declaration_count']==2293,'complete141 selected-owned audit zero missing/axiom gates')
    require(cert['targets'][TARGET]['audit_raw_sha256']==audit_pin['sha256'] and all(set(x['axioms'])<=FOUNDATIONS for x in audit['declarations']),'all3486 exact raw audit standard foundations')
    byname={x['name']:x for x in audit['declarations']};require(len(byname)==3486,'no duplicate names')
    raw_qc_pin=pin(W/'design-qc/natural141-raw-audit-20261011T0146Z-solver_design_recovery/NATURAL141-RAW-AUDIT-EXACT-CONTEXT-QC-ATTEMPT1.json','02338630bdf5f396a6451223c68d5859b198bf9e61e873e019bd2aee09bddc30')
    raw_qc=load(raw_qc_pin['path']);require(raw_qc['actual_raw_audit']==audit_pin and raw_qc['status']=='PASS_SAVED_RAW_141_AUDIT_EXACT_13_CONTEXT_RECORD_QUALIFICATION','bind independently recomputed parent1504+parallel117 exact raw audit comparison')
    for key in ('authored_new_records','unique_generated_new_records','already_accepted_parallel24_records_literal_match'):
        require(all(byname[x['name']]==x for x in raw_qc[key]),'all exact new/authored/generated/separateaccepted records match independently frozen raw qualification')
    require(raw_qc['counts']['unique_new_source_names']==45 and raw_qc['counts']['unique_new_theorems']==32 and raw_qc['counts']['new_source_owner_labeled_records']==48 and raw_qc['counts']['qualified_exact_context_differences']==13 and raw_qc['SourceCalendar_calendarTail_eq_def_literal_parent_match'],'unique new45 vs48ownerlabels and exact13 context fields')
    prefix_component=next(x for x in components if x['module']=='G6OriginalCommonPrefix')
    prefix_key=Path(prefix_component['cached_object']).parent.name
    require(prefix_key=='54ae5d6ce3d15200690415bbd1279d656cc4bfd4afa654a9d4a8f01f81bb95a9' and not prefix_component['receipt_directory'].startswith(str(R)+'/'),'authenticated a080 key54ae reused, not currentfresh')
    prefix_provenance_pin=pin(P/cert['partial_prefix_component_only_provenance']['path'],cert['partial_prefix_component_only_provenance']['sha256']) if not Path(cert['partial_prefix_component_only_provenance']['path']).is_absolute() else pin(cert['partial_prefix_component_only_provenance']['path'],cert['partial_prefix_component_only_provenance']['sha256'])
    guard_dir = next((E/'resource-guard').iterdir())
    guard_pin = pin(guard_dir/'RECEIPT.json')
    guard = load(guard_pin['path'])
    require(guard['status'] == 'PASS_UNCHANGED_BUILDER_EXIT_ZERO' and guard['exit_code'] == 0 and guard['abort_reason'] is None and guard['monitor_error'] is None and not guard['resource_caps_kernel_flags_core_or_audit_changed'], 'actual unchanged guard successful exit/noabort')
    require(guard['config_sha256'] == pin(W/'RESOURCE-AND-RUN-PLAN.json')['sha256'] and guard['monitor_sha256'] == policy_pins[0]['sha256'] and guard['peak_distinct_inode_allocation_bytes'] < plan['scratch_abort_bytes'] < plan['scratch_hard_limit_bytes'] and guard['peak_nonreclaimable_estimate_bytes'] < plan['memory_abort_bytes'], 'actual guard exact config and measured resource bounds')
    host=Path('/dev/shm/rc-lean-g6-natural-common-20261011T005738.287542Z/scripts')
    helper_pins=[pin(P/'lean/scripts/verify_g6_natural_common_transport_20261011.py','d74d11428f6e5fd74771cdad322d7c9b4fa260c467820b8555093570003427fe'),pin(host/'preserve_g6_natural_common_20261011_v3_shmem_metadata.py','cb9826d672dde47dd4beb8fa5f739a1d365d06c416ccf38737859a46c3217b04'),pin(host/'summarize_g6_natural_common_factorization_20261011_v3_shmem_metadata.py',cert['summarizer_sha256']),pin(host/'evidence_distribution.py','6eeadde07ef3ffe6f77b0d71101c683742c32fedf93fea396ae02edf66cd5201')]
    require(sum(p.stat().st_size for p in E.rglob('*') if p.is_file())==4672092,'all73 actual file byte total')
    return {'status':'PASS_SAVED_NATURAL141_KERNEL_AGGREGATE_COMPLETE_OWNED_AUDIT_AND_EXACT_CONTEXT_QUALIFICATION','manifest':manifest_pin,'certificate':cert_pin,'final_receipt':final_pin,'graph':graph_pin,'frozen_source':freeze_pin,'prior_static_preparation_gates':refs,'preservation':{'rows':71,'fixed_files':73,'gzip_rows':17,'payload_bytes_before_preservation_manifest':4630159,'all73_file_bytes':4672092,'packet_distribution_complete_at_run':False,'all_export_original_raw_bytes_compared':True,'files':preserved},'source_and_execution_counts':{'selected_executable':141,'staged':145,'accepted_source_parents':139,'accepted1504':138,'separateaccepted_f40':1,'qualified_prefix_reused':1,'fresh_factor':1,'reused_components':140,'new_source_versions':2,'fresh_aggregate':1,'fresh_owned_audit':1,'protected_guard_only':4},'transport':{'postreport':post_pin,'pre_use_files_rehashed':300,'selected_post_records':141,'installed_companions':141,'fresh_strict_cache_key':strict_key,'qualified_prefix_key':prefix_key,'all_fresh_attempt_cache_install_companions_same_inode':True,'actual_imported_selected_records_rehashed':len(own_imports),'unique_compiled_paths_rehashed':len(compiled)},'compiler':compiler_pin,'native_current28':native,'live_captures':captures,'storage':storage_pin,'core':core_pin,'static_C3':mro,'policy_pins':policy_pins,'helper_source_pins':helper_pins,'audit':{'raw':audit_pin,'declarations':3486,'theorems':2293,'exact_parent_and_new_name_comparison':raw_qc_pin,**raw_qc['counts'],'exact13_inherited_differences':raw_qc['exact_inherited_differences'],'all_inherited_kind_type_reference_and_axiom_fields_equal':True,'all24_separateaccepted_f40_records_literal_equal':True,'no_generic_metadata_normalization':True},'qualified_prefix_provenance':prefix_provenance_pin,'guard':guard_pin,'scope':['Separate141 module local natural original COMMON full-forest/register factor and literal before-node/tied-prefix no-read consumer. Original private seed marginalized once, full erased initialized Code plus every endpoint retained as arbitrary Old, original gamma orientation and actual stored selector support.', 'All live owners at original hybrid, positive full-arm exposures, original ordered parent/physical edge identity and arbitrary carried full forest/register remain explicit. Positive minimum baseline plus residual0 identity; no fixed-Code fresh Bernoulli mixture.', 'Exactly45 genuinely new unique names (14prefix+31factor),32theorems13definitions;48ownerlabels include3 inherited finalDate heads. Exact13 inherited context differences separately proven,24 f40 names already accepted117. No1504 metadata retention/coherent union promotion.', 'Actual whole physical calendar-word/exit/context, proper outside panels, future no-read, CutRefines/wordBinContract, calibrated observational decoder, positive biological graph/approximation and G4 scalar-word hq interfaces remain separate. No timed/metric/native universal refinement/source provenance/master claim.', 'All earlier failed versions and complete captures retained; qualified prefix currentreuse is not currentfresh. Fresh factor/aggregate/full141 audit all strict4GiB180s/j1t0/trust0.', 'Saved bytes/AST only; no producer/compiler/helper/guard/Builder/evaluator import or invocation. Root formal scoped acceptance remains separate.']}

def main():
    report = {'schema':'natural141_independent_saved_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':pin(__file__)['sha256'],'target_modules_imported_or_producer_processes_started':0,'mathematical_acceptance_modified':False}
    try:
        report.update(check())
    except Exception as e:
        report.update(status='FAIL_SAVED_NATURAL141_QC',error_type=type(e).__name__,error=str(e))
    out = Path(sys.argv[1])
    with out.open('x') as f:
        json.dump(report,f,indent=2,sort_keys=True)
        f.write('\n')
    print(json.dumps({'path':str(out),'status':report['status'],'sha256':pin(out)['sha256']}))
    return int(report['status'].startswith('FAIL'))

if __name__ == '__main__':
    raise SystemExit(main())
