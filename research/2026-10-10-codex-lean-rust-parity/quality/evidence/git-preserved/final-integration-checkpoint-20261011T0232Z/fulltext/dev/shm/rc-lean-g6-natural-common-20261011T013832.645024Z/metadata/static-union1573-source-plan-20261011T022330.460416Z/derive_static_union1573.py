"""Derive only static source metadata and import text; never import a Builder or Lean."""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import os
import re
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
ROOT = Path('/workspace/Research-Commons')
OUT = Path(__file__).parent
META_COMMIT = 'f8120b1e413b64303891f7f2f8007169856c03f3'
PEER_ORIGINAL_COMMIT = '3972858d5c896171f80d7bc5a32f3ed1e95a6583'
PACKET = 'research/2026-10-11-dot-accepted-connected-union1568-0133z'
LEAN = 'research/2026-10-10-codex-lean-rust-parity/lean'
HANDOFF_PATH = LEAN + '/FIVE-ACCEPTED-ADDITIONS-FOR-UNION1573-HANDOFF-20261011T0204Z.json'
HANDOFF_SHA = 'a8da11f75c80dffde842ac6f982a119dc32ca8188269aca90cb1339d39056f9d'
PEER_GRAPH_SHA = '1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825'
PEER_MANIFEST_SHA = '355515fdea8b7515511c24681edbb93b70daf35ff5be1c7cf4bfb6a802f9bb78'
ORIGINAL_MANIFEST_SHA = 'a907d14ad4a4f172feeba616e8190e51d898203c7e0ec3dcb7b98f24d255e139'
QC = Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/commons1568-readonly-review-20261011T0200Z/PUBLIC1568-SAVED-READONLY-REVIEW.json')
QC_SHA = 'dc9392e2b23e02b2cc5f8a6d9c2fedcec92f95a91fa9a5757020ccdf7a90a40b'
PARSER_SOURCE_SHA = '1e44d1acec98e30bfe2f6331f97415d11f9c8ba74918f202ed21c2a88db9f930'
NEW_ACCEPTANCES = {
 'G7OriginalFamilyCalendarNormalization': (LEAN + '/G7-ORIGINAL-FAMILY-CALENDAR-NORMALIZATION-168-ACCEPTANCE.json', 'ed59cc19b5faade4ab514459129e35de9c031236005ed67dd758438cb07c9c9b'),
 'G6OriginalParallelArmTransport': (LEAN + '/G6-ORIGINAL-PARALLEL-ARM-TRANSPORT-117-ACCEPTANCE.json', '3a97ebdad3974a0873e5a1d9f68757f3ecc87bdee1b2b3669be0c6a6eba3a48e'),
 'G6OriginalForestRegisterCompression': (LEAN + '/G6-FOREST-REGISTER-COMPRESSION-101-ACCEPTANCE-20261011T0109Z.json', 'c6fbef540c9dc2f6456c75cfe79c0b55a5a015f1b4d7f8a0f716233f6844c7ce'),
 'G6OriginalCommonPrefix': (LEAN + '/G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-ACCEPTANCE-20261011T0202Z.json', '4b38e92700caa3ec2bd853b119fb2aa90d5cbf49af71081a1e6cfbbbcd73514d'),
 'G6NaturalCommonForestFactorization': (LEAN + '/G6-NATURAL-COMMON-FOREST-FACTORIZATION-141-ACCEPTANCE-20261011T0202Z.json', '4b38e92700caa3ec2bd853b119fb2aa90d5cbf49af71081a1e6cfbbbcd73514d')
}
GIT = ['git', '-c', 'core.packedGitWindowSize=16m', '-c', 'core.packedGitLimit=64m', '-C', str(ROOT)]
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(body):
    return hashlib.sha256(body).hexdigest()


def canonical_sha(value):
    return sha(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode())


def git(*args):
    return subprocess.check_output(GIT + list(args), env=ENV)


def published(commit, name):
    return git('show', commit + ':' + PACKET + '/' + name)


def checked_file(path, expected):
    body = Path(path).read_bytes()
    require(sha(body) == expected, 'File pin differs: ' + str(path))
    return body


def tree_records(commit, prefix):
    records = {}
    for line in git('ls-tree', '-r', '-z', commit, '--', prefix).split(b'\0'):
        if not line:
            continue
        attrs, path = line.split(b'\t', 1)
        mode, kind, blob = attrs.decode().split()
        require(mode == '100644' and kind == 'blob', 'Nonregular source origin: ' + path.decode())
        records[path.decode()] = blob
    return records


def exact_git_source(path, expected_sha, expected_bytes, tree):
    if path in tree:
        blob = tree[path]
        commit = META_COMMIT
        ref = {'kind': 'commit', 'value': commit}
    else:
        lines = git('ls-files', '--stage', '--', path).decode().splitlines()
        require(len(lines) == 1, 'Missing unique index source: ' + path)
        attrs, indexed_path = lines[0].split('\t', 1)
        mode, blob, stage = attrs.split()
        require(mode == '100644' and stage == '0' and indexed_path == path, 'Nonregular/unmerged index origin: ' + path)
        ref = {'kind': 'regular_index_blob_snapshot', 'git_mode': mode, 'stage': 0, 'git_blob': blob}
    body = git('cat-file', 'blob', blob)
    require(len(body) == expected_bytes and sha(body) == expected_sha, 'Durable source pin differs: ' + path)
    return body, blob, ref


def literal_imports(text):
    """Remove nested Lean block/line comments before reading import lines."""
    out = []
    depth = 0
    i = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        else:
            out.append(text[i])
            if text[i] == '"':
                quoted = True
            i += 1
    require(depth == 0, 'Unclosed source block comment')
    imports = []
    for line in ''.join(out).splitlines():
        stripped = line.strip()
        if stripped.startswith('public '):
            stripped = stripped[7:].lstrip()
        if stripped.startswith('import '):
            imports.extend(stripped[7:].split())
    return imports



def write_json(name, value, limit):
    body = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
    require(len(body) <= limit, 'Static output exceeds attributed bound: ' + name)
    path = OUT / name
    with path.open('xb') as f:
        f.write(body)
    require(path.read_bytes() == body, 'Output readback differs: ' + name)
    return {'path': str(path), 'sha256': sha(body), 'bytes': len(body)}


def derive():
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    own = Path(__file__).read_bytes()
    graph_bytes = published(META_COMMIT, 'DEPENDENCY-GRAPH.json')
    require(sha(graph_bytes) == PEER_GRAPH_SHA, 'Peer graph identity differs')
    graph = json.loads(graph_bytes)
    peer = graph['targets']['current/connected']
    peer_modules = peer['modules']
    require(len(peer_modules) == 1568, 'Peer module count differs')
    handoff_bytes = checked_file(ROOT / HANDOFF_PATH, HANDOFF_SHA)
    handoff = json.loads(handoff_bytes)
    qc_bytes = checked_file(QC, QC_SHA)
    qc = json.loads(qc_bytes)
    require(qc['public_graph_sha256'] == PEER_GRAPH_SHA and qc['all_1568_source_bytes_and_literal_imports_verified'], 'Independent source gate differs')
    require(handoff['base_peer_graph_sha256'] == PEER_GRAPH_SHA, 'Handoff base differs')
    manifest_bytes = published(META_COMMIT, 'MANIFEST.json')
    require(sha(manifest_bytes) == PEER_MANIFEST_SHA, 'Latest public manifest differs')
    original_manifest_bytes = published(PEER_ORIGINAL_COMMIT, 'MANIFEST.json')
    require(sha(original_manifest_bytes) == ORIGINAL_MANIFEST_SHA, 'Original reviewed manifest differs')
    manifest = json.loads(manifest_bytes)
    original_manifest = json.loads(original_manifest_bytes)
    expected = {x['path']: x for x in manifest['files']}
    old_expected = {x['path']: x for x in original_manifest['files']}
    require(len(expected) == len(manifest['files']) and manifest['mathematical_sources'] == 1568, 'Manifest uniqueness/source count differs')
    acceptance_bytes = published(META_COMMIT, 'ACCEPTANCE.json')
    acceptance = json.loads(acceptance_bytes)
    require(acceptance['modules'] == 1568 and acceptance['graph_sha256'] == PEER_GRAPH_SHA, 'Parent public acceptance binding differs')
    require(acceptance['local_loader_payloads_public'] is False, 'Public native qualification unexpectedly differs')
    original_tree = tree_records(PEER_ORIGINAL_COMMIT, PACKET + '/source-store')
    latest_new_tree = tree_records(META_COMMIT, LEAN)
    require(len(handoff['sources']) == 5 and handoff['added_modules'] == 5, 'Five-source handoff differs')
    new_names = [x['module'] for x in handoff['sources']]
    require(new_names == handoff['safe_new_only_topological_order'] and len(set(new_names)) == 5, 'New source order/uniqueness differs')
    require(not set(new_names).intersection(peer_modules), 'New names overlap accepted peer modules')
    combined = dict(peer_modules)
    source_map = {}
    by_sha = collections.defaultdict(list)
    for name, row in peer_modules.items():
        require(row.get('module', name) == name and isinstance(row['imports'], list), 'Original module identity differs: ' + name)
        require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name), 'Import-only aggregate identifier invalid: ' + name)
        by_sha[row['sha256']].append(name)
    batch = subprocess.Popen(GIT + ['cat-file', '--batch'], env=ENV, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    checked_peer_bodies = 0
    try:
        for digest, names in sorted(by_sha.items()):
            file = 'source-store/' + digest + '.lean'
            require(file in expected and file in old_expected, 'Source-store origin missing: ' + file)
            current_pin = expected[file]
            old_pin = old_expected[file]
            require(current_pin['sha256'] == old_pin['sha256'] == digest and current_pin['bytes'] == old_pin['bytes'], 'Source-store old/new pin mismatch: ' + file)
            path = PACKET + '/' + file
            require(original_tree.get(path) == current_pin['git_blob'] == old_pin['git_blob'], 'Source Git origin differs: ' + file)
            blob = current_pin['git_blob']
            batch.stdin.write((blob + '\n').encode());batch.stdin.flush()
            info = batch.stdout.readline().decode().split()
            require(len(info) == 3 and info[0] == blob and info[1] == 'blob', 'Git source-object response differs')
            size = int(info[2]);require(size == current_pin['bytes'], 'Git source-object byte count differs')
            body = batch.stdout.read(size)
            require(len(body) == size and batch.stdout.read(1) == b'\n' and sha(body) == digest, 'Source byte hash/transport differs')
            imports = literal_imports(body.decode())
            for name in names:
                require(imports == peer_modules[name]['imports'], 'Source imports differ from accepted graph: ' + name)
                source_map[name] = {
                    'module': name, 'sha256': digest, 'bytes': size, 'literal_imports': imports,
                    'source_git_path': path, 'source_git_ref': {'kind': 'commit', 'value': PEER_ORIGINAL_COMMIT},
                    'git_blob': blob, 'git_mode': '100644',
                    'source_origin': {'kind': 'original_peer1568_public_source_store', 'source_metadata_git_commit': META_COMMIT, 'parent_graph_sha256': PEER_GRAPH_SHA, 'parent_target': 'current/connected', 'original_record_canonical_sha256': canonical_sha(peer_modules[name]), 'manifest_reuse_public_blob': current_pin.get('reuse_public_blob', False)},
                    'accepted_scope_origin': {'git_path': PACKET + '/ACCEPTANCE.json', 'git_ref': META_COMMIT, 'sha256': sha(acceptance_bytes), 'qualification': 'Original peer public acceptance scope; unavailable local native/loader/cache payloads are not authenticated or admitted by this static reader.'},
                    'body_hash_size_and_literal_imports_checked': True,
                    'combined1573_object_admission': 'NOT_PERFORMED'
                }
                checked_peer_bodies += 1
        batch.stdin.close()
        stderr = batch.stderr.read()
        require(batch.wait() == 0 and not stderr, 'Read-only source batch failed')
    finally:
        if batch.poll() is None:
            batch.kill();batch.wait()
        for stream in (batch.stdout, batch.stderr):
            stream.close()
        if batch.stdin and not batch.stdin.closed:
            batch.stdin.close()
    new_scope_pins = {}
    for x in handoff['sources']:
        name = x['module']
        body, blob, ref = exact_git_source(x['source_git_path'], x['sha256'], x['bytes'], latest_new_tree)
        imports = literal_imports(body.decode())
        require(imports == x['literal_imports'], 'New literal import pin differs: ' + name)
        combined[name] = {'module': name, 'sha256': x['sha256'], 'imports': list(imports)}
        scope_path, scope_sha = NEW_ACCEPTANCES[name]
        scope_bytes = checked_file(ROOT / scope_path, scope_sha)
        new_scope_pins[name] = {'source_git_path': scope_path, 'sha256': scope_sha, 'bytes': len(scope_bytes)}
        source_map[name] = {
            'module': name, 'sha256': x['sha256'], 'bytes': len(body), 'literal_imports': imports,
            'source_git_path': x['source_git_path'], 'source_git_ref': ref, 'git_blob': blob, 'git_mode': '100644',
            'source_origin': {'kind': 'separately_accepted_cloud_source', 'handoff_git_path': HANDOFF_PATH, 'handoff_sha256': HANDOFF_SHA, 'original_handoff_record': x},
            'accepted_scope_origin': {'source_git_path': scope_path, 'sha256': scope_sha, 'bytes': len(scope_bytes), 'qualification': 'Separate narrow context and exact premises only; cloud component native receipts cannot be relabelled as peer1573 current-context admission.'},
            'body_hash_size_and_literal_imports_checked': True,
            'combined1573_object_admission': 'NOT_PERFORMED'
        }
    order = list(peer['order']) + new_names
    roots = list(peer['roots']) + new_names
    require(len(combined) == len(source_map) == len(order) == len(set(order)) == 1573, 'Combined graph/module/source-map count differs')
    require(len(roots) == len(set(roots)) and all(x in combined for x in roots), 'Prospective root list differs')
    require(all(combined.get(name) == row for name, row in peer_modules.items()), 'Inherited module record changed')
    seen = set()
    internal_edges = 0
    externals = set()
    for name in order:
        require(name in combined, 'Order has unknown module: ' + name)
        for parent in combined[name]['imports']:
            if parent in combined:
                require(parent in seen, 'Topological violation: ' + name + ' imports ' + parent)
                internal_edges += 1
            else:
                externals.add(parent)
        seen.add(name)
    require(externals == set(peer['external_imports']), 'External dependency set changed')
    require(all(x.startswith(('Init.', 'Lean.', 'Mathlib.')) or x == 'Std' for x in externals), 'Undeclared external project import')
    reached = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        pending.extend(x for x in combined[name]['imports'] if x in combined)
    require(reached == set(combined), 'Prospective source/root closure is incomplete')
    inputs = {
        'peer_metadata_commit': META_COMMIT,
        'original_peer_public_source_commit': PEER_ORIGINAL_COMMIT,
        'peer_graph': {'source_git_path': PACKET + '/DEPENDENCY-GRAPH.json', 'sha256': PEER_GRAPH_SHA, 'bytes': len(graph_bytes), 'selected_target': 'current/connected'},
        'peer_latest_manifest': {'source_git_path': PACKET + '/MANIFEST.json', 'sha256': sha(manifest_bytes), 'bytes': len(manifest_bytes)},
        'peer_original_reviewed_manifest': {'source_git_path': PACKET + '/MANIFEST.json', 'git_ref': PEER_ORIGINAL_COMMIT, 'sha256': sha(original_manifest_bytes), 'bytes': len(original_manifest_bytes)},
        'peer_original_public_acceptance': {'source_git_path': PACKET + '/ACCEPTANCE.json', 'sha256': sha(acceptance_bytes), 'bytes': len(acceptance_bytes)},
        'five_source_handoff': {'source_git_path': HANDOFF_PATH, 'sha256': HANDOFF_SHA, 'bytes': len(handoff_bytes)},
        'independent_public_saved_source_gate': {'path': str(QC), 'sha256': QC_SHA, 'bytes': len(qc_bytes)},
        'source_parser_origin': {'source_sha256': PARSER_SOURCE_SHA, 'function': 'literal_imports', 'qualification': 'Exact pure source-import parser copied as text; original reviewer/Builder modules are not imported.'},
        'separate_new_scope_pins': new_scope_pins,
        'derivation_reader': {'path': str(Path(__file__)), 'sha256': sha(own), 'bytes': len(own)}
    }
    target = {'roots': roots, 'order': order, 'modules': combined, 'external_imports': sorted(externals)}
    derived_graph = {
        'schema': 'static_prospective_union1573_dependency_graph_v1',
        'status': 'STATIC_NOT_KERNEL_ACCEPTED',
        'created_utc': started,
        'contributor': 'Codex / lean_integration_successor',
        'source_inputs': inputs,
        'original_peer_graph_scope_retained_as_historical_metadata': graph['scope'],
        'original_other_targets_excluded_from_this_single_static_projection': [x for x in graph['targets'] if x != 'current/connected'],
        'targets': {'static/prospective1573': target},
        'counts': {'inherited_peer_modules': 1568, 'new_unique_source_versions': 5, 'prospective_modules': 1573, 'new_mathematical_source_bodies_or_repairs': 0, 'extra_guard_modules': 0, 'external_import_names': len(externals)},
        'scope': 'Derived source/DAG plan only. All original1568 module dictionaries and source/import tuples are retained exactly, plus five separately accepted source versions. No combined kernel, aggregate or owned audit has run; no declaration-count prediction, executable cache admission, runnable Lake/build context or master/native refinement is claimed.',
        'runnable_lake_setup_or_builder_context': False,
        'combined_kernel_or_owned_audit_acceptance': False
    }
    module_source_map = {
        'schema': 'static_prospective_union1573_module_source_map_v1',
        'status': 'STATIC_NOT_KERNEL_ACCEPTED',
        'created_utc': started,
        'contributor': 'Codex / lean_integration_successor',
        'source_inputs': inputs,
        'modules': source_map,
        'scope': 'Portable Git-relative source origins and original provenance. Names preserve the graph namespace; source-store files are hash-addressed bodies. No host source filename, Lake/module installation, compiled object or current native admission is inferred.',
        'module_count': 1573
    }
    graph_pin = write_json('STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json', derived_graph, 1536 * 1024)
    map_pin = write_json('STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json', module_source_map, 3 * 2**20)
    header = ('/-\nSTATIC_NOT_KERNEL_ACCEPTED\nContributor: Codex / lean_integration_successor\n'
              'Source plan: exact peer1568 graph1a82 plus five-source handoffa8da.\n'
              'This file contains imports only and is not a runnable Lake/build setup.\n'
              'No combined1573 kernel/aggregate/owned audit or native admission is claimed.\n-/\n')
    aggregate = (header + ''.join('import ' + x + '\n' for x in order)).encode()
    require(len(aggregate) <= 128 * 1024, 'Static import-only aggregate bound exceeded')
    aggregate_path = OUT / 'StaticProspectiveUnion1573Imports.lean'
    with aggregate_path.open('xb') as f:
        f.write(aggregate)
    require(aggregate_path.read_bytes() == aggregate, 'Aggregate text readback differs')
    require(literal_imports(aggregate.decode()) == order, 'Import-only aggregate sequence differs')
    aggregate_pin = {'path': str(aggregate_path), 'sha256': sha(aggregate), 'bytes': len(aggregate), 'import_count': 1573, 'declarations': 0}
    check = {
        'schema': 'static_prospective_union1573_complete_source_dag_validation_v1',
        'status': 'PASS_STATIC_NOT_KERNEL_ACCEPTED',
        'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'contributor': 'Codex / lean_integration_successor',
        'inputs': inputs,
        'outputs': {'dependency_graph': graph_pin, 'module_source_map': map_pin, 'import_only_aggregate': aggregate_pin},
        'checks': {
            'original1568_module_records_exact': True,
            'original1568_order_retained_as_prefix': order[:1568] == peer['order'],
            'original1451_root_entries_retained_as_prefix': roots[:len(peer['roots'])] == peer['roots'],
            'public_peer_bodies_sha_size_and_literal_imports_checked': checked_peer_bodies,
            'new_durable_git_bodies_sha_size_and_literal_imports_checked': len(new_names),
            'latest_and_original_source_manifest_sha_size_blob_identity_match': True,
            'new_unique_modules_against_peer_base': 5,
            'duplicate_or_conflicting_module_names': 0,
            'source_body_vs_graph_or_handoff_import_conflicts': 0,
            'complete_internal_DAG_topological_order_checked': True,
            'internal_import_edges': internal_edges,
            'root_reachable_source_closure': len(reached),
            'prospective_module_count': 1573,
            'external_imports_unchanged_from_peer': len(externals),
            'external_native_or_library_resolution_not_exercised': True,
            'original_record_module_fields_missing_in_peer_preserved_not_normalized': sum('module' not in x for x in peer_modules.values()),
            'new_G4_drafts_or_duplicate_G3_modules_added': 0,
            'aggregate_exact1573_imports_only_no_options_or_declarations': True,
            'no_decl_count_prediction': True
        },
        'storage': {'all_outputs_inside_existing_counted_WN_metadata': True, 'new_working_context': False, 'accepted_graphs_or_inputs_written_moved_or_deleted': False, 'source_bodies_copied_to_outputs': False, 'Git_index_or_reference_mutation': False},
        'execution': {'Lean_or_Builder_import': False, 'compiler_evaluator_native_or_audit_producer': False, 'compiled_cache_admission_or_artifact_stage': False, 'kernel_or_caps_policy_change': False},
        'remaining_gate': 'The peer integrator resolves/install-authenticates the exact source origins and current native/library context, checks the five components, then produces one fresh aggregate/full owned audit with exact inherited comparison. This static plan is not a Lake setup or combined proof acceptance.'
    }
    checked_file(ROOT / HANDOFF_PATH, HANDOFF_SHA)
    checked_file(QC, QC_SHA)
    require(published(META_COMMIT, 'DEPENDENCY-GRAPH.json') == graph_bytes, 'Parent graph post-read identity differs')
    validation_pin = write_json('STATIC-PROSPECTIVE-UNION1573-VALIDATION.json', check, 128 * 1024)
    handoff_record = {
        'schema': 'static_union1573_source_plan_handoff_v1', 'status': 'STATIC_NOT_KERNEL_ACCEPTED',
        'created_utc': check['created_utc'], 'contributor': 'Codex / lean_integration_successor',
        'outputs': {'graph': graph_pin, 'source_map': map_pin, 'import_only_aggregate': aggregate_pin, 'validation': validation_pin},
        'reader': inputs['derivation_reader'], 'base_graph_sha256': PEER_GRAPH_SHA, 'five_source_handoff_sha256': HANDOFF_SHA,
        'counts': {'base1568': 1568, 'five_unique': 5, 'prospective1573': 1573},
        'read_only_source_checks_completed': True, 'combined_kernel_aggregate_audit_executed': False,
        'scope': derived_graph['scope'],
        'first_class_source_origins': 'Original peer source-store Git paths at397285 and latest metadata atf812; exact five Git-relative source paths plus commit or regular index-blob provenance. All original module tuples retained. No accepted artifact or graph changes.',
        'next_action': check['remaining_gate']
    }
    handoff_pin = write_json('STATIC-PROSPECTIVE-UNION1573-FINAL-HANDOFF.json', handoff_record, 32 * 1024)
    print(json.dumps({'status': check['status'], 'directory': str(OUT), 'outputs': handoff_record['outputs'], 'handoff': handoff_pin, 'new_context_or_producer': False}, sort_keys=True))


if __name__ == '__main__':
    try:
        derive()
    except Exception as error:
        diagnostic = {'status': 'STATIC_DERIVATION_READER_FAILED_NO_KERNEL_EXECUTION', 'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'error_type': type(error).__name__, 'error': str(error), 'reader_sha256': sha(Path(__file__).read_bytes()), 'new_compiler_context_or_producer': False}
        path = OUT / ('STATIC-READER-FAILURE-' + datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ') + '.json')
        with path.open('x') as f:
            json.dump(diagnostic, f, indent=2, sort_keys=True);f.write('\n')
        raise
