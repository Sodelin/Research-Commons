"""Read-only public Git/audit reconciliation; no Lean, build, or target replay."""
from pathlib import Path
import ast
import collections
import datetime
import gzip
import hashlib
import io
import json
import os
import re
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
ROOT = Path('/workspace/Research-Commons')
OUT = Path(__file__).parent
COMMIT = '3972858d5c896171f80d7bc5a32f3ed1e95a6583'
PRIOR = '6d54a4a66da5c1a57a199ea64c282a625c5c0bc6'
PACKET = 'research/2026-10-11-dot-accepted-connected-union1568-0133z'
BASE_GRAPH = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/DEPENDENCY-GRAPH.json')
BASE_AUDIT = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/.build/runs/20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json')
DELTA = Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/metadata/integration-source-identity-delta-1509-20261011T015156.237141Z/INTEGRATION-SOURCE-IDENTITY-DELTA.json')
PARSER = Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z/scripts/compare_natural141_owned_20261011_v2.py')
GIT = ['git', '-c', 'core.packedGitWindowSize=16m', '-c', 'core.packedGitLimit=64m', '-C', str(ROOT)]
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_pin(path):
    path = Path(path)
    h = hashlib.sha256()
    size = 0
    with path.open('rb') as f:
        while part := f.read(65536):
            size += len(part)
            h.update(part)
    return {'path': str(path), 'bytes': size, 'sha256': h.hexdigest()}


def git(*args):
    return subprocess.check_output(GIT + list(args), env=ENV)


def public(path):
    return git('show', COMMIT + ':' + PACKET + '/' + path)


def record_hash(row):
    return hashlib.sha256(json.dumps(row, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()).digest()


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


class HashedRaw(io.RawIOBase):
    def __init__(self, raw):
        self.raw = raw
        self.sha = hashlib.sha256()
        self.size = 0
        super().__init__()

    def readable(self):
        return True

    def readinto(self, target):
        data = self.raw.read(len(target))
        if not data:
            return 0
        self.sha.update(data)
        self.size += len(data)
        target[:len(data)] = data
        return len(data)

    def close(self):
        if not self.closed:
            self.raw.close()
        super().close()


class AuditInput:
    def __init__(self, raw, label):
        self.raw = raw
        self.label = label
        self.metadata = None

    def open(self, encoding):
        return io.TextIOWrapper(io.BufferedReader(self.raw, 65536), encoding=encoding)


def get_record_parser():
    source = PARSER.read_text()
    require(digest(source.encode()) == '163f91e0f3ba1a140b853989493908bf88d7da8ca0667026ad7fc570de630f4a', 'Existing parser source changed')
    tree = ast.parse(source)
    selected = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'records']
    require(len(selected) == 1, 'Existing record parser not uniquely found')
    record_node = selected[0]
    require(sum(isinstance(n, ast.Return) for n in ast.walk(record_node)) == 1, 'Record parser return shape changed')

    class ExposeMetadata(ast.NodeTransformer):
        def visit_Return(self, node):
            call = ast.Expr(ast.Call(func=ast.Name(id='_capture', ctx=ast.Load()), args=[ast.Name(id='p', ctx=ast.Load()), ast.Name(id='prefix', ctx=ast.Load()), ast.Name(id='tail', ctx=ast.Load())], keywords=[]))
            return [call, node]

    record_node = ExposeMetadata().visit(record_node)
    module = ast.fix_missing_locations(ast.Module(body=[record_node], type_ignores=[]))

    def capture(p, prefix, tail):
        p.metadata = json.loads(prefix + '"declarations":[]' + tail)

    namespace = {'json': json, 're': re, '_capture': capture}
    exec(compile(module, str(PARSER) + ':records-only-metadata-hook', 'exec'), namespace)
    return namespace['records']


def review():
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    source_pin = file_pin(__file__)
    base_graph_pin = file_pin(BASE_GRAPH)
    delta_pin = file_pin(DELTA)
    require(base_graph_pin['sha256'] == 'e05a87db2b34f42aada87a958f7ff9114c68a817458b5919f7ecac62386fbacd', 'Base graph pin mismatch')
    require(delta_pin['sha256'] == '242535f8d6748df81b5c376d5c3aa1ebe44e2cd4594f8099e240e2f4505a5e6d', 'Static five-source pin mismatch')
    graph_raw = public('DEPENDENCY-GRAPH.json')
    require(digest(graph_raw) == '1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825', 'New graph pin mismatch')
    graph = json.loads(graph_raw)
    current = graph['targets']['current/connected']
    modules = current['modules']
    base = json.loads(BASE_GRAPH.read_bytes())['targets']['current/connected']['modules']
    require(len(modules) == 1568 and len(base) == 1504, 'Graph module count mismatch')
    require(all(modules.get(k) == v for k, v in base.items()), 'Inherited source/import record difference')
    added = set(modules) - set(base)
    require(len(added) == 64, 'New G3 graph difference mismatch')
    delta = json.loads(DELTA.read_bytes())
    five = delta['genuinely_new_modules']
    require(len(five) == 5 and not any(x['module'] in modules for x in five), 'Later-five selection overlaps peer graph')
    combined = dict(modules)
    for item in five:
        require(file_pin(item['path'])['sha256'] == item['sha256'], 'Later source changed')
        require(Path(item['path']).stat().st_size == item['bytes'], 'Later source length mismatch')
        require(literal_imports(Path(item['path']).read_text()) == item['imports'], 'Later literal import mismatch')
        combined[item['module']] = {k: item[k] for k in ('module', 'sha256', 'imports')}
    order = list(current['order']) + list(delta['safe_new_only_topological_order'])
    require(len(order) == len(set(order)) == len(combined) == 1573, 'Combined static order mismatch')
    seen = set()
    for name in order:
        require(name in combined, 'Unknown combined-order module')
        require(all(parent not in combined or parent in seen for parent in combined[name]['imports']), 'Combined import graph is not topological')
        seen.add(name)

    manifest_raw = public('MANIFEST.json')
    manifest = json.loads(manifest_raw)
    expected = {item['path']: item for item in manifest['files']}
    require(len(expected) == len(manifest['files']) == 1621 and manifest['mathematical_sources'] == 1568, 'Manifest count mismatch')
    projections = json.loads(public('PUBLIC-PROJECTIONS.json'))
    projection_by_path = {item['public_path']: item for item in projections}
    require(len(projection_by_path) == len(projections) == 22, 'Projection path selection mismatch')
    tree = {}
    for item in git('ls-tree', '-r', '-z', COMMIT, '--', PACKET).split(b'\0'):
        if not item:
            continue
        fields, path = item.split(b'\t', 1)
        mode, kind, oid = fields.split()
        name = path.decode()[len(PACKET) + 1:]
        require(mode == b'100644' and kind == b'blob', 'Nonregular public artifact')
        tree[name] = oid.decode()
    require(set(tree) == set(expected) | {'MANIFEST.json'}, 'Manifest/tree selection mismatch')
    require(tree['MANIFEST.json'] == hashlib.sha1(('blob ' + str(len(manifest_raw)) + '\0').encode() + manifest_raw).hexdigest(), 'Manifest Git blob mismatch')
    for name, item in expected.items():
        require(tree[name] == item['git_blob'], 'Manifest tree blob mismatch')
    by_sha = {}
    for name, row in modules.items():
        by_sha.setdefault(row['sha256'], []).append(name)
    captured = {}
    part_bytes = {}
    source_imports_verified = set()
    projections_verified = set()
    payload_bytes = 0
    batch = subprocess.Popen(GIT + ['cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV)
    try:
        for name, item in expected.items():
            batch.stdin.write((item['git_blob'] + '\n').encode())
            batch.stdin.flush()
            header = batch.stdout.readline().decode().strip().split()
            require(len(header) == 3 and header[0] == item['git_blob'] and header[1] == 'blob', 'Public artifact Git header mismatch')
            size = int(header[2])
            require(size == item['bytes'] and size <= 8 * 2**20, 'Public artifact size mismatch/bound')
            body = batch.stdout.read(size)
            require(len(body) == size and batch.stdout.read(1) == b'\n', 'Truncated public artifact')
            require(digest(body) == item['sha256'], 'Public artifact SHA mismatch')
            require(hashlib.sha1(('blob ' + str(size) + '\0').encode() + body).hexdigest() == item['git_blob'], 'Public Git blob content mismatch')
            payload_bytes += size
            if name in projection_by_path:
                projection = projection_by_path[name]
                decoded = gzip.decompress(body) if name.endswith('.gz') else body
                require(len(decoded) == projection['projected_bytes'] and digest(decoded) == projection['projected_uncompressed_sha256'], 'Public operational projection decoded identity mismatch')
                if projection['exact_raw_public']:
                    require(len(decoded) == projection['raw_bytes'] and digest(decoded) == projection['raw_sha256'], 'Claimed exact raw public projection differs')
                projections_verified.add(name)
            if name.startswith('source-store/') and name.endswith('.lean'):
                sha = name.rsplit('/', 1)[1][:-5]
                require(digest(body) == sha and sha in by_sha, 'Source-store filename pin mismatch')
                imports = literal_imports(body.decode())
                for module in by_sha[sha]:
                    require(imports == modules[module]['imports'], 'Public source literal imports differ from graph: ' + module)
                    source_imports_verified.add(module)
            elif name.startswith('evidence/audit-parts/'):
                part_bytes[name] = body
            elif name in {'ACCEPTANCE.json', 'AUDIT-TRANSPORT.json', 'PUBLIC-PROJECTIONS.json', 'evidence/FINAL-RECEIPT.json.projected', 'evidence/POST-BUILD-VERIFICATION.json.projected', 'evidence/LAKE-TERMINAL.json.projected', 'evidence/INDEPENDENT-FINAL-REVIEW.projected.json.gz'}:
                captured[name] = body
        batch.stdin.close()
        stderr = batch.stderr.read()
        require(batch.wait() == 0 and not stderr, 'Read-only artifact batch failed')
    finally:
        if batch.poll() is None:
            batch.kill()
            batch.wait()
        for f in [batch.stdout, batch.stderr]:
            f.close()
    require(len(source_imports_verified) == 1568, 'Public source import coverage incomplete')
    require(len(projections_verified) == 22, 'Operational projection coverage incomplete')
    transport = json.loads(captured['AUDIT-TRANSPORT.json'])
    compressed_hash = hashlib.sha256()
    pieces = []
    part_pins = []
    for item in transport['parts']:
        body = part_bytes.pop(item['path'])
        require(len(body) == item['bytes'] and digest(body) == item['sha256'], 'Audit transport part binding mismatch')
        compressed_hash.update(body)
        pieces.append(body)
        part_pins.append(item)
    require(len(pieces) == 8 and not part_bytes, 'Audit transport selection mismatch')
    require(compressed_hash.hexdigest() == transport['gzip_sha256'] == 'ce96f4d2380cfeac0fe2c2becc30e18c6ac25b561708ad9478d125ebefac0f55', 'Concatenated audit gzip hash mismatch')
    gzip_bytes = b''.join(pieces)
    pieces.clear()
    records = get_record_parser()
    old_raw = HashedRaw(BASE_AUDIT.open('rb'))
    old_input = AuditInput(old_raw, 'accepted1504')
    inherited = {}
    old_kinds = collections.Counter()
    for row in records(old_input):
        require(row['name'] not in inherited, 'Duplicate original declaration')
        require(set(row['axioms']).issubset(STANDARD_AXIOMS) and row['kind'] != 'axiom', 'Original axiom scope mismatch')
        inherited[row['name']] = record_hash(row)
        old_kinds[row['kind']] += 1
    require(old_raw.sha.hexdigest() == '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813', 'Accepted original raw audit mismatch')
    require(len(inherited) == 100985 and old_kinds['theorem'] == 91690, 'Original audited count mismatch')
    require(set(old_input.metadata['selected_modules']) == set(base), 'Original selected-module metadata mismatch')
    raw = HashedRaw(gzip.GzipFile(fileobj=io.BytesIO(gzip_bytes), mode='rb'))
    new_input = AuditInput(raw, 'public1568')
    names = set()
    matched = set()
    kinds = collections.Counter()
    new_kinds = collections.Counter()
    additions = []
    for row in records(new_input):
        name = row['name']
        require(name not in names, 'Duplicate public declaration')
        names.add(name)
        require(row['module'] in modules, 'Audit owner outside selected graph')
        require(set(row['axioms']).issubset(STANDARD_AXIOMS) and row['kind'] != 'axiom', 'Public audit has nonstandard/owned axiom')
        kinds[row['kind']] += 1
        sha = record_hash(row)
        if name in inherited:
            require(inherited[name] == sha, 'Inherited full parsed record differs: ' + name)
            matched.add(name)
        else:
            require(row['module'] in added, 'New declaration owned outside added G3 modules')
            new_kinds[row['kind']] += 1
            additions.append({'name': name, 'module': row['module'], 'kind': row['kind'], 'full_parsed_record_sha256': sha.hex()})
    require(raw.sha.hexdigest() == transport['raw_sha256'] == 'ee29bc1196c22fb27dd024e8593b0208aba5f4195edbf4895871235ee6e42e53', 'Public full decompressed audit mismatch')
    require(len(names) == 101705 and kinds['theorem'] == 92153, 'Public owned declaration/theorem count mismatch')
    require(matched == set(inherited) and len(additions) == 720, 'Original declaration inventory not fully preserved')
    metadata = new_input.metadata
    require(metadata['declaration_count'] == 101705 and metadata['theorem_declaration_count'] == 92153, 'Audit metadata count mismatch')
    require(len(metadata['selected_modules']) == 1568 and len(set(metadata['selected_modules'])) == 1568 and set(metadata['selected_modules']) == set(modules), 'Public selected modules mismatch/duplicate')
    require(not metadata['owned_axioms'] and not metadata['nonstandard_axiom_rows'] and not metadata['missing_modules'], 'Public metadata mathematical gate mismatch')
    independent = json.loads(gzip.decompress(captured['evidence/INDEPENDENT-FINAL-REVIEW.projected.json.gz']))
    acceptance = json.loads(captured['ACCEPTANCE.json'])
    final = json.loads(captured['evidence/FINAL-RECEIPT.json.projected'])
    terminal = json.loads(captured['evidence/LAKE-TERMINAL.json.projected'])
    require(acceptance['status'] == 'ACCEPTED_EXACT_CONNECTED_1568_AFTER_INDEPENDENT_REVIEW', 'Final acceptance status mismatch')
    require(independent['status'] == 'PASS_INDEPENDENT_EXACT_1568_CONTEXT_REVIEW' and independent['audit_sha256'] == raw.sha.hexdigest(), 'Independent projected review mismatch')
    require(final['status'] == 'PASS_ALL_REQUESTED_TARGETS' and final['counts'] == {'cache_reuse': 70, 'fresh_components': 1498} and terminal['exit_code'] == 0, 'Terminal status/freshness mismatch')
    require(file_pin(BASE_GRAPH) == base_graph_pin and file_pin(DELTA) == delta_pin, 'Local static input changed')
    return {
        'schema': 'research_commons_public1568_readonly_saved_review_v1',
        'reader': '/root/rust_implementation',
        'status': 'PASS_PUBLIC_GRAPH_SOURCE_IMPORTS_FULL_AUDIT_AND_EXACT_1504_RECORD_RETENTION',
        'started_utc': started,
        'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source': source_pin,
        'previous_main': PRIOR,
        'new_main': COMMIT,
        'public_packet': PACKET,
        'public_graph_sha256': digest(graph_raw),
        'base_graph': base_graph_pin,
        'static_five_source_delta': delta_pin,
        'existing_record_parser': file_pin(PARSER),
        'parser_reuse_qualification': 'Only the frozen records function is extracted; its sole return receives a metadata-capture hook. Original top-level reviewer/producers are never imported or invoked.',
        'public_manifest': {'bytes': len(manifest_raw), 'sha256': digest(manifest_raw), 'files_verified': len(expected), 'payload_bytes_verified': payload_bytes},
        'all_1568_source_bytes_and_literal_imports_verified': True,
        'inherited_1504_source_sha_import_records_exact': True,
        'new_g3_module_count': 64,
        'new_g3_modules': sorted(added),
        'audit_transport_parts': part_pins,
        'concatenated_gzip_bytes': len(gzip_bytes),
        'concatenated_gzip_sha256': compressed_hash.hexdigest(),
        'public_audit_raw_bytes_streamed': raw.size,
        'public_audit_raw_sha256': raw.sha.hexdigest(),
        'public_owned_declarations': len(names),
        'public_theorem_rows': kinds['theorem'],
        'public_kind_counts': dict(kinds),
        'owned_axioms': [],
        'nonstandard_axiom_rows': [],
        'missing_modules': [],
        'duplicate_declaration_names': [],
        'accepted_base_audit': {'path': str(BASE_AUDIT), 'bytes_streamed': old_raw.size, 'sha256': old_raw.sha.hexdigest(), 'declarations': len(inherited), 'theorems': old_kinds['theorem']},
        'all_100985_inherited_full_parsed_records_equal': True,
        'record_equality_method': 'SHA256 of canonical JSON for every parsed field, including module, kind, ordered axiom/type-reference/body-reference lists; all original names matched exactly once.',
        'new_unique_declaration_count': len(additions),
        'new_unique_kind_counts': dict(new_kinds),
        'new_unique_declarations': additions,
        'terminal_acceptance_public_sha256': digest(captured['ACCEPTANCE.json']),
        'terminal_receipt_projected_sha256': digest(captured['evidence/FINAL-RECEIPT.json.projected']),
        'independent_review_projected_gzip_sha256': digest(captured['evidence/INDEPENDENT-FINAL-REVIEW.projected.json.gz']),
        'operational_public_projection_records': len(projections),
        'projection_identities_checked_against_manifest': len(projections_verified),
        'projection_identity_qualification': 'All 22 public decoded identities match their explicit projection map. Exact-raw entries additionally match raw pins; changed host-path projections do not authenticate unavailable original local operational or native payloads.',
        'fresh_components_in_peer_terminal_run': 1498,
        'authenticated_interrupted_run_components_in_peer_terminal_run': 70,
        'peer_freshness_verified_from_published_metadata_only': True,
        'peer_local_native_trace_or_companion_payloads_authenticated_by_this_reader': False,
        'later_five_sources': [{k: x[k] for k in ('module', 'path', 'bytes', 'sha256', 'imports')} for x in five],
        'compatible_combined_identity_set_count': 1573,
        'combined_source_import_DAG_static_only': True,
        'combined1573_graph_or_audit_materialized': False,
        'combined1573_kernel_acceptance_claimed': False,
        'public_or_native_practical_contracts_promoted': False,
        'general_G3_G4_or_G6_G7_master_closure_claimed': False,
        'compiler_mathematical_native_or_reference_producers_started': False,
        'Git_staging_fetch_index_or_reference_mutations': False,
        'raw_audit_artifact_materialized': False,
        'all_outputs_inside_existing_counted_forest_metadata': True,
        'reader_AS_cap_bytes': 256 * 2**20,
        'reader_observed_maxrss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }


if __name__ == '__main__':
    try:
        result = review()
        path = OUT / 'PUBLIC1568-SAVED-READONLY-REVIEW.json'
    except Exception as error:
        result = {'schema': 'research_commons_public1568_reader_failure_v1', 'status': 'READER_FAILURE_NO_ACCEPTANCE', 'source': file_pin(__file__), 'error': type(error).__name__, 'detail': str(error), 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'no_compiler_or_Git_mutation': True}
        path = OUT / 'PUBLIC1568-READER-ATTEMPT1-FAILURE.json'
        with path.open('x') as stream:
            json.dump(result, stream, sort_keys=True, indent=2)
            stream.write('\n')
        raise
    raw = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
    with path.open('xb') as stream:
        stream.write(raw)
    print(json.dumps({'path': str(path), 'bytes': len(raw), 'sha256': digest(raw), 'status': result['status'], 'owned_declarations': result['public_owned_declarations'], 'theorems': result['public_theorem_rows'], 'inherited_records': result['accepted_base_audit']['declarations'], 'static_combined': result['compatible_combined_identity_set_count'], 'maxrss_KiB': result['reader_observed_maxrss_KiB']}, sort_keys=True))
