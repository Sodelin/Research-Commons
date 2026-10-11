"""Read-only identities for the new G3/G4 packets and saved accepted1504.

Only stdlib byte/JSON/Git-object inspection runs.  No Lean, mathematical
checker, native solver, series checker, or prospective audit is invoked.
The large existing audit is streamed through a pinned byte-span helper.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
import types
from urllib.parse import urlsplit


ROOT = Path('/workspace/Research-Commons')
PACKET = ROOT / 'research/2026-10-10-codex-lean-rust-parity'
G3 = ROOT / 'research/2026-10-10-dot-g3-finite-residue-source-lift-2340z'
G4 = ROOT / 'research/2026-10-10-dot-g4-formalization-map-2345z'
STAGE = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z')
GRAPH = STAGE / 'DEPENDENCY-GRAPH.json'
AUDIT = STAGE / '.build/runs/20261010T223805.816906Z/attempts/00002-OwnedAudit/work/AUDIT-RESULT.json'
CERTIFICATE = PACKET / 'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json'
HELPER = PACKET / 'rust/audit_copy_literal_codec.py'
HELPER_SHA = 'cdb613eab954437ea47a441f5bd0e2bfdddb98e835a7ed1cd21559056f54257c'
COMMIT_PREFIX = 'b90ed33bb'
MEMORY_CAP = 256 * 1024 * 1024
SMALL_FILE_CAP = 4 * 1024 * 1024
SOURCE_CAP = 2 * 1024 * 1024
AUDIT_CAP = 128 * 1024 * 1024
RESERVE = 8 * 1024 * 1024
NAME = re.compile(rb'^\s*"name":\s*("(?:\\.|[^"\\])*")', re.M)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode('ascii') + b'\0' + raw).hexdigest()


def bounded(path, cap=SMALL_FILE_CAP):
    require(path.is_file() and path.stat().st_size <= cap, f'file cap/shape: {path}')
    with path.open('rb') as handle:
        raw = handle.read(cap + 1)
    require(len(raw) <= cap, f'file grew: {path}')
    return raw


def file_pin(path, raw=None):
    if raw is None:
        raw = bounded(path)
    return {'path': str(path), 'bytes': len(raw), 'sha256': sha(raw)}


def git(*args):
    return subprocess.check_output(['git', '-c', 'core.packedGitWindowSize=8m',
                                    '-c', 'core.packedGitLimit=32m', *args],
                                   cwd=ROOT, timeout=15)


def git_bytes(object_name, cap=SOURCE_CAP):
    length = int(git('cat-file', '-s', object_name))
    require(0 <= length <= cap, f'Git object cap: {object_name}')
    raw = git('cat-file', 'blob', object_name)
    require(len(raw) == length, f'Git length: {object_name}')
    return raw


def committed_pin(path, commit, expected_sha=None, expected_blob=None, expected_size=None):
    raw = bounded(path)
    relative = path.relative_to(ROOT).as_posix()
    saved = git_bytes(f'{commit}:{relative}', SMALL_FILE_CAP)
    require(raw == saved, f'current versus fixed commit: {relative}')
    observed_sha, observed_blob = sha(raw), blob(raw)
    if expected_sha is not None:
        require(observed_sha == expected_sha, f'SHA: {relative}')
    if expected_blob is not None:
        require(observed_blob == expected_blob, f'Git blob: {relative}')
    if expected_size is not None:
        require(len(raw) == expected_size, f'length: {relative}')
    return {**file_pin(path, raw), 'git_commit': commit, 'git_blob': observed_blob,
            'current_equals_committed_blob': True}


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f'duplicate JSON field: {key}')
        result[key] = value
    return result


def load(raw):
    return json.loads(raw, object_pairs_hook=unique)


def inspect():
    started = time.monotonic()
    commit = git('rev-parse', COMMIT_PREFIX).decode('ascii').strip()
    require(re.fullmatch(r'[0-9a-f]{40}', commit) is not None and commit.startswith(COMMIT_PREFIX),
            'fixed commit resolution')

    g3_raw = bounded(G3 / 'MANIFEST.json')
    g3 = load(g3_raw)
    require(len(g3['files']) == 7, 'G3 manifest count')
    require(len({entry['path'] for entry in g3['files']}) == 7, 'G3 distinct entries')
    g3_pins = [committed_pin(G3 / 'MANIFEST.json', commit)]
    for entry in g3['files']:
        require(Path(entry['path']).name == entry['path'], 'G3 relative filename')
        g3_pins.append(committed_pin(G3 / entry['path'], commit, entry['sha256'],
                                     entry['git_blob'], entry['bytes']))

    g4_manifest = bounded(G4 / 'MANIFEST.sha256')
    lines = g4_manifest.decode('ascii').splitlines()
    require(len(lines) == 5, 'G4 manifest count')
    g4_pins = [committed_pin(G4 / 'MANIFEST.sha256', commit)]
    manifest_names = set()
    for line in lines:
        match = re.fullmatch(r'([0-9a-f]{64})  ([^ /]+)', line)
        require(match is not None, 'G4 manifest row')
        expected, name = match.groups()
        require(name not in manifest_names, 'G4 duplicate manifest row')
        manifest_names.add(name)
        g4_pins.append(committed_pin(G4 / name, commit, expected))

    ledger_raw = bounded(G4 / 'FORMAL-PROVIDER-PINS.json')
    ledger = load(ledger_raw)
    entries = ledger['declarations']
    require(len(entries) == 31 and len({e['declaration'] for e in entries}) == 31,
            '31 distinct declaration ledger entries')
    graph_raw = bounded(GRAPH)
    require(sha(graph_raw) == ledger['accepted1504_graph_sha256'], 'accepted graph SHA')
    graph = load(graph_raw)
    target = graph['targets']['current/connected']
    require(len(target['modules']) == 1504 and len(target['order']) == 1504,
            'accepted graph module counts')
    certificate_raw = bounded(CERTIFICATE)
    require(sha(certificate_raw) == ledger['accepted1504_certificate_sha256'],
            'accepted certificate SHA')
    certificate = load(certificate_raw)
    require(certificate['graph_sha256'] == sha(graph_raw), 'certificate graph binding')
    require(certificate['status'] == 'PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS',
            'certificate saved status')

    modules = {}
    declaration_sources = []
    for entry in entries:
        module = entry['module']
        graph_record = target['modules'][module]
        require(graph_record['module'] == module and graph_record['sha256'] == entry['source_sha256']
                and graph_record['imports'] == entry['imports'], f'graph source/imports: {module}')
        require(entry['source_store_filename'] == entry['source_sha256'] + '.lean',
                f'source-store name: {module}')
        require(entry['public_git_blob_api'].endswith('/' + entry['source_git_blob']),
                f'public Git blob URL: {module}')
        if module not in modules:
            source = bounded(STAGE / 'source-store' / entry['source_store_filename'], SOURCE_CAP)
            git_source = git_bytes(entry['source_git_blob'])
            require(source == git_source, f'saved source versus Git blob: {module}')
            require(sha(source) == entry['source_sha256'] and blob(source) == entry['source_git_blob'],
                    f'source identities: {module}')
            text = source.decode('utf-8')
            imports = []
            for match in re.finditer(r'^\s*import\s+([^\n]+)', text, re.M):
                imports.extend(match.group(1).split('--', 1)[0].split())
            require(imports == entry['imports'], f'actual source imports: {module}')
            modules[module] = {**file_pin(STAGE / 'source-store' / entry['source_store_filename'], source),
                               'module': module, 'git_blob': blob(source), 'imports': imports,
                               'saved_source_equals_git_blob': True,
                               'source_lines': text.splitlines()}
        source_lines = modules[module]['source_lines']
        line_number = entry['declaration_line']
        require(type(line_number) is int and 1 <= line_number <= len(source_lines),
                f'declaration line domain: {entry["declaration"]}')
        source_line = source_lines[line_number - 1]
        require(re.search(r'\btheorem\s+' + re.escape(entry['declaration'].split('.')[-1]) + r'\b',
                          source_line) is not None, f'declaration source line: {entry["declaration"]}')
        declaration_sources.append({'declaration': entry['declaration'], 'module': module,
                                    'declaration_line': line_number, 'source_line': source_line})
    for value in modules.values():
        value.pop('source_lines')

    helper_raw = bounded(HELPER)
    require(sha(helper_raw) == HELPER_SHA, 'stream span helper SHA')
    helper = types.ModuleType('g3_g4_saved_byte_span_helper')
    helper.__file__ = str(HELPER)
    sys.modules[helper.__name__] = helper
    exec(compile(helper_raw, str(HELPER), 'exec'), helper.__dict__)
    limits = helper.Limits()
    limits.validate()
    wanted = {entry['declaration']: entry for entry in entries}
    found = {}
    header, tail = bytearray(), bytearray()
    before_first_record = True
    digest = hashlib.sha256()
    byte_count, record_count, max_piece = 0, 0, 0
    require(AUDIT.is_file() and AUDIT.stat().st_size <= AUDIT_CAP, 'raw audit cap/shape')
    with AUDIT.open('rb') as handle:
        for kind, raw in helper.target_spans(handle, limits):
            digest.update(raw)
            byte_count += len(raw)
            max_piece = max(max_piece, len(raw))
            require(byte_count <= AUDIT_CAP, 'stream audit size')
            if kind == 'L':
                if before_first_record:
                    require(len(header) + len(raw) <= SOURCE_CAP, 'audit header cap')
                    header.extend(raw)
                else:
                    require(len(tail) + len(raw) <= SOURCE_CAP, 'audit gap/tail cap')
                    tail.extend(raw)
                continue
            before_first_record = False
            tail.clear()
            record_count += 1
            require(record_count <= limits.record_count, 'audit record count cap')
            name_match = NAME.search(raw)
            require(name_match is not None, f'audit record name field at record {record_count}')
            name = json.loads(name_match.group(1))
            if name in wanted:
                require(name not in found, f'duplicate selected audit name: {name}')
                row = load(raw)
                expected = wanted[name]
                require(set(row) == helper.RECORD_FIELDS, f'audit selected row shape: {name}')
                require(row['name'] == name and row['module'] == expected['module'],
                        f'audit selected name/module: {name}')
                require(row['kind'] == expected['accepted1504_inventory_kind'], f'audit kind: {name}')
                require(row['axioms'] == expected['accepted1504_inventory_axioms'], f'audit axioms: {name}')
                found[name] = {'declaration': name, 'module': row['module'], 'kind': row['kind'],
                               'axioms': row['axioms'], 'raw_record_bytes': len(raw),
                               'raw_record_sha256': sha(raw)}
    require(digest.hexdigest() == ledger['accepted1504_audit_sha256'], 'full streamed audit SHA')
    require(len(found) == len(wanted), 'every selected declaration found')
    declaration_start = bytes(header).rfind(b'"declarations"')
    require(declaration_start >= 0, 'audit declarations header')
    header_prefix = bytes(header[:declaration_start]).rstrip()
    require(header_prefix.endswith(b','), 'audit header comma')
    top = load(header_prefix[:-1] + b'\n}')
    tail_start = bytes(tail).find(b'"declaration_count"')
    require(tail_start >= 0, 'audit declaration count tail')
    footer = load(b'{' + bytes(tail[tail_start:]))
    require(record_count == footer['declaration_count'], 'stream count equals saved declaration count')
    require(set(top['selected_modules']) == set(target['modules']), 'audit selected modules equal graph')
    require(not top['owned_axioms'] and not top['nonstandard_axiom_rows'] and not top['missing_modules'],
            'saved owned/nonstandard/missing summaries')

    hand_raw = bounded(G4 / 'ADDITIONAL-HAND-PROVIDER-PINS.json')
    hand_entries = load(hand_raw)
    require(len(hand_entries) == 3, 'three hand references')
    hand_pins = []
    for entry in hand_entries:
        parts = urlsplit(entry['url']).path.split('/')
        require(parts[:4] == ['', 'Sodelin', 'Research-Commons', 'blob'] and len(parts) >= 7,
                'hand Git URL shape')
        pinned_commit, relative = parts[4], '/'.join(parts[5:])
        require(Path(relative).name == entry['path'], 'hand URL filename')
        hand_pins.append(committed_pin(ROOT / relative, pinned_commit, entry['sha256'],
                                        entry['git_blob']))

    return {
        'schema': 'g3_g4_static_identity_review_v1', 'status': 'PASS_STATIC_IDENTITIES_ONLY',
        'reviewed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'review_source': file_pin(Path(__file__)), 'fixed_new_package_commit': commit,
        'g3_manifest_files': 7, 'g3_manifest_and_files': g3_pins,
        'g3_saved_series_logs_are_identical':
            (G3 / 'check_residue_lift_series.log').read_bytes() ==
            (G3 / 'independent_series_replay.log').read_bytes(),
        'g4_sha_manifest_files': 5, 'g4_manifest_and_files': g4_pins,
        'accepted1504': {
            'graph': file_pin(GRAPH, graph_raw), 'graph_target': 'current/connected',
            'graph_module_count': len(target['modules']), 'original_graph_status': target['status'],
            'certificate': file_pin(CERTIFICATE, certificate_raw),
            'saved_certificate_status': certificate['status'],
            'original_ledger_commit': ledger['accepted1504_commit'],
            'audit': {'path': str(AUDIT), 'bytes': byte_count, 'sha256': digest.hexdigest(),
                      'streamed_record_count': record_count,
                      'saved_theorem_declaration_count': top['theorem_declaration_count'],
                      'selected_module_count': len(top['selected_modules']),
                      'saved_owned_axioms': top['owned_axioms'],
                      'saved_nonstandard_axiom_rows': top['nonstandard_axiom_rows'],
                      'saved_missing_modules': top['missing_modules'],
                      'maximum_piece_bytes': max_piece, 'raw_audit_copied': False},
            'span_helper': file_pin(HELPER, helper_raw),
            'source_module_count': len(modules), 'source_and_import_bindings': list(modules.values()),
            'source_declaration_lines': declaration_sources,
            'selected_declaration_count': len(found),
            'selected_audit_declarations': [found[entry['declaration']] for entry in entries]},
        'hand_reference_count': len(hand_pins), 'hand_references': hand_pins,
        'reported_preparation1568': {
            'graph_sha256': ledger['prepared_graph_sha256'],
            'module_count': ledger['prepared_graph_modules'],
            'exact_graph_located_or_authenticated': False,
            'unchanged_source_import_assertion_independently_checked': False,
            'status': 'REPORTED_PREPARATION_ONLY'},
        'execution_scope': {
            'only_byte_json_and_git_object_inspection': True, 'lean_compiler_called': False,
            'theorem_auditor_called': False, 'mathematical_checker_called': False,
            'series_checker_called': False, 'native_solver_called': False,
            'reference_provider_called': False, 'new_closure_or_audit_synthesized': False,
            'accepted_source_or_cache_modified': False, 'elf_copied': False},
        'limits': {'address_space_bytes': MEMORY_CAP, 'small_file_bytes': SMALL_FILE_CAP,
                   'source_or_record_bytes': SOURCE_CAP, 'audit_bytes': AUDIT_CAP,
                   'overlay_reserve_bytes': RESERVE},
        'observed': {'elapsed_seconds': time.monotonic() - started,
                     'peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},
        'scope_qualification':
            'Authenticates saved identities and inventory fields. Does not rerun Lean or prove '
            'a G3 cutoff/RCF witness, G4 global entry or inverse decoder, generic source '
            'closure, runtime refinement, or aggregate1568 acceptance.'}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_CAP, MEMORY_CAP))
    args.output.mkdir(parents=True, exist_ok=False)
    try:
        result = inspect()
    except Exception as error:
        result = {'schema': 'g3_g4_static_identity_review_v1', 'status': 'FAIL_PRESERVED',
                  'reviewed_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  'review_source': file_pin(Path(__file__)),
                  'error_type': type(error).__name__, 'error': str(error),
                  'no_mathematical_compiler_or_solver_process': True}
    raw = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True).encode('ascii') + b'\n'
    require(len(raw) <= SMALL_FILE_CAP, 'receipt size cap')
    require(__import__('shutil').disk_usage(args.output).free - len(raw) >= RESERVE,
            'overlay reserve before receipt')
    with (args.output / 'RECEIPT.json').open('xb') as handle:
        handle.write(raw)
    print(json.dumps({'status': result['status'], 'receipt_sha256': sha(raw),
                      'receipt_bytes': len(raw), 'receipt_path': str(args.output / 'RECEIPT.json')},
                     sort_keys=True))
    return 0 if result['status'] == 'PASS_STATIC_IDENTITIES_ONLY' else 1


if __name__ == '__main__':
    raise SystemExit(main())
