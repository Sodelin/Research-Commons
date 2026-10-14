#!/usr/bin/env python3
"""Derive a source-only full-query successor; never execute the resulting runner."""
import ast
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PRIOR = ROOT / 'research/2026-10-13-astra-follow-on-import-query-2355z/query_imports.py'
PRIOR_SHA = '1bbcc570d913793490d8bf3688a975ff7e9bfd2dfcab78ee383d922fe6087965'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def prepare():
    if digest(PRIOR) != PRIOR_SHA:
        raise ValueError('reviewed predecessor changed')
    old = PRIOR.read_text()
    source = old
    changes = []
    def replace(before, after):
        nonlocal source
        if source.count(before) != 1:
            raise ValueError('exact unique source replacement absent: ' + before[:100])
        source = source.replace(before, after)
        changes.append(dict(before=before, after=after))
    replace('MAX_QUERIES = 550', 'MAX_QUERIES = 2500')
    start = source.index('PINNED = {\n')
    end = source.index('\n\n\ndef sha(path):', start)
    selected = HERE / 'FULL-SOURCE-SELECTION.json'
    prefix = ROOT / 'research/2026-10-13-astra-follow-on-import-query-2355z/evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json'
    pins = {
        'HERE / \'FULL-SOURCE-SELECTION.json\'': digest(selected),
        'FOLLOW / \'generate_plan.py\'': '89a30e4bc048196b452a0f6be534d26913c66cc998c80ca63490d4426ad97854',
        'ROOT / \'research/2026-10-13-astra-unified-accepted-extension-2340z/SOURCE-CATALOG.json\'': '0298e842f71f3d3c318e4d16a6acb7f67cee2f6e80d92a6cbde44fa1a5a1093f',
        'ROOT / \'research/2026-10-12-dot-accepted-connected-union1613-1737z/DEPENDENCY-GRAPH.json\'': '768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13',
        'PREVIOUS / \'PACKET-MANIFEST.json\'': '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5',
        'PREVIOUS / \'build_mathlib_serial.py\'': '8838b18400dcb2129de366b4e95fa1c8bccdfb5295d119e6d04206b13468cf87',
        'PREVIOUS / \'guard.py\'': 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3',
        'SUPPORT / \'EXTERNAL-PLAN.json\'': 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10',
        'PREFIX_PLAN': digest(prefix),
        'MATERIALIZED / \'SOURCE-SELECTION.json\'': 'c9108a72e670961a9ddfb2a8cad283dfd10da6f9cc893c372c60f60e78b91fa3',
        'MATERIALIZED / \'lakefile.lean\'': '6317704a95e3d30284f1b2dca1d601aa28ee2ef5c05e7b87c0044f7fb8d5da89',
        'MATHLIB / \'lakefile.lean\'': '9618b4491ba2a0ce2edde2cd29a6ff12974ccec5b331773ad0ae679cbebbc857',
        'LEAN_BIN / \'lean\'': 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
    }
    replacement = "PREFIX_PLAN = ROOT / 'research/2026-10-13-astra-follow-on-import-query-2355z/evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json'\nPINNED = {\n" + ''.join('    '+path+': '+repr(value)+',\n' for path,value in pins.items()) + '}'
    source = source[:start] + replacement + source[end:]
    start = source.index('def authenticate_sources(headers):\n')
    end = source.index('\n\nclass Queries:', start)
    authentication = '''def authenticate_sources(headers):
    for path, expected in PINNED.items():
        if sha(path) != expected:
            raise ValueError('pinned input differs: ' + str(path))
    full = read(HERE / 'FULL-SOURCE-SELECTION.json')
    materialized = read(MATERIALIZED / 'SOURCE-SELECTION.json')
    selected = full['sources']
    if len(selected) != 1642 or full['library_source_count'] != 1641 or full['lake_configuration_source_count'] != 1:
        raise ValueError('full library/configuration source scope differs')
    names = [row['module'] for row in selected]
    if len(set(names)) != 1642 or names[:1613] != full['literal_baseline_order']:
        raise ValueError('full selected graph order or module identities differ')
    mapping = {}
    for row in selected:
        name = row['module']
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name):
            raise ValueError('unsupported module name')
        destination = name.replace('.', '/') + '.lean'
        source = MATERIALIZED / destination
        if row['destination'] != destination or materialized['sources'].get(destination) != row['sha256']:
            raise ValueError('materialized selection differs: ' + name)
        original_paths = [(ROOT / origin['path']) for origin in row['origins']]
        for path in [source, *original_paths]:
            body = path.read_bytes()
            blob = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\\0' + body).hexdigest()
            if (hashlib.sha256(body).hexdigest() != row['sha256'] or len(body) != row['bytes']
                    or blob != row['git_blob'] or headers.imports(path) != row['imports']):
                raise ValueError('literal source/header differs: ' + name)
        mapping[name] = dict(row, original_path=str(original_paths[0] if original_paths else source), source=str(source.resolve()))
    full['package_dependency_pins'] = read(PREFIX_PLAN)['dependencies']
    return full, selected, mapping
'''
    source = source[:start] + authentication + source[end:]
    replace("startswith('astra-follow-on-import-query-')", "startswith('astra-full-accepted-import-query-')")
    replace('astra-follow-on-import-query-* directory', 'astra-full-accepted-import-query-* directory')
    replace('schema=\'astra_follow_on_import_query_invocation_v1\'', 'schema=\'astra_full_accepted_import_query_invocation_v1\'')
    replace("old = read(SUPPORT / 'EXTERNAL-PLAN.json')", "old = read(PREFIX_PLAN)")
    replace("if len(old['modules']) != 3591:", "if len(old['modules']) != 3593:")
    replace("copy_new(SUPPORT / 'EXTERNAL-PLAN.json', output / 'PRESERVED-ACTIVE-PLAN.json')", "copy_new(PREFIX_PLAN, output / 'PRESERVED-QUERY-PREFIX-PLAN.json')\n        copy_new(SUPPORT / 'EXTERNAL-PLAN.json', output / 'UNCHANGED-ACTIVE-PLAN.json')")
    replace('if len(owned_mathlib) != 9:', 'if len(owned_mathlib) != 11:')
    replace("queries = Queries(output, headers, [MATERIALIZED, CORE_SOURCE, *repos])", "env['LEAN_SRC_PATH'] += os.pathsep + str(CORE_SOURCE / 'lake')\n        queries = Queries(output, headers, [MATERIALIZED, CORE_SOURCE, *repos])")
    replace("if name == 'Init' or name.startswith(('Lean.', 'Init.', 'Std.', 'Lake.')):\n                path = CORE_SOURCE / (name.replace('.', '/') + '.lean')", "if name in {'Init', 'Lean', 'Std', 'Lake'} or name.startswith(('Lean.', 'Init.', 'Std.', 'Lake.')):\n                base = CORE_SOURCE / 'lake' if name == 'Lake' or name.startswith('Lake.') else CORE_SOURCE\n                path = base / (name.replace('.', '/') + '.lean')")
    replace("if dep not in names and dep not in old_names and dep != 'Lean.Elab.Tactic.Omega':", "if (dep not in names and dep not in old_names and dep not in follow['direct_external_roots']):")
    start = source.index("        additions = read(FOLLOW / 'FOLLOW-ON-EXTERNAL-ROOTS.json')")
    end = source.index('\n        def recorded_check_output', start)
    source = source[:start] + '''        names = sorted(set(follow['new_mathlib_roots_outside_active_plan']) - old_names)
        additions = []
        for name in names:
            actual = serial.source_for(name, repos)
            record = dict(module=name, sha256=sha(actual))
            if name in owned and record['sha256'] != owned[name]['sha256']:
                raise ValueError('selected owned Mathlib body differs from official source')
            additions.append(record)
        save(output / 'NEW-EXTERNAL-ROOTS.json', dict(roots=additions, transitive_cost='UNQUERIED_AT_SELECTION'))
''' + source[end:]
    replace("schema='astra_follow_on_official_import_plan_v1'", "schema='astra_full_accepted_official_import_plan_v1'")
    replace('selected_sources=475, selected_owned_sources=469, selected_astra_sources=6,', 'selected_sources=1642, selected_library_sources=1641, selected_configuration_sources=1,\n             selected_baseline_sources=1613,')
    replace("previous_plan_sha256=PINNED[SUPPORT / 'EXTERNAL-PLAN.json'],", "previous_plan_sha256=PINNED[PREFIX_PLAN],\n             unchanged_active_plan_sha256=PINNED[SUPPORT / 'EXTERNAL-PLAN.json'],")
    ast.parse(source)
    with (HERE / 'query_imports.py').open('x') as handle:
        handle.write(source)
    with (HERE / 'PREDECESSOR-query_imports.py').open('x') as handle:
        handle.write(old)
    record = dict(schema='astra_full_query_source_successor_v1', status='SOURCE_ONLY_NOT_EXECUTED',
                  predecessor_sha256=PRIOR_SHA, source_sha256=digest(HERE / 'query_imports.py'),
                  selected_source_sha256=digest(selected), prior_query_plan_sha256=digest(prefix),
                  lexical_replacements=changes, larger_replacements=['exact pinned inputs', 'full source authentication', 'new external roots'],
                  source_ast_parse='PASS', import_queries=0, compilers=0, object_authentication=False)
    with (HERE / 'SOURCE-SUCCESSOR.json').open('x') as handle:
        json.dump(record, handle, indent=2);handle.write('\n')
    print(json.dumps({key:record[key] for key in ['status','source_sha256','prior_query_plan_sha256','import_queries','compilers']}))


if __name__ == '__main__':
    prepare()
