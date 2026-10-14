#!/usr/bin/env python3
"""Prepare a literal full-package source inventory; no Lean/Lake/Git execution."""
import ast
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
MATERIALIZED = Path('/workspace/scratch/astra-unified-extension-sources-2340')
EXTENSION = ROOT / 'research/2026-10-13-astra-unified-accepted-extension-2340z'
BASE = ROOT / 'research/2026-10-12-dot-accepted-connected-union1613-1737z'
HEADERS = ROOT / 'research/2026-10-13-astra-follow-on-dependency-plan-2305z/generate_plan.py'
HEADER_SHA = '89a30e4bc048196b452a0f6be534d26913c66cc998c80ca63490d4426ad97854'
SELECTION_SHA = 'c9108a72e670961a9ddfb2a8cad283dfd10da6f9cc893c372c60f60e78b91fa3'
CATALOG_SHA = '0298e842f71f3d3c318e4d16a6acb7f67cee2f6e80d92a6cbde44fa1a5a1093f'
GRAPH_SHA = '768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def exact(path):
    data = path.read_bytes()
    return dict(path=str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
                bytes=len(data), sha256=hashlib.sha256(data).hexdigest(),
                git_blob=hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest())


def pinned_json(path, expected):
    if sha(path) != expected:
        raise ValueError('selected source/configuration changed: ' + str(path))
    return json.loads(path.read_text())


def header_functions():
    if sha(HEADERS) != HEADER_SHA:
        raise ValueError('source header parser changed')
    tree = ast.parse(HEADERS.read_text())
    functions = [node for node in tree.body if isinstance(node, ast.FunctionDef)
                 and node.name in {'uncomments', 'imports'}]
    if len(functions) != 2:
        raise ValueError('exact two header functions absent')
    scope = dict(re=re)
    exec(compile(ast.Module(body=functions, type_ignores=[]), str(HEADERS), 'exec'), scope)
    return scope['imports']


def prepare():
    selection = pinned_json(MATERIALIZED / 'SOURCE-SELECTION.json', SELECTION_SHA)
    catalog = pinned_json(EXTENSION / 'SOURCE-CATALOG.json', CATALOG_SHA)
    graph = pinned_json(BASE / 'DEPENDENCY-GRAPH.json', GRAPH_SHA)['targets']['current/connected']
    if selection['baseline']['modules'] != graph['modules'] or selection['baseline']['order'] != graph['order']:
        raise ValueError('literal baseline graph differs')
    if not selection['all_68_g2_retained'] or len(graph['modules']) != 1613:
        raise ValueError('baseline scope differs')
    imports = header_functions()
    origins = {}
    for name, row in graph['modules'].items():
        source = BASE / 'source-store' / (row['sha256'] + '.lean')
        origins[name] = [source]
        if sha(source) != row['sha256'] or imports(source) != row['imports']:
            raise ValueError('original accepted body/header differs: ' + name)
    for row in catalog['sources']:
        source = ROOT / row['path']
        if sha(source) != row['sha256'] or source.stat().st_size != row['bytes']:
            raise ValueError('extension body differs: ' + row['module'])
        origins.setdefault(row['module'], []).append(source)
    generated = {'Accepted1613', 'AstraUnified', 'lakefile'}
    all_names = {name[:-5].replace('/', '.') for name in selection['sources']}
    if len(all_names) != 1642 or all_names - set(origins) != generated:
        raise ValueError('full materialized source/configuration scope differs')
    recipes = {
        'Accepted1613': ''.join('import ' + name + '\n' for name in graph['roots']).encode(),
        'AstraUnified': b'import Accepted1613\nimport AstraKernel\n',
    }
    order = graph['order'] + sorted(all_names - set(graph['order']))
    rows = []
    for name in order:
        destination = name.replace('.', '/') + '.lean'
        source = MATERIALIZED / destination
        body = source.read_bytes()
        if sha(source) != selection['sources'][destination]:
            raise ValueError('materialized body differs: ' + name)
        literal_imports = imports(source)
        original = origins.get(name, [])
        for origin in original:
            if origin.read_bytes() != body or imports(origin) != literal_imports:
                raise ValueError('original/materialized exact body or imports differ: ' + name)
        if name in recipes and body != recipes[name]:
            raise ValueError('generated aggregate differs: ' + name)
        row = dict(exact(source), module=name, destination=destination, source=str(source),
                   imports=literal_imports, origins=[exact(path) for path in original],
                   kind='lake_configuration' if name == 'lakefile' else 'accepted1613' if name in graph['modules']
                        else 'generated_aggregate' if name in recipes else 'extension',
                   generated_provenance=None if original else dict(
                       materializer=str((EXTENSION / 'materialize_extension.py').relative_to(ROOT)),
                       materializer_sha256=sha(EXTENSION / 'materialize_extension.py'),
                       source_selection_sha256=SELECTION_SHA))
        rows.append(row)
    mathlib = [row for row in rows if row['module'].startswith('Mathlib.')]
    if len(mathlib) != 11:
        raise ValueError('selected owned Mathlib scope differs')
    external = sorted({dep for row in rows for dep in row['imports'] if dep not in all_names})
    old = json.loads((ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/EXTERNAL-PLAN.json').read_text())
    old_names = {row['module'] for row in old['modules']}
    extension_roots = sorted(({name for name in external if name.startswith('Mathlib.')} |
                              {row['module'] for row in mathlib}) - old_names)
    record = dict(schema='astra_full_accepted_query_source_selection_v1',
                  status='LITERAL_SOURCE_AND_HEADER_AUTHENTICATION_ONLY', sources=rows,
                  selected_source_count=len(rows), library_source_count=len(rows)-1,
                  lake_configuration_source_count=1, selected_mathlib_count=len(mathlib),
                  literal_baseline_order=graph['order'], direct_external_roots=external,
                  new_mathlib_roots_outside_active_plan=extension_roots,
                  prior_plan_sha256=sha(ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/EXTERNAL-PLAN.json'),
                  graph_sha256=GRAPH_SHA, materialized_selection_sha256=SELECTION_SHA,
                  source_catalog_sha256=CATALOG_SHA, header_parser_sha256=HEADER_SHA,
                  compiler_queries=0, lean_compilers=0, object_authentication=False,
                  active_plan_mutation=False, all_68_g2_retained=True)
    path = HERE / 'FULL-SOURCE-SELECTION.json'
    with path.open('x') as handle:
        json.dump(record, handle, indent=2)
        handle.write('\n')
    print(json.dumps(dict(status=record['status'], source_count=len(rows),
                         library_sources=len(rows)-1, selected_mathlib=len(mathlib),
                         new_mathlib_roots=extension_roots, selection_sha256=sha(path),
                         compiler_queries=0, lean_compilers=0)))


if __name__ == '__main__':
    prepare()
