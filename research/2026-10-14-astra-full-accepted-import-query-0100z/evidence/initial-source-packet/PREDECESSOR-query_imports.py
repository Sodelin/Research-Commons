#!/usr/bin/env python3
"""Isolated serial official source-import queries; no compilation or object audit.

SOURCE-ONLY PREPARATION: this runner must be reviewed, then invoked by the sole
compiler owner under the unchanged resource guard. No work occurs on import.
"""
import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FOLLOW = ROOT / 'research/2026-10-13-astra-follow-on-dependency-plan-2305z'
PREVIOUS = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
MATERIALIZED = Path('/workspace/scratch/astra-unified-extension-sources-2340')
MATHLIB = Path('/workspace/scratch/astra-mathlib-0645')
LEAN_BIN = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin')
CORE_SOURCE = LEAN_BIN.parent / 'src/lean'
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
MATHLIB_PIN = '0df444a360eaa60ab8c11dca51a86af692955474'
MAX_QUERIES = 550
QUERY_WALL_SECONDS = 10
MAX_OUTPUT_BYTES = 4 * 1024**2
PINNED = {
    FOLLOW / 'PACKET-MANIFEST.json': 'db6b93770aa633f1f6a2adef805591c88dcbd42f02a74c0d39f4eaa61979c447',
    FOLLOW / 'FOLLOW-ON-DEPENDENCIES.json': 'e79e84a9e1ca36bfd10b76a39aa37331d82ab16f7e2a5ad1ef75eed0a48f180b',
    FOLLOW / 'FOLLOW-ON-EXTERNAL-ROOTS.json': 'c328a20ad50801902568ed8bfc9b66dfb9141b7b7a66cd250af4ec49d04d4bf1',
    FOLLOW / 'MATERIALIZATION-CONFIG.json': '5cef7db596cfcdf760e149140cfb06b7d52317268f8d66797d27c225ac722870',
    FOLLOW / 'generate_plan.py': '89a30e4bc048196b452a0f6be534d26913c66cc998c80ca63490d4426ad97854',
    PREVIOUS / 'PACKET-MANIFEST.json': '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5',
    PREVIOUS / 'build_mathlib_serial.py': '8838b18400dcb2129de366b4e95fa1c8bccdfb5295d119e6d04206b13468cf87',
    PREVIOUS / 'guard.py': 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3',
    SUPPORT / 'EXTERNAL-PLAN.json': 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10',
    MATERIALIZED / 'SOURCE-SELECTION.json': 'c9108a72e670961a9ddfb2a8cad283dfd10da6f9cc893c372c60f60e78b91fa3',
    MATERIALIZED / 'lakefile.lean': '6317704a95e3d30284f1b2dca1d601aa28ee2ef5c05e7b87c0044f7fb8d5da89',
    MATHLIB / 'lakefile.lean': '9618b4491ba2a0ce2edde2cd29a6ff12974ccec5b331773ad0ae679cbebbc857',
    LEAN_BIN / 'lean': COMPILER_SHA,
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def save(path, value):
    with Path(path).open('x') as handle:
        json.dump(value, handle, indent=2)
        handle.write('\n')
        handle.flush()
        os.fsync(handle.fileno())


def copy_new(source, target):
    with Path(target).open('xb') as handle:
        handle.write(Path(source).read_bytes())


def import_pinned(name, source):
    if sha(source) != PINNED[source]:
        raise ValueError('helper source differs: ' + str(source))
    spec = importlib.util.spec_from_file_location(name, source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    if sha(source) != PINNED[source]:
        raise ValueError('helper changed during import')
    return module


def pause_check():
    if (SUPPORT / 'PAUSE-BUILDS').exists() or (HERE / 'PAUSE-BUILDS').exists():
        raise RuntimeError('PAUSE-BUILDS present; no next official query')


def authenticate_sources(headers):
    for path, expected in PINNED.items():
        if sha(path) != expected:
            raise ValueError('pinned input differs: ' + str(path))
    follow = read(FOLLOW / 'FOLLOW-ON-DEPENDENCIES.json')
    materialized = read(MATERIALIZED / 'SOURCE-SELECTION.json')
    selected = follow['owned'] + follow['new_astra_sources']
    if len(follow['owned']) != 469 or len(follow['new_astra_sources']) != 6:
        raise ValueError('selected research/Astra source scope changed')
    names = [row['module'] for row in selected]
    if len(set(names)) != 475 or follow['owned_order'] != names[:469]:
        raise ValueError('selected graph order or module identities differ')
    mapping = {}
    for row in selected:
        name = row['module']
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name):
            raise ValueError('unsupported module name')
        destination = name.replace('.', '/') + '.lean'
        original = ROOT / row['path']
        source = MATERIALIZED / destination
        if row['destination'] != destination or materialized['sources'].get(destination) != row['sha256']:
            raise ValueError('materialized selection differs: ' + name)
        for path in (original, source):
            body = path.read_bytes()
            git_blob = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()
            if (hashlib.sha256(body).hexdigest() != row['sha256'] or len(body) != row['bytes']
                    or git_blob != row['git_blob'] or headers.imports(path) != row['imports']):
                raise ValueError('literal source/header differs: ' + name)
        mapping[name] = dict(row, original_path=str(original), source=str(source.resolve()))
    return follow, selected, mapping


class Queries:
    def __init__(self, output, headers, allowed_roots):
        self.output = output
        self.headers = headers
        self.allowed_roots = [root.resolve() for root in allowed_roots]
        self.rows = []
        self.route_equivalence_sha256 = None

    def execute(self, source, cwd, env, phase, expected_imports=None, expected_source_sha256=None):
        pause_check()
        source = Path(source).resolve()
        if not source.is_file() or not any(source.is_relative_to(root) for root in self.allowed_roots):
            raise ValueError('query source escaped authenticated roots')
        if len(self.rows) >= MAX_QUERIES:
            raise RuntimeError('bounded query budget exhausted; no closure conclusion')
        index = len(self.rows)
        directory = self.output / 'queries' / f'{index:04d}'
        directory.mkdir(parents=True, exist_ok=False)
        source_pin = sha(source)
        if expected_source_sha256 is not None and source_pin != expected_source_sha256:
            raise ValueError('query source differs from its selected exact body')
        source_copy = directory / 'source.lean'
        copy_new(source, source_copy)
        if sha(source_copy) != source_pin:
            raise ValueError('source changed while saving query copy')
        command = [str(LEAN_BIN / 'lean'), '-j', '1', '-s', '8192', '--src-deps', str(source)]
        request = dict(index=index, phase=phase, source=str(source), source_sha256=source_pin,
                       command=command, cwd=str(cwd), compiler_sha256=COMPILER_SHA,
                       environment={key: env[key] for key in ['LEAN_PATH', 'LEAN_SRC_PATH',
                           'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB', 'LEAN_IMPORT_WORKERS',
                           'MIMALLOC_ARENA_RESERVE', 'RAYON_NUM_THREADS']},
                       expected_imports=expected_imports, query_wall_seconds=QUERY_WALL_SECONDS,
                       route_equivalence_sha256=self.route_equivalence_sha256,
                       source_compilation_performed=False, object_authentication_performed=False)
        save(directory / 'REQUEST.json', request)
        start = time.monotonic()
        code = None
        error = None
        try:
            with (directory / 'stdout').open('xb') as stdout, (directory / 'stderr').open('xb') as stderr:
                completed = subprocess.run(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr,
                                           timeout=QUERY_WALL_SECONDS, check=False)
                code = completed.returncode
        except BaseException as caught:
            error = dict(type=type(caught).__name__, message=str(caught))
            raise
        finally:
            receipt = dict(request_sha256=sha(directory / 'REQUEST.json'), index=index, phase=phase,
                           source_sha256_before=source_pin, source_sha256_after=sha(source),
                           exit_code=code, error=error, seconds=time.monotonic() - start,
                           outputs={name: dict(bytes=(directory / name).stat().st_size,
                                             sha256=sha(directory / name))
                                    for name in ['stdout', 'stderr'] if (directory / name).exists()})
            save(directory / 'RECEIPT.json', receipt)
            self.rows.append(dict(index=index, phase=phase, source=str(source),
                                  source_sha256=source_pin,
                                  receipt_sha256=sha(directory / 'RECEIPT.json')))
        if code != 0 or receipt['source_sha256_after'] != source_pin:
            raise RuntimeError('official import query failed or source changed: ' + str(source))
        if any(value['bytes'] > MAX_OUTPUT_BYTES for value in receipt['outputs'].values()):
            raise RuntimeError('query output budget exceeded')
        text = (directory / 'stdout').read_text()
        if any(not Path(line).is_absolute() for line in text.splitlines() if line):
            raise ValueError('official query emitted a relative dependency path')
        imports = list(dict.fromkeys(str(Path(line).resolve()) for line in text.splitlines() if line))
        for path in imports:
            actual = Path(path)
            if not actual.is_file() or not any(actual.is_relative_to(root) for root in self.allowed_roots):
                raise ValueError('compiler-reported dependency escaped authenticated source roots')
        if expected_imports is not None and imports != expected_imports:
            raise ValueError('official import paths differ from selected literal header: ' + str(source))
        save(directory / 'IMPORTS.json', dict(imports=imports, literal_header=self.headers.imports(source),
              dependencies=[dict(path=path, sha256=sha(path)) for path in imports],
              only_source_resolution_verified=True, object_authentication_performed=False))
        print(json.dumps(dict(status='OFFICIAL_IMPORT_QUERY_PASS', index=index, phase=phase,
                              source=str(source), imports=len(imports))), flush=True)
        return text


def run(output):
    output = output.resolve()
    if (output.parent != Path('/workspace/scratch') or
            not output.name.startswith('astra-follow-on-import-query-') or output.exists()):
        raise ValueError('output must be a new direct /workspace/scratch/astra-follow-on-import-query-* directory')
    # Never permit output under a selected source/toolchain/active-state directory.
    excluded = [MATERIALIZED, MATHLIB, LEAN_BIN.parent,
                Path('/workspace/scratch/astra-support-external-0840'),
                Path('/workspace/scratch/astra-support-sources-0936')]
    if any(output.is_relative_to(path) for path in excluded):
        raise ValueError('output overlaps existing source, object or active state')
    for key, cap in [(resource.RLIMIT_AS, 6 * 1024**3), (resource.RLIMIT_CPU, 600),
                     (resource.RLIMIT_FSIZE, 1024**3)]:
        soft, hard = resource.getrlimit(key)
        if soft == resource.RLIM_INFINITY or hard == resource.RLIM_INFINITY or soft > cap or hard > cap:
            raise RuntimeError('run only under the reviewed finite outer guard')
    pause_check()
    output.mkdir(parents=True, exist_ok=False)
    save(output / 'INVOCATION.json', dict(schema='astra_follow_on_import_query_invocation_v1',
         started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), runner_sha256=sha(__file__),
         argv=sys.argv, selected_materialization=str(MATERIALIZED),
         pinned_inputs={str(path): value for path, value in PINNED.items()},
         max_queries=MAX_QUERIES, source_compilation_performed=False,
         active_plan_mutation=False, object_authentication_performed=False))
    queries = None
    try:
        # These two authenticated modules define functions and have __main__ guards.
        headers = import_pinned('frozen_followon_headers', FOLLOW / 'generate_plan.py')
        follow, selected, owned = authenticate_sources(headers)
        serial = import_pinned('frozen_external_helpers', PREVIOUS / 'build_mathlib_serial.py')
        repos, dependencies, env = serial.setup(MATHLIB, LEAN_BIN)
        if (serial.LEAN_SHA != COMPILER_SHA or serial.PIN != MATHLIB_PIN
                or dependencies != follow['package_dependency_pins']):
            raise ValueError('compiler/Mathlib/package dependency identity differs')
        old = read(SUPPORT / 'EXTERNAL-PLAN.json')
        if old['compiler_sha256'] != COMPILER_SHA or old['mathlib_pin'] != MATHLIB_PIN or old['dependencies'] != dependencies:
            raise ValueError('active source-plan toolchain/package pins differ')
        if len(old['modules']) != 3591:
            raise ValueError('active pinned source-plan scope differs')
        # These are source checks only. No .olean/.ir or compiler receipt is read.
        for row in old['modules']:
            if sha(row['source']) != row['source_sha256']:
                raise ValueError('preserved official source body changed: ' + row['module'])
        copy_new(SUPPORT / 'EXTERNAL-PLAN.json', output / 'PRESERVED-ACTIVE-PLAN.json')
        # Lean chooses a namespace root before resolving its full subpath. A
        # partial materialized Mathlib directory first would mask upstream's
        # remaining Mathlib source files. Route that namespace upstream ONLY
        # after proving equality of every selected owned Mathlib body.
        owned_mathlib = [row for row in selected if row['module'].startswith('Mathlib.')]
        if len(owned_mathlib) != 9:
            raise ValueError('selected owned Mathlib equivalence scope changed')
        routes = []
        for row in owned_mathlib:
            upstream = serial.source_for(row['module'], repos)
            original = Path(owned[row['module']]['original_path'])
            materialized = Path(owned[row['module']]['source'])
            if not (upstream.read_bytes() == materialized.read_bytes() == original.read_bytes()):
                raise ValueError('upstream routing would change a selected owned Mathlib body: ' + row['module'])
            if sha(upstream) != row['sha256'] or headers.imports(upstream) != row['imports']:
                raise ValueError('selected/upstream Mathlib header or source identity differs')
            routes.append(dict(module=row['module'], selected_sha256=row['sha256'],
                original=str(original), queried_materialized_source=str(materialized),
                import_provider=str(upstream.resolve()), upstream_sha256=sha(upstream),
                full_bytes_equal=True, same_selected_version=True,
                object_authentication_performed=False))
        save(output / 'ROUTE-EQUIVALENCE.json', dict(
            schema='astra_owned_mathlib_source_route_equivalence_v1',
            reason='complete upstream Mathlib namespace before the partial materialized namespace',
            routes=routes, original_owned_source_query_paths_preserved=True,
            research_namespaces='materialized selected provider; no upstream replacement',
            object_authentication_performed=False))
        queries = Queries(output, headers, [MATERIALIZED, CORE_SOURCE, *repos])
        queries.route_equivalence_sha256 = sha(output / 'ROUTE-EQUIVALENCE.json')
        owned_env = env.copy()
        owned_env['LEAN_SRC_PATH'] = os.pathsep.join([str(MATHLIB), str(MATERIALIZED),
            *[path for path in env['LEAN_SRC_PATH'].split(os.pathsep) if path != str(MATHLIB)]])
        upstream_objects = str(MATHLIB / '.lake/build/lib/lean')
        owned_env['LEAN_PATH'] = os.pathsep.join([upstream_objects,
            str(MATERIALIZED / '.lake/build/lib/lean'),
            *[path for path in env['LEAN_PATH'].split(os.pathsep) if path != upstream_objects]])

        def resolved(name):
            if name.startswith('Mathlib.'):
                return str(serial.source_for(name, repos).resolve())
            if name in owned:
                return owned[name]['source']
            if name == 'Init' or name.startswith(('Lean.', 'Init.', 'Std.', 'Lake.')):
                path = CORE_SOURCE / (name.replace('.', '/') + '.lean')
            else:
                path = serial.source_for(name, repos)
            if not path.is_file():
                raise ValueError('literal import has no authenticated provider: ' + name)
            return str(path.resolve())

        names = set(owned)
        old_names = {row['module'] for row in old['modules']}
        for row in selected:
            pause_check()
            source = Path(owned[row['module']]['source'])
            declared = row['imports']
            for dep in declared:
                if dep not in names and dep not in old_names and dep != 'Lean.Elab.Tactic.Omega':
                    raise ValueError('new direct external root requires explicit successor selection: ' + dep)
            has_prelude = bool(re.search(r'(?m)^\s*prelude\s*$', headers.uncomments(source.read_text())))
            expected = list(dict.fromkeys(resolved(name) for name in ([] if has_prelude else ['Init']) + declared))
            queries.execute(source, MATERIALIZED, owned_env, 'EXACT_OWNED_OR_ASTRA_SOURCE',
                            expected, row['sha256'])

        additions = read(FOLLOW / 'FOLLOW-ON-EXTERNAL-ROOTS.json')['official_additions_outside_active_plan']
        names = sorted(row['module'] for row in additions)
        if names != ['Mathlib.Algebra.MvPolynomial.Funext', 'Mathlib.Algebra.MvPolynomial.Polynomial']:
            raise ValueError('external extension roots differ from the exact two selected bodies')
        for row in additions:
            actual = serial.source_for(row['module'], repos)
            if sha(actual) != row['sha256'] or sha(actual) != owned[row['module']]['sha256']:
                raise ValueError('selected owned Mathlib body differs from official source')

        def recorded_check_output(command, *, cwd, env, text):
            if command[:6] != [str(LEAN_BIN / 'lean'), '-j', '1', '-s', '8192', '--src-deps'] or len(command) != 7 or text is not True or Path(cwd) != MATHLIB:
                raise ValueError('frozen helper requested an unsupported command')
            selected_pin = next((row['sha256'] for row in additions
                                 if serial.source_for(row['module'], repos).resolve() == Path(command[-1]).resolve()), None)
            return queries.execute(Path(command[-1]), MATHLIB, env, 'OFFICIAL_EXTERNAL_EXTENSION',
                                   expected_source_sha256=selected_pin)

        # Preserve frozen graph-walk/order/target rules while recording every
        # new official query. Only this imported module's subprocess reference
        # is replaced; no global subprocess function or active plan is changed.
        serial.subprocess = types.SimpleNamespace(check_output=recorded_check_output)
        serial.ROOTS = names
        expanded = serial.plan(MATHLIB, LEAN_BIN, repos, env, old['modules'])
        if expanded[:len(old['modules'])] != old['modules']:
            raise ValueError('preserved official source-plan prefix changed')
        external_queries = {row['source']: row for row in queries.rows
                            if row['phase'] == 'OFFICIAL_EXTERNAL_EXTENSION'}
        for row in expanded:
            if sha(row['source']) != row['source_sha256']:
                raise ValueError('external source changed before final plan: ' + row['module'])
        for row in expanded[len(old['modules']):]:
            if external_queries[row['source']]['source_sha256'] != row['source_sha256']:
                raise ValueError('new external row body differs from actual query body')
        authenticate_sources(headers)
        for path, expected in PINNED.items():
            if sha(path) != expected:
                raise ValueError('pinned input changed during queries: ' + str(path))
        result = dict(schema='astra_follow_on_official_import_plan_v1',
             status='OFFICIAL_IMPORT_QUERIES_ONLY_NO_SOURCE_COMPILATION',
             mathlib_pin=MATHLIB_PIN, compiler_sha256=COMPILER_SHA, dependencies=dependencies,
             roots=sorted(set(old['roots'] + names)), modules=expanded,
             selected_sources=475, selected_owned_sources=469, selected_astra_sources=6,
             new_external_roots=names, new_external_source_records=len(expanded) - len(old['modules']),
             previous_plan_sha256=PINNED[SUPPORT / 'EXTERNAL-PLAN.json'],
             previous_import_edges='AUTHENTICATED_REUSE_OF_PINNED_COMPILER_QUERY_PLAN',
             previous_source_records_authenticated=len(old['modules']),
             owned_mathlib_route_equivalence_sha256=queries.route_equivalence_sha256,
             object_paths='EXISTING_CANDIDATES_ONLY; NOT INSPECTED, AUTHENTICATED OR WRITTEN',
             source_compilation_performed=False, object_authentication_performed=False,
             active_plan_mutation=False, compiler_queries=queries.rows)
        save(output / 'EXTERNAL-PLAN.json', result)
        save(output / 'RESULT.json', dict(status=result['status'], plan_sha256=sha(output / 'EXTERNAL-PLAN.json'),
             actual_official_queries=len(queries.rows), source_compilation_performed=False,
             object_authentication_performed=False, active_plan_mutation=False))
        print(json.dumps(read(output / 'RESULT.json')), flush=True)
    except BaseException as error:
        save(output / 'FAILED.json', dict(status='INCOMPLETE_QUERY_EVIDENCE_NO_CLOSURE_CLAIM',
             error=dict(type=type(error).__name__, message=str(error)),
             captured_query_receipts=[] if queries is None else queries.rows,
             source_compilation_performed=False, object_authentication_performed=False,
             active_plan_mutation=False))
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    run(args.out)


if __name__ == '__main__':
    main()
