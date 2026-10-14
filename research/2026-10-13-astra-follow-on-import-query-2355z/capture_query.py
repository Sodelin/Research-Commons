#!/usr/bin/env python3
"""Authenticate and preserve the closed v2 source-query run; never compile."""
import hashlib
import json
import importlib.util
import os
import re
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SCRATCH = Path('/workspace/scratch/astra-follow-on-import-query-2355-v2')
GUARDED = HERE / 'evidence/import-query-v2'
PAYLOAD = HERE / 'evidence/import-query-v2-authenticated'
OUTPUT = HERE / 'evidence/import-query-v3-authenticated'
RUNNER_SHA = '1bbcc570d913793490d8bf3688a975ff7e9bfd2dfcab78ee383d922fe6087965'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
PRIOR_SHA = 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10'
PYTHON = '/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3'
LEAN = '/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin/lean'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def check(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    check(not OUTPUT.exists(), 'exclusive capture already exists')
    check(sha(HERE / 'query_imports.py') == RUNNER_SHA, 'executed runner differs')
    check(sha(LEAN) == COMPILER_SHA, 'compiler differs')
    spec = importlib.util.spec_from_file_location('closed_query_provider', HERE / 'query_imports.py')
    query = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(query)
    headers = query.import_pinned('frozen_headers_for_capture', query.FOLLOW / 'generate_plan.py')
    follow, selected, owned = query.authenticate_sources(headers)
    serial = query.import_pinned('frozen_serial_for_capture', query.PREVIOUS / 'build_mathlib_serial.py')
    repos = [query.MATHLIB, *[query.MATHLIB / '.lake/packages' / r['name']
                            for r in follow['package_dependency_pins']]]
    base_env = dict(LEAN_PATH=os.pathsep.join(str(p / '.lake/build/lib/lean') for p in repos),
        LEAN_SRC_PATH=os.pathsep.join(map(str, [*repos, query.CORE_SOURCE])),
        LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='8192', LEAN_IMPORT_WORKERS='1',
        MIMALLOC_ARENA_RESERVE='16384', RAYON_NUM_THREADS='1')
    owned_env = dict(base_env,
        LEAN_PATH=os.pathsep.join([str(query.MATHLIB / '.lake/build/lib/lean'),
            str(query.MATERIALIZED / '.lake/build/lib/lean'),
            *[str(p / '.lake/build/lib/lean') for p in repos[1:]]]),
        LEAN_SRC_PATH=os.pathsep.join(map(str, [query.MATHLIB, query.MATERIALIZED,
                                             *repos[1:], query.CORE_SOURCE])))
    def resolved(name):
        if name.startswith('Mathlib.'):
            return str(serial.source_for(name, repos).resolve())
        if name in owned:
            return owned[name]['source']
        if name == 'Init' or name.startswith(('Lean.', 'Init.', 'Std.', 'Lake.')):
            return str((query.CORE_SOURCE / (name.replace('.', '/') + '.lean')).resolve())
        return str(serial.source_for(name, repos).resolve())

    guard = read(GUARDED / 'RECEIPT.json')
    check(guard['runner_sha256'] == GUARD_SHA and guard['exit_code'] == 0
          and guard['stop'] is None and not guard.get('error'), 'guard was not successful')
    check(guard['command'] == [PYTHON, '-B', str(HERE / 'query_imports.py'), '--out', str(SCRATCH)]
          and guard['cwd'] == str(ROOT), 'guard command/cwd differs')
    check(guard['limits'] == dict(cpu_seconds=180, wall_seconds=300,
          address_space_bytes=6 * 1024**3, file_bytes=256 * 1024**2,
          disk_floor=8 * 1024**3, ram_floor=1024**3, cgroup_stop=4 * 1024**3), 'guard limits differ')
    check(set(guard['outputs']) == {'stdout', 'stderr'}, 'guard output keys differ')
    for name, row in guard['outputs'].items():
        check(sha(GUARDED / name) == row['sha256']
              and (GUARDED / name).stat().st_size == row['bytes'], 'guard log differs')
    invocation = read(SCRATCH / 'INVOCATION.json')
    check(invocation['runner_sha256'] == RUNNER_SHA
          and invocation['pinned_inputs'] == {str(p): h for p, h in query.PINNED.items()}
          and invocation['selected_materialization'] == str(query.MATERIALIZED),
          'invocation source/selection pins differ')
    check(sha(SCRATCH / 'PRESERVED-ACTIVE-PLAN.json') == PRIOR_SHA, 'prior source plan differs')
    old = read(SCRATCH / 'PRESERVED-ACTIVE-PLAN.json')
    plan = read(SCRATCH / 'EXTERNAL-PLAN.json')
    result = read(SCRATCH / 'RESULT.json')
    check(result['plan_sha256'] == sha(SCRATCH / 'EXTERNAL-PLAN.json'), 'result plan differs')
    check(result['actual_official_queries'] == 477 and len(plan['compiler_queries']) == 477,
          'actual query ledger scope differs')
    check(plan['modules'][:3591] == old['modules'] and len(plan['modules']) == 3593,
          'external source-plan prefix or extension differs')
    check({r['module'] for r in plan['modules'][3591:]} == {
          'Mathlib.Algebra.MvPolynomial.Funext', 'Mathlib.Algebra.MvPolynomial.Polynomial'},
          'two new source roots differ')
    for value in (plan, result):
        check(value['source_compilation_performed'] is False
              and value['object_authentication_performed'] is False
              and value['active_plan_mutation'] is False, 'scope was promoted')
    route_sha = sha(SCRATCH / 'ROUTE-EQUIVALENCE.json')
    check(plan['owned_mathlib_route_equivalence_sha256'] == route_sha, 'route binding differs')
    route = read(SCRATCH / 'ROUTE-EQUIVALENCE.json')
    expected_routes = [dict(module=r['module'], selected_sha256=r['sha256'],
        original=owned[r['module']]['original_path'],
        queried_materialized_source=owned[r['module']]['source'],
        import_provider=str(serial.source_for(r['module'], repos).resolve()),
        upstream_sha256=r['sha256'], full_bytes_equal=True, same_selected_version=True,
        object_authentication_performed=False)
        for r in selected if r['module'].startswith('Mathlib.')]
    check(len(expected_routes) == 9 and route['routes'] == expected_routes,
          'exact selected owned Mathlib route identities differ')
    for row in route['routes']:
        for key in ('original', 'queried_materialized_source', 'import_provider'):
            check(sha(row[key]) == row['selected_sha256'], 'selected route body differs')
    events = [json.loads(line) for line in (GUARDED / 'stdout').read_text().splitlines()]
    check(len(events) == 478 and events[-1] == result, 'guard query/event ledger differs')
    additions = query.read(query.FOLLOW / 'FOLLOW-ON-EXTERNAL-ROOTS.json')['official_additions_outside_active_plan']
    expected_sources = [dict(source=owned[r['module']]['source'], sha256=r['sha256']) for r in selected]
    expected_sources += [dict(source=str(serial.source_for(r['module'], repos).resolve()), sha256=r['sha256'])
                         for r in sorted(additions, key=lambda r:r['module'])]
    check(len(expected_sources) == 477, 'selected query identity count differs')
    for index, row in enumerate(plan['compiler_queries']):
        directory = SCRATCH / 'queries' / f'{index:04d}'
        request = read(directory / 'REQUEST.json')
        receipt = read(directory / 'RECEIPT.json')
        imports = read(directory / 'IMPORTS.json')
        expected = expected_sources[index]
        phase = 'EXACT_OWNED_OR_ASTRA_SOURCE' if index < 475 else 'OFFICIAL_EXTERNAL_EXTENSION'
        expected_cwd = str(query.MATERIALIZED if index < 475 else query.MATHLIB)
        check(row['source'] == request['source'] == expected['source']
              and row['source_sha256'] == expected['sha256']
              and row['phase'] == request['phase'] == receipt['phase'] == phase
              and request['cwd'] == expected_cwd
              and request['environment'] == (owned_env if index < 475 else base_env)
              and request['query_wall_seconds'] == 10
              and request['source_compilation_performed'] is False
              and request['object_authentication_performed'] is False,
              'selected query identity/environment/phase differs')
        literal = headers.imports(Path(row['source']))
        has_prelude = bool(re.search(r'(?m)^\s*prelude\s*$', headers.uncomments(Path(row['source']).read_text())))
        expected_imports = list(dict.fromkeys(resolved(name) for name in ([] if has_prelude else ['Init']) + literal))
        check(imports['literal_header'] == literal, 'actual literal import header differs')
        check(row['index'] == index and receipt['index'] == index and request['index'] == index,
              'query order differs')
        check(sha(directory / 'RECEIPT.json') == row['receipt_sha256']
              and sha(directory / 'REQUEST.json') == receipt['request_sha256'], 'query receipt binding differs')
        check(receipt['exit_code'] == 0 and receipt['error'] is None, 'query did not succeed')
        check(request['source_sha256'] == row['source_sha256'] == receipt['source_sha256_before']
              == receipt['source_sha256_after'] == sha(directory / 'source.lean') == sha(row['source']),
              'queried source body differs')
        check(request['command'] == [LEAN, '-j', '1', '-s', '8192', '--src-deps', row['source']]
              and request['compiler_sha256'] == COMPILER_SHA
              and request['route_equivalence_sha256'] == route_sha, 'query command/route differs')
        check(set(receipt['outputs']) == {'stdout', 'stderr'}, 'query output keys differ')
        for name, observed in receipt['outputs'].items():
            check(sha(directory / name) == observed['sha256']
                  and (directory / name).stat().st_size == observed['bytes'], 'query log differs')
        actual = list(dict.fromkeys(str(Path(line).resolve())
                      for line in (directory / 'stdout').read_text().splitlines() if line))
        check(actual == imports['imports'] == expected_imports, 'resolved literal import ledger differs')
        check([d['path'] for d in imports['dependencies']] == actual
              and len(set(actual)) == len(actual), 'exact dependency-source ledger differs')
        if index < 475:
            check(actual == request['expected_imports'], 'selected literal import resolution differs')
        else:
            check(request['expected_imports'] is None, 'external helper request differs')
            matches = [r for r in plan['modules'][3591:] if r['source'] == row['source']]
            check(len(matches) == 1, 'extended plan source missing or duplicated')
            planned = matches[0]
            check(planned['source'] == row['source']
                  and planned['source_sha256'] == row['source_sha256']
                  and planned['imports'] == actual, 'extended plan does not bind actual query')
        for dependency in imports['dependencies']:
            check(sha(dependency['path']) == dependency['sha256'], 'dependency source differs')
        check(events[index]['status'] == 'OFFICIAL_IMPORT_QUERY_PASS'
              and events[index]['index'] == index and events[index]['source'] == row['source']
              and events[index]['phase'] == phase and events[index]['imports'] == len(actual),
              'actual stdout event differs')
    OUTPUT.mkdir()
    shutil.copyfile(HERE / 'query_imports.py', OUTPUT / 'EXECUTED-query_imports.py')
    # Reuse literal v1 capture bytes only after complete current readback; do not
    # duplicate megabytes or rewrite its successful, narrower historical receipt.
    preserved = read(PAYLOAD / 'FILES.json')
    for row in preserved['files']:
        check(sha(PAYLOAD / row['path']) == row['sha256']
              and (PAYLOAD / row['path']).stat().st_size == row['bytes'], 'prior capture payload differs')
    for path in sorted(SCRATCH.rglob('*')):
        if path.is_file():
            captured = PAYLOAD / 'captured' / path.relative_to(SCRATCH)
            check(sha(path) == sha(captured), 'literal captured source/evidence differs')
    files = [dict(path=os.path.relpath(p, OUTPUT), bytes=p.stat().st_size, sha256=sha(p))
             for p in sorted(PAYLOAD.rglob('*')) if p.is_file()]
    files.append(dict(path='EXECUTED-query_imports.py', bytes=(OUTPUT / 'EXECUTED-query_imports.py').stat().st_size,
                      sha256=sha(OUTPUT / 'EXECUTED-query_imports.py')))
    summary = dict(schema='astra_follow_on_official_query_capture_v2',
        status='ACTUAL_OFFICIAL_SOURCE_QUERY_AND_LITERAL_CAPTURE_AUTHENTICATED',
        capture_runner_sha256=sha(__file__), query_runner_sha256=RUNNER_SHA,
        guard_receipt_sha256=sha(GUARDED / 'RECEIPT.json'),
        external_plan_sha256=sha(SCRATCH / 'EXTERNAL-PLAN.json'),
        route_equivalence_sha256=route_sha, actual_queries=477,
        original_owned_and_astra_sources=475, prior_source_plan_records=3591,
        extended_source_plan_records=3593, source_compilation_performed=False,
        object_authentication_performed=False, active_plan_mutation=False,
        source_query_is_not_theorem_elaboration=True, files=files)
    (OUTPUT / 'FILES.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'files'}))


if __name__ == '__main__':
    main()
