#!/usr/bin/env python3
"""Authenticate and preserve the closed v2 source-query run; never compile."""
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SCRATCH = Path('/workspace/scratch/astra-follow-on-import-query-2355-v2')
GUARDED = HERE / 'evidence/import-query-v2'
OUTPUT = HERE / 'evidence/import-query-v2-authenticated'
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
    guard = read(GUARDED / 'RECEIPT.json')
    check(guard['runner_sha256'] == GUARD_SHA and guard['exit_code'] == 0
          and guard['stop'] is None and not guard.get('error'), 'guard was not successful')
    check(guard['command'] == [PYTHON, '-B', str(HERE / 'query_imports.py'), '--out', str(SCRATCH)]
          and guard['cwd'] == str(ROOT), 'guard command/cwd differs')
    check(guard['limits'] == dict(cpu_seconds=180, wall_seconds=300,
          address_space_bytes=6 * 1024**3, file_bytes=256 * 1024**2,
          disk_floor=8 * 1024**3, ram_floor=1024**3, cgroup_stop=4 * 1024**3), 'guard limits differ')
    for name, row in guard['outputs'].items():
        check(sha(GUARDED / name) == row['sha256']
              and (GUARDED / name).stat().st_size == row['bytes'], 'guard log differs')
    invocation = read(SCRATCH / 'INVOCATION.json')
    check(invocation['runner_sha256'] == RUNNER_SHA, 'invocation source differs')
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
    check(len(route['routes']) == 9, 'owned Mathlib route scope differs')
    for row in route['routes']:
        for key in ('original', 'queried_materialized_source', 'import_provider'):
            check(sha(row[key]) == row['selected_sha256'], 'selected route body differs')
    events = [json.loads(line) for line in (GUARDED / 'stdout').read_text().splitlines()]
    check(len(events) == 478 and events[-1] == result, 'guard query/event ledger differs')
    for index, row in enumerate(plan['compiler_queries']):
        directory = SCRATCH / 'queries' / f'{index:04d}'
        request = read(directory / 'REQUEST.json')
        receipt = read(directory / 'RECEIPT.json')
        imports = read(directory / 'IMPORTS.json')
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
        for name, observed in receipt['outputs'].items():
            check(sha(directory / name) == observed['sha256']
                  and (directory / name).stat().st_size == observed['bytes'], 'query log differs')
        actual = list(dict.fromkeys(str(Path(line).resolve())
                      for line in (directory / 'stdout').read_text().splitlines() if line))
        check(actual == imports['imports'], 'resolved import ledger differs')
        if index < 475:
            check(actual == request['expected_imports'], 'selected literal import resolution differs')
        for dependency in imports['dependencies']:
            check(sha(dependency['path']) == dependency['sha256'], 'dependency source differs')
        check(events[index]['status'] == 'OFFICIAL_IMPORT_QUERY_PASS'
              and events[index]['index'] == index and events[index]['source'] == row['source'],
              'actual stdout event differs')
    OUTPUT.mkdir()
    shutil.copyfile(HERE / 'query_imports.py', OUTPUT / 'EXECUTED-query_imports.py')
    for path in sorted(SCRATCH.rglob('*')):
        if path.is_file():
            target = OUTPUT / 'captured' / path.relative_to(SCRATCH)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
            check(sha(path) == sha(target), 'capture copy differs')
    files = [dict(path=str(p.relative_to(OUTPUT)), bytes=p.stat().st_size, sha256=sha(p))
             for p in sorted(OUTPUT.rglob('*')) if p.is_file()]
    summary = dict(schema='astra_follow_on_official_query_capture_v1',
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
