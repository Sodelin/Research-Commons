#!/usr/bin/env python3
"""Preserve and authenticate one explicitly configured, closed source-query run.

SOURCE-ONLY DRAFT: no full-query run or capture is asserted by this file.
No compiler, Lake, Git or subprocess is invoked. The owner must first provide
RUN-CONFIG.json and its exact SHA256; no successful run/profile is invented.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
RUNNER_SHA = '0ac11bd889eef51ce47f1850e11d98ba7e3120d0be36650051048589e5783a91'
SELECTION_SHA = 'fb8f2ac3ba0a55f563f3ea0fcce3c8b1af6e127097df0668bf4d8e051ab16925'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'
COMPILER_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
PREFIX_SHA = '32bb59e44de8b3252c37deae1f12a7a14fc79a0407da97dd15f7d5b576991d2c'
ACTIVE_SHA = 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10'
PREDECESSOR_CAPTURE_SHA = 'dbce28be1df8b5b7dac80dc8400551d8ef7415eb0e15e93e07a3d9005ac518c4'
PYTHON = '/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3'
LEAN = '/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin/lean'
MAX_CAPTURE_BYTES = 256 * 1024**2
MAX_CAPTURE_FILES = 16032
ROOT_FILES = {'INVOCATION.json', 'PRESERVED-QUERY-PREFIX-PLAN.json',
              'UNCHANGED-ACTIVE-PLAN.json', 'ROUTE-EQUIVALENCE.json',
              'NEW-EXTERNAL-ROOTS.json', 'EXTERNAL-PLAN.json', 'RESULT.json', 'FAILED.json'}
QUERY_FILES = {'REQUEST.json', 'RECEIPT.json', 'IMPORTS.json', 'source.lean', 'stdout', 'stderr'}


def check(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(262144), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def load_source(name, path, pin):
    """Load exact inspected source bytes, bypassing cached Python bytecode."""
    body = Path(path).read_bytes()
    check(hashlib.sha256(body).hexdigest() == pin, 'helper source differs: ' + str(path))
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(body, str(path), 'exec'), module.__dict__)
    check(sha(path) == pin, 'helper source changed while loading')
    return module


def config_for(pin):
    path = HERE / 'RUN-CONFIG.json'
    check(re.fullmatch(r'[0-9a-f]{64}', pin) is not None and sha(path) == pin,
          'explicit owner run-configuration hash differs')
    config = read(path)
    check(set(config) == {'schema', 'query_runner_sha256', 'scratch', 'guarded',
                         'output', 'command', 'cwd', 'limits'}, 'run-configuration keys differ')
    check(config['schema'] == 'astra_full_query_capture_run_config_v1'
          and config['query_runner_sha256'] == RUNNER_SHA, 'run-configuration version differs')
    scratch, guarded, output = [Path(config[name]) for name in ('scratch', 'guarded', 'output')]
    for value in (scratch, guarded, output):
        check(value.is_absolute() and value.resolve() == value, 'configuration path is not literal/canonical')
    check(scratch.parent == Path('/workspace/scratch')
          and scratch.name.startswith('astra-full-accepted-import-query-'), 'scratch scope differs')
    check(guarded.parent == HERE / 'evidence' and output.parent == HERE / 'evidence'
          and guarded != output and not output.exists(), 'exclusive capture/evidence scope differs')
    check(config['command'] == [PYTHON, '-B', str(HERE / 'query_imports.py'), '--out', str(scratch)]
          and config['cwd'] == str(ROOT), 'only the fixed full-query command is accepted')
    limits = config['limits']
    check(set(limits) == {'cpu_seconds', 'wall_seconds', 'address_space_bytes', 'file_bytes',
                         'disk_floor', 'ram_floor', 'cgroup_stop'}, 'configured limit keys differ')
    check(all(type(value) is int and value > 0 for value in limits.values()), 'limits must be positive integers')
    check(limits['cpu_seconds'] <= 600 and limits['wall_seconds'] <= 900
          and limits['address_space_bytes'] <= 6 * 1024**3 and limits['file_bytes'] <= 1024**3
          and limits['disk_floor'] == 8 * 1024**3 and limits['ram_floor'] == 1024**3
          and limits['cgroup_stop'] == 4 * 1024**3, 'configuration exceeds reviewed finite profile')
    return config, scratch, guarded, output


def snapshot(scratch, guarded):
    """Pin raw complete/partial inputs before semantic checking; no symlink traversal."""
    files = []
    check(guarded.is_dir(), 'closed guard evidence directory missing')
    check(not scratch.exists() or scratch.is_dir(), 'scratch evidence is not a directory')
    for path in sorted(scratch.rglob('*')):
        check(not path.is_symlink(), 'scratch evidence symlink is refused')
        rel = path.relative_to(scratch)
        if path.is_dir():
            check(str(rel) == 'queries' or (len(rel.parts) == 2 and rel.parts[0] == 'queries'
                  and re.fullmatch(r'[0-9]{4}', rel.parts[1]) is not None), 'unexpected evidence directory')
            continue
        allowed = (len(rel.parts) == 1 and path.name in ROOT_FILES) or (
            len(rel.parts) == 3 and rel.parts[0] == 'queries'
            and re.fullmatch(r'[0-9]{4}', rel.parts[1]) is not None and path.name in QUERY_FILES)
        check(path.is_file() and allowed, 'unexpected scratch payload')
        files.append((path, Path('captured') / rel))
    for name in ('RECEIPT.json', 'stdout', 'stderr'):
        path = guarded / name
        check(path.is_file() and not path.is_symlink(), 'closed guard file missing or symlink')
        files.append((path, Path('guard') / name))
    files += [(HERE / name, Path('configuration') / name) for name in
              ('RUN-CONFIG.json', 'query_imports.py', 'FULL-SOURCE-SELECTION.json',
               'prepare_sources.py', 'prepare_runner.py', 'SOURCE-SUCCESSOR.json', 'capture_query.py')]
    rows = [dict(source=str(path), path=str(rel), bytes=path.stat().st_size, sha256=sha(path))
            for path, rel in files]
    check(len(rows) <= MAX_CAPTURE_FILES and sum(r['bytes'] for r in rows) <= MAX_CAPTURE_BYTES,
          'bounded evidence-capture budget exceeded; original inputs retained')
    return rows


def audit_success(config, scratch, guarded):
    check(sha(HERE / 'query_imports.py') == RUNNER_SHA, 'query runner differs')
    check(sha(HERE / 'FULL-SOURCE-SELECTION.json') == SELECTION_SHA, 'full selection differs')
    check(sha(LEAN) == COMPILER_SHA, 'compiler binary differs')
    query = load_source('frozen_full_query_for_capture', HERE / 'query_imports.py', RUNNER_SHA)
    headers = load_source('frozen_headers_for_full_capture', query.FOLLOW / 'generate_plan.py',
                          query.PINNED[query.FOLLOW / 'generate_plan.py'])
    serial = load_source('frozen_serial_for_full_capture', query.PREVIOUS / 'build_mathlib_serial.py',
                         query.PINNED[query.PREVIOUS / 'build_mathlib_serial.py'])
    full, selected, owned = query.authenticate_sources(headers)
    check(query.MAX_QUERIES == 2500 and query.QUERY_WALL_SECONDS == 10
          and query.MAX_OUTPUT_BYTES == 4 * 1024**2, 'per-query budget differs')
    repos = [query.MATHLIB, *[query.MATHLIB / '.lake/packages' / row['name']
                            for row in full['package_dependency_pins']]]
    core = query.CORE_SOURCE.resolve()
    base_env = dict(LEAN_PATH=os.pathsep.join(str(p / '.lake/build/lib/lean') for p in repos),
        LEAN_SRC_PATH=os.pathsep.join(map(str, [*repos, core, core / 'lake'])),
        LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='8192', LEAN_IMPORT_WORKERS='1',
        MIMALLOC_ARENA_RESERVE='16384', RAYON_NUM_THREADS='1')
    owned_env = dict(base_env,
        LEAN_PATH=os.pathsep.join([str(query.MATHLIB / '.lake/build/lib/lean'),
            str(query.MATERIALIZED / '.lake/build/lib/lean'),
            *[str(p / '.lake/build/lib/lean') for p in repos[1:]]]),
        LEAN_SRC_PATH=os.pathsep.join(map(str, [query.MATHLIB, query.MATERIALIZED,
                                             *repos[1:], core, core / 'lake'])))

    def resolved(name):
        if name.startswith('Mathlib.'):
            return str(serial.source_for(name, repos).resolve())
        if name in owned:
            return owned[name]['source']
        if name in {'Init', 'Lean', 'Std', 'Lake'} or name.startswith(('Lean.', 'Init.', 'Std.', 'Lake.')):
            base = core / 'lake' if name == 'Lake' or name.startswith('Lake.') else core
            return str((base / (name.replace('.', '/') + '.lean')).resolve())
        return str(serial.source_for(name, repos).resolve())

    guard = read(guarded / 'RECEIPT.json')
    check(guard['runner_sha256'] == GUARD_SHA and sha(query.PREVIOUS / 'guard.py') == GUARD_SHA,
          'frozen guard identity differs')
    check(guard['command'] == config['command'] and guard['cwd'] == config['cwd']
          and guard['limits'] == config['limits'], 'actual guard command/profile differs')
    check(guard['exit_code'] == 0 and guard['stop'] is None and not guard.get('error'),
          'actual guard not successful; preserve without query-completion claim')
    check(set(guard['outputs']) == {'stdout', 'stderr'}, 'guard output keys differ')
    for name, row in guard['outputs'].items():
        check(sha(guarded / name) == row['sha256'] and (guarded / name).stat().st_size == row['bytes'],
              'guard output bytes differ')
    check(not (scratch / 'FAILED.json').exists(), 'runner preserved an incomplete query run')
    invocation = read(scratch / 'INVOCATION.json')
    check(invocation['schema'] == 'astra_full_accepted_import_query_invocation_v1'
          and invocation['runner_sha256'] == RUNNER_SHA
          and invocation['argv'] == [str(HERE / 'query_imports.py'), '--out', str(scratch)]
          and invocation['pinned_inputs'] == {str(p): pin for p, pin in query.PINNED.items()}
          and invocation['selected_materialization'] == str(query.MATERIALIZED)
          and invocation['max_queries'] == 2500, 'invocation/selection differs')
    check(sha(scratch / 'PRESERVED-QUERY-PREFIX-PLAN.json') == PREFIX_SHA
          and sha(query.PREFIX_PLAN) == PREFIX_SHA, '3593 source-query prefix differs')
    check(sha(scratch / 'UNCHANGED-ACTIVE-PLAN.json') == ACTIVE_SHA
          and sha(query.SUPPORT / 'EXTERNAL-PLAN.json') == ACTIVE_SHA, 'active3591 plan changed')
    old = read(scratch / 'PRESERVED-QUERY-PREFIX-PLAN.json')
    plan, result = read(scratch / 'EXTERNAL-PLAN.json'), read(scratch / 'RESULT.json')
    check(len(old['modules']) == 3593 and plan['modules'][:3593] == old['modules'],
          'literal source-plan prefix differs')
    check(plan['mathlib_pin'] == query.MATHLIB_PIN and plan['compiler_sha256'] == COMPILER_SHA
          and plan['dependencies'] == old['dependencies'] == full['package_dependency_pins'],
          'source-plan compiler/Mathlib/package identities differ')
    check(result['plan_sha256'] == sha(scratch / 'EXTERNAL-PLAN.json'), 'result/plan binding differs')
    n = len(plan['compiler_queries'])
    check(1642 <= n <= 2500 and result['actual_official_queries'] == n, 'actual query count differs')
    check(plan['selected_sources'] == 1642 and plan['selected_library_sources'] == 1641
          and plan['selected_configuration_sources'] == 1 and plan['selected_baseline_sources'] == 1613
          and plan['previous_plan_sha256'] == PREFIX_SHA and plan['unchanged_active_plan_sha256'] == ACTIVE_SHA
          and plan['previous_source_records_authenticated'] == 3593, 'full source scope differs')
    for value in (invocation, plan, result):
        check(value['source_compilation_performed'] is False and value['object_authentication_performed'] is False
              and value['active_plan_mutation'] is False, 'source-query scope was promoted')
    status = 'OFFICIAL_IMPORT_QUERIES_ONLY_NO_SOURCE_COMPILATION'
    check(plan['schema'] == 'astra_full_accepted_official_import_plan_v1'
          and plan['status'] == result['status'] == status, 'actual query status differs')
    route_sha = sha(scratch / 'ROUTE-EQUIVALENCE.json')
    check(plan['owned_mathlib_route_equivalence_sha256'] == route_sha, 'route binding differs')
    route = read(scratch / 'ROUTE-EQUIVALENCE.json')
    expected_routes = [dict(module=r['module'], selected_sha256=r['sha256'],
        original=owned[r['module']]['original_path'], queried_materialized_source=owned[r['module']]['source'],
        import_provider=str(serial.source_for(r['module'], repos).resolve()), upstream_sha256=r['sha256'],
        full_bytes_equal=True, same_selected_version=True, object_authentication_performed=False)
        for r in selected if r['module'].startswith('Mathlib.')]
    check(len(expected_routes) == 11 and route['routes'] == expected_routes
          and route['original_owned_source_query_paths_preserved'] is True
          and route['object_authentication_performed'] is False, 'all11 owned Mathlib routes differ')
    for row in expected_routes:
        for key in ('original', 'queried_materialized_source', 'import_provider'):
            check(sha(row[key]) == row['selected_sha256'], 'selected route source bytes differ')
    old_names = {row['module'] for row in old['modules']}
    roots = sorted(set(full['new_mathlib_roots_outside_active_plan']) - old_names)
    check(len(roots) == 9 and plan['new_external_roots'] == roots
          and plan['roots'] == sorted(set(old['roots'] + roots)), 'nine new root walks differ')
    additions = [dict(module=name, sha256=sha(serial.source_for(name, repos))) for name in roots]
    check(read(scratch / 'NEW-EXTERNAL-ROOTS.json') == dict(roots=additions,
          transitive_cost='UNQUERIED_AT_SELECTION'), 'selected root source ledger differs')
    events = [json.loads(line) for line in (guarded / 'stdout').read_text().splitlines()]
    check(len(events) == n + 1 and events[-1] == result, 'guard event sequence differs')
    expected_files = set(ROOT_FILES) - {'FAILED.json'}
    imports_by_source = {}
    external_order = []
    allowed_roots = [query.MATERIALIZED.resolve(), core, *[r.resolve() for r in repos]]
    for index, row in enumerate(plan['compiler_queries']):
        directory = scratch / 'queries' / f'{index:04d}'
        expected_files.update(str(Path('queries') / f'{index:04d}' / name) for name in QUERY_FILES)
        request, receipt, imports = [read(directory / name) for name in
                                     ('REQUEST.json', 'RECEIPT.json', 'IMPORTS.json')]
        owned_phase = index < 1642
        phase = 'EXACT_OWNED_OR_ASTRA_SOURCE' if owned_phase else 'OFFICIAL_EXTERNAL_EXTENSION'
        expected_source = owned[selected[index]['module']]['source'] if owned_phase else row['source']
        source = Path(expected_source)
        check(source.is_absolute() and source.resolve() == source
              and any(source.is_relative_to(base) for base in allowed_roots), 'query source escaped source roots')
        check(row['index'] == request['index'] == receipt['index'] == index
              and row['phase'] == request['phase'] == receipt['phase'] == phase
              and row['source'] == request['source'] == expected_source, 'query identity/order differs')
        if owned_phase:
            check(row['source_sha256'] == selected[index]['sha256'], 'selected source differs')
        else:
            check(row['source'] not in imports_by_source, 'duplicate external source query')
            external_order.append(row['source'])
        check(request['cwd'] == str(query.MATERIALIZED if owned_phase else query.MATHLIB)
              and request['environment'] == (owned_env if owned_phase else base_env)
              and request['query_wall_seconds'] == 10, 'query cwd/environment/budget differs')
        check(request['source_compilation_performed'] is False
              and request['object_authentication_performed'] is False
              and imports['only_source_resolution_verified'] is True
              and imports['object_authentication_performed'] is False, 'query scope differs')
        check(sha(directory / 'RECEIPT.json') == row['receipt_sha256']
              and sha(directory / 'REQUEST.json') == receipt['request_sha256'], 'request/receipt binding differs')
        check(receipt['exit_code'] == 0 and receipt['error'] is None, 'individual query failed')
        check(row['source_sha256'] == request['source_sha256'] == receipt['source_sha256_before']
              == receipt['source_sha256_after'] == sha(source) == sha(directory / 'source.lean'),
              'source/query-copy binding differs')
        check(request['command'] == [LEAN, '-j', '1', '-s', '8192', '--src-deps', str(source)]
              and request['compiler_sha256'] == COMPILER_SHA
              and request['route_equivalence_sha256'] == route_sha, 'query command/route differs')
        check(set(receipt['outputs']) == {'stdout', 'stderr'}, 'query output keys differ')
        for name, observed in receipt['outputs'].items():
            check(sha(directory / name) == observed['sha256']
                  and (directory / name).stat().st_size == observed['bytes']
                  and observed['bytes'] <= 4 * 1024**2, 'query output bytes or accepted-output budget differs')
        lines = (directory / 'stdout').read_text().splitlines()
        check(all(Path(line).is_absolute() for line in lines if line), 'query output has relative path')
        actual = list(dict.fromkeys(str(Path(line).resolve()) for line in lines if line))
        literal = headers.imports(source)
        prelude = bool(re.search(r'(?m)^\s*prelude\s*$', headers.uncomments(source.read_text())))
        expected_imports = list(dict.fromkeys(resolved(name) for name in ([] if prelude else ['Init']) + literal))
        check(imports['literal_header'] == literal and imports['imports'] == actual == expected_imports,
              'literal header/official resolved paths differ')
        check(request['expected_imports'] == (expected_imports if owned_phase else None),
              'query expected-source policy differs')
        check(imports['dependencies'] == [dict(path=path, sha256=sha(path)) for path in actual],
              'exact imported-source hash ledger differs')
        check(all(any(Path(path).is_relative_to(base) for base in allowed_roots) for path in actual),
              'dependency source escaped source roots')
        check(events[index] == dict(status='OFFICIAL_IMPORT_QUERY_PASS', index=index, phase=phase,
                                    source=str(source), imports=len(actual)), 'query event differs')
        if not owned_phase:
            imports_by_source[str(source)] = dict(imports=actual, sha256=row['source_sha256'])
    actual_files = {str(path.relative_to(scratch)) for path in scratch.rglob('*') if path.is_file()}
    check(actual_files == expected_files, 'success run contains missing or extra evidence files')

    # Replay the frozen helper's preorder queries and postorder plan in memory.
    # This uses the already recorded imports; it never calls serial.plan/setup.
    done = {str(Path(row['source']).resolve()): row for row in old['modules']}
    check(len(done) == 3593, 'old source identities are not unique')
    active, preorder = set(), []

    def visit(path):
        source = Path(path).resolve()
        key = str(source)
        if key in done or source.is_relative_to(core):
            return
        check(key not in active and key in imports_by_source, 'cycle or missing actual external query')
        active.add(key)
        preorder.append(key)
        observed = imports_by_source[key]
        for dep in observed['imports']:
            visit(dep)
        matching = [repo for repo in repos if source.is_relative_to(repo)]
        check(bool(matching), 'external query outside pinned package sources')
        repo = max(matching, key=lambda value: len(value.parts))
        rel = source.relative_to(repo)
        done[key] = dict(source=key, source_sha256=observed['sha256'], repo=str(repo),
            module='.'.join(rel.with_suffix('').parts),
            target=str(repo / '.lake/build/lib/lean' / rel.with_suffix('.olean')),
            imports=observed['imports'])
        active.remove(key)

    for name in roots:
        visit(serial.source_for(name, repos))
    check(preorder == external_order and set(preorder) == set(imports_by_source),
          'recorded external query order or reachability differs from frozen DFS')
    check(list(done.values()) == plan['modules']
          and plan['new_external_source_records'] == len(done) - 3593
          and n == 1642 + len(done) - 3593, 'source graph postorder/coverage differs')
    for row in plan['modules']:
        check(sha(row['source']) == row['source_sha256'], 'external source bytes changed')
    query.authenticate_sources(headers)
    return dict(status='ACTUAL_OFFICIAL_SOURCE_QUERY_AND_CAPTURE_AUTHENTICATED',
        query_runner_sha256=RUNNER_SHA, guard_receipt_sha256=sha(guarded / 'RECEIPT.json'),
        source_selection_sha256=SELECTION_SHA, external_plan_sha256=sha(scratch / 'EXTERNAL-PLAN.json'),
        route_equivalence_sha256=route_sha, actual_queries=n, selected_sources=1642,
        selected_library_sources=1641, lake_configuration_sources=1, owned_mathlib_routes=11,
        old_query_prefix_records=3593, unchanged_active_records=3591,
        new_external_root_walks=9, new_external_source_records=len(done) - 3593,
        extended_source_records=len(done), dfs_preorder_and_postorder_replayed=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config-sha256', required=True)
    args = parser.parse_args()
    config, scratch, guarded, output = config_for(args.config_sha256)
    scratch_present = scratch.is_dir()
    rows = snapshot(scratch, guarded)
    try:
        check(scratch_present, 'query scratch directory absent; preserve only closed guard/configuration bytes')
        conclusion = audit_success(config, scratch, guarded)
        code = 0
    except Exception as error:
        # Preserve exact raw failure/partial bytes, but never promote their
        # module/query events to an authenticated successful closure.
        conclusion = dict(status='PRESERVED_INCOMPLETE_OR_UNVERIFIED_QUERY_EVIDENCE',
                          error=dict(type=type(error).__name__, message=str(error)),
                          actual_query_completion_authenticated=False)
        code = 2
    check(scratch.is_dir() == scratch_present, 'scratch presence changed during capture audit')
    output.mkdir()
    for row in rows:
        source, target = Path(row['source']), output / row['path']
        check(sha(source) == row['sha256'] and source.stat().st_size == row['bytes'],
              'input evidence changed during audit')
        target.parent.mkdir(parents=True, exist_ok=True)
        with source.open('rb') as incoming, target.open('xb') as outgoing:
            for block in iter(lambda: incoming.read(262144), b''):
                outgoing.write(block)
        check(sha(target) == row['sha256'] and target.stat().st_size == row['bytes'],
              'capture copy differs')
    summary = dict(schema='astra_full_accepted_query_capture_v1',
        observed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), **conclusion,
        capture_runner_sha256=sha(__file__), predecessor_capture_sha256=PREDECESSOR_CAPTURE_SHA,
        run_config_sha256=args.config_sha256, configured_guard_profile=config,
        query_scratch_observation=dict(path=str(scratch), present=scratch_present,
                                       absence_does_not_imply_a_query_or_success=True),
        source_compilation_performed=False, object_authentication_performed=False,
        active_plan_mutation=False, subprocesses_invoked_by_capture=0,
        source_query_is_not_theorem_elaboration=True, old042_057_059_outer_guards='UNKNOWN; unchanged',
        capture_budget=dict(max_files=MAX_CAPTURE_FILES, max_bytes=MAX_CAPTURE_BYTES),
        files=rows)
    with (output / 'FILES.json').open('x') as stream:
        json.dump(summary, stream, indent=2)
        stream.write('\n')
    print(json.dumps({key: value for key, value in summary.items() if key != 'files'}))
    return code


if __name__ == '__main__':
    sys.exit(main())
