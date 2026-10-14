#!/usr/bin/env python3
"""Prepare an isolated full owned-source graph; never inspect or build objects."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
FULL = ROOT / 'research/2026-10-14-astra-full-accepted-import-query-0100z'
SOURCES = FULL / 'FULL-SOURCE-SELECTION.json'
EXTERNAL = FULL / 'evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json'
CURRENT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/PROVIDER-SELECTION.json'
STATE = Path('/workspace/scratch/astra-full-owned-0145')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pinned(path, sha):
    if digest(path) != sha:
        raise ValueError('selected metadata changed: ' + str(path))
    return json.loads(path.read_text())


def prepare():
    selected = pinned(SOURCES, 'fb8f2ac3ba0a55f563f3ea0fcce3c8b1af6e127097df0668bf4d8e051ab16925')
    external = pinned(EXTERNAL, '0c64ed24f1b9d237a7ccee440e9b360cce7ba797079c02d1b0154473866b1d0a')
    current = pinned(CURRENT, '0be6bc5d9d9e8e329d8b899bb4d158e1e42188510631d115c60d0a89717ea95b')
    modules = {r['module']: r for r in selected['sources'] if r['kind'] != 'lake_configuration'}
    upstream = {r['module']: r for r in external['modules']}
    if len(modules) != 1641 or len(upstream) != 3661:
        raise ValueError('selected source graph scope differs')
    order, seen, active = [], set(), set()

    def visit(name):
        if name in seen:
            return
        if name in active:
            raise ValueError('owned source cycle: ' + name)
        active.add(name)
        for dep in modules[name]['imports']:
            if dep in modules:
                visit(dep)
            elif dep not in upstream and dep not in {'Init', 'Lean', 'Std', 'Lake'} and not dep.startswith(('Init.', 'Lean.', 'Std.', 'Lake.')):
                raise ValueError('selected import lacks an external/core source provider: ' + dep)
        active.remove(name)
        seen.add(name)
        order.append(name)

    for name in selected['literal_baseline_order']:
        visit(name)
    if order != selected['literal_baseline_order']:
        raise ValueError('literal accepted1613 dependency order changed')
    for name in sorted(modules):
        visit(name)
    rows = []
    for name in order:
        source = modules[name]
        row = dict(module=name, source=source['source'], source_sha256=source['sha256'],
                   imports=source['imports'], provenance=source['origins'],
                   kind=source['kind'], execution='NOT_REQUESTED',
                   proposed_target=str(STATE / '.lake/build/lib/lean' / Path(*name.split('.')).with_suffix('.olean')))
        if name.startswith('Mathlib.'):
            upstream_source = upstream[name]
            if source['sha256'] != upstream_source['source_sha256']:
                raise ValueError('selected owned/upstream Mathlib source version differs: ' + name)
            row['future_mathlib_route'] = dict(source=upstream_source['source'],
                source_sha256=upstream_source['source_sha256'], target=upstream_source['target'],
                object_authenticated=False,
                required_gate='Full external source/log/receipt/object authentication and exact lookup identity before use.')
        rows.append(row)
    candidates = []
    for row in current['owned']:
        full = modules[row['module']]
        if row['sha256'] != full['sha256'] or row['imports'] != full['imports']:
            raise ValueError('current provider version/imports differ: ' + row['module'])
        candidates.append(dict(module=row['module'], source_sha256=row['sha256'],
                               object_authenticated=False, reused=False))
    if len(candidates) != 319 or sum(r['module'].startswith('Mathlib.') for r in rows) != 11:
        raise ValueError('source-only candidate scope differs')
    result = dict(schema='astra_full_owned_source_plan_v1',
        status='SOURCE_PLAN_ONLY_NO_OBJECT_AUTHENTICATION_OR_EXECUTION',
        source_selection_sha256=digest(SOURCES), full_external_source_plan_sha256=digest(EXTERNAL),
        current_provider_source_selection_sha256=digest(CURRENT),
        materialized_source='/workspace/scratch/astra-unified-extension-sources-2340',
        proposed_fresh_owned_state=str(STATE), baseline_order_preserved=True,
        modules=rows, current_provider_source_matches=candidates,
        current_provider_objects_authenticated=False, namespace_resolution='NOT_RUN',
        compiler_invocations=0, source_files_modified=False, active_state_modified=False,
        current_support_target_remains_first=True, current_target_completion_claimed=False,
        actual_lake_run=False, axiom_audit_completed=False, physical_representative_proved=False)
    with (HERE / 'FULL-OWNED-SOURCE-PLAN.json').open('x') as handle:
        json.dump(result, handle, indent=2);handle.write('\n')
    print(json.dumps(dict(status=result['status'], owned_sources=len(rows),
                         exact_current_provider_source_matches=len(candidates),
                         plan_sha256=digest(HERE / 'FULL-OWNED-SOURCE-PLAN.json'),
                         compiler_invocations=0, objects_authenticated=False)))


if __name__ == '__main__':
    prepare()
