#!/usr/bin/env python3
"""Authenticate and preserve the complete original prefix in a NEW state only.

Run under the fixed guard. This never invokes Lean or changes an old artifact.
Missing complete pinned provenance is an explicit refusal before mutation.
"""
import argparse
import json
from pathlib import Path
import sys

import external_state as auth


def copy_exact(source, target, expected):
    require = auth.require
    require(not source.is_symlink() and auth.digest(source) == expected, 'copy source identity differs')
    target.parent.mkdir(parents=True, exist_ok=True)
    with target.open('xb') as out, source.open('rb') as inp:
        for data in iter(lambda: inp.read(1024**2), b''):
            out.write(data)
    require(auth.digest(target) == expected, 'preserved copy identity differs')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--guard-output', type=Path, required=True)
    args = parser.parse_args()
    command = auth.prepare_command(args.guard_output)
    auth.require_running_guard(args.guard_output, command)
    origins = auth.provenance()  # mandatory future reviewed complete3591 pin
    compiler, gate, serial = auth.providers()
    repos, pins, env = compiler.setup(auth.MATHLIB, auth.LEAN_BIN)
    plan, compiler, gate, serial = auth.context(repos, auth.LEAN_BIN, pins)
    auth.require(not auth.STATE.exists(), 'new state already exists; preserve it, do not overwrite')
    auth.require(auth.digest(auth.ORIGINAL_STATE/'PLAN.json') == auth.ORIGINAL_PLAN_SHA,
                 'original state selection changed')
    indices = sorted(int(p.stem) for p in auth.ORIGINAL_STATE.glob('[0-9][0-9][0-9][0-9].json'))
    auth.require(indices == list(range(auth.PREFIX_COUNT)), 'original3591 execution is not complete')
    baseline_path = auth.PREVIOUS/'evidence/MATHLIB-SOURCE-EXECUTION.json'
    auth.require(auth.digest(baseline_path) == auth.BASELINE_SHA, 'published early execution changed')
    baseline = auth.read(baseline_path)['compiled_modules']
    for index, row in enumerate(plan['modules'][:auth.PREFIX_COUNT]):
        auth.namespace_route(row, repos, compiler)
        auth.authenticate_record(auth.ORIGINAL_STATE, index, row, compiler, origins['modules'][index], baseline)
    checked = gate.verify_dependency_state(auth.ORIGINAL_STATE, repos, auth.LEAN_BIN, pins)
    auth.require(checked['plan_sha256'] == auth.ORIGINAL_PLAN_SHA
                 and len(checked['modules']) == auth.PREFIX_COUNT, 'original complete graph gate differs')
    for row in plan['modules'][auth.PREFIX_COUNT:]:
        auth.require(not compiler.artifacts(Path(row['target'])),
                     'unreceipted new target already exists; preserve and investigate explicitly')
    # Everything above is read-only. Any interrupted partial new state below is
    # preserved and is refused by later preparation; no automatic deletion.
    auth.STATE.mkdir()
    copy_exact(auth.PLAN, auth.STATE/'PLAN.json', auth.PLAN_SHA)
    copy_exact(auth.PREFIX_PROVENANCE, auth.STATE/'PREFIX-PROVENANCE.json', auth.PREFIX_PROVENANCE_SHA)
    wrappers = {}
    for index, row in enumerate(plan['modules'][:auth.PREFIX_COUNT]):
        origin = origins['modules'][index]
        for suffix, expected in [('json', origin['receipt_sha256']),
                                 ('stdout', origin['stdout_sha256']), ('stderr', origin['stderr_sha256'])]:
            copy_exact(auth.ORIGINAL_STATE/f'{index:04d}.{suffix}', auth.STATE/f'{index:04d}.{suffix}', expected)
        receipt = auth.read(auth.STATE/f'{index:04d}.json')
        wrapper = auth.STATE/'reuse'/f'{index:04d}.json'
        auth.write_new(wrapper, auth.reuse_wrapper(index, receipt, origin))
        wrappers[str(index)] = auth.digest(wrapper)
        source_copy = auth.STATE/'source'/Path(*row['module'].split('.')).with_suffix('.lean')
        copy_exact(Path(row['source']), source_copy, row['source_sha256'])
    auth.write_new(auth.STATE/'INITIALIZATION.json', dict(schema='astra_full_external_initialization_v1',
        plan_sha256=auth.PLAN_SHA, original_plan_sha256=auth.ORIGINAL_PLAN_SHA,
        prefix_provenance_sha256=auth.PREFIX_PROVENANCE_SHA,
        prepare_runner_sha256=auth.digest(__file__), authenticator_sha256=auth.LOADED_SHA,
        command=command, guard_output=str(auth.guard_output(args.guard_output)),
        reused=auth.PREFIX_COUNT, source_compilations=0, reuse_wrapper_sha256=wrappers,
        original042_057_059_outer_guards='UNKNOWN', originals_mutated=False))
    print(json.dumps(dict(status='ORIGINAL_PREFIX_PRESERVED_AFTER_AUTHENTICATION',
        reused=auth.PREFIX_COUNT, source_compilations=0,
        initialization_sha256=auth.digest(auth.STATE/'INITIALIZATION.json'))), flush=True)


if __name__ == '__main__':
    main()
