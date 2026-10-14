#!/usr/bin/env python3
"""Compile one explicit small batch of the70 additional selected external sources.

Reuses reviewed compiler/setup, exact artifact checks and serial resource helper.
No queries, plan extension, old-state mutation, parallelism or automatic next job.
"""
import argparse
import json
from pathlib import Path
import time

import external_state as auth
from prepare_full import copy_exact


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--guard-output', type=Path, required=True)
    parser.add_argument('--batch', type=int, choices=(1, 4, 8, 16, 32), required=True)
    args = parser.parse_args()
    command = auth.builder_command(args.guard_output, args.batch)
    auth.require_running_guard(args.guard_output, command)
    auth.provenance()
    compiler, gate, serial = auth.providers()
    repos, pins, env = compiler.setup(auth.MATHLIB, auth.LEAN_BIN)
    plan, reused, compiler, gate, serial = auth.authenticate_partial(auth.STATE, repos, auth.LEAN_BIN, pins)
    # authenticate_partial already checks the stronger first-top-namespace
    # route for every reused record, not merely the first existing deep object.
    input_files = serial.toolchain_inputs(auth.LEAN_BIN)
    for row in reused:
        input_files.update(row['artifacts'])
    start = len(reused)
    fresh = 0
    for index in range(start, min(start+args.batch, auth.FULL_COUNT)):
        auth.require(not (auth.SUPPORT/'PAUSE-BUILDS').exists() and not (auth.HERE/'PAUSE-BUILDS').exists(),
                     'paused before next compiler')
        row = plan['modules'][index]
        auth.namespace_route(row, repos, compiler)
        source, target = Path(row['source']), Path(row['target'])
        auth.require(index >= auth.PREFIX_COUNT and compiler.sha(source) == row['source_sha256'],
                     'new selected source identity differs')
        auth.require(not compiler.artifacts(target), 'unreceipted target family exists; no automatic repair')
        for suffix in ('json', 'stdout', 'stderr'):
            auth.require(not (auth.STATE/f'{index:04d}.{suffix}').exists(), 'unreceipted partial evidence exists')
        source_copy = auth.STATE/'source'/Path(*row['module'].split('.')).with_suffix('.lean')
        copy_exact(source, source_copy, row['source_sha256'])
        target.parent.mkdir(parents=True, exist_ok=True)
        stdout, stderr = auth.STATE/f'{index:04d}.stdout', auth.STATE/f'{index:04d}.stderr'
        started = time.monotonic()
        compiler_code, resource_control = serial.compile_one(auth.expected_command(row), cwd=row['repo'], env=env,
            stdout=stdout, stderr=stderr, input_files=input_files, target=target, index=index, module=row['module'])
        actual = compiler.artifacts(target)
        code = compiler_code if compiler_code else (0 if str(target) in actual else 2)
        receipt = dict(**row, command=auth.expected_command(row), exit_code=code, compiler_exit_code=compiler_code,
            runner_sha256=auth.digest(__file__), authenticator_sha256=auth.LOADED_SHA,
            frozen_helpers_sha256=auth.FROZEN_COMPILER_HELPER_SHA, seconds=time.monotonic()-started,
            execution='FRESH_FULL_EXTERNAL_SOURCE_COMPILE', artifacts=actual,
            stdout_sha256=compiler.sha(stdout), stderr_sha256=compiler.sha(stderr),
            resource_control=resource_control, environment=auth.selected_environment(env),
            guard_output=str(auth.guard_output(args.guard_output)), builder_command=command, fresh_budget=args.batch)
        auth.write_new(auth.STATE/f'{index:04d}.json', receipt)
        print(json.dumps(dict(index=index, module=row['module'], exit_code=code, seconds=receipt['seconds'],
                              receipt_sha256=auth.digest(auth.STATE/f'{index:04d}.json'))), flush=True)
        if code:
            raise SystemExit(1)
        input_files.update(actual)
        fresh += 1
        compiler.release_own_file_cache(repos, auth.LEAN_BIN)
    print(json.dumps(dict(status='BATCH_COMPLETE', freshly_compiled=fresh, authenticated_reuse=start,
        planned=auth.FULL_COUNT, complete=start+fresh == auth.FULL_COUNT,
        complete_authentication_requires_closed_guard=True, no_automatic_next_batch=True)), flush=True)


if __name__ == '__main__':
    main()
