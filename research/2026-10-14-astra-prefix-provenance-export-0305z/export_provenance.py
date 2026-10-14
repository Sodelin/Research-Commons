#!/usr/bin/env python3
"""Draft: assemble a complete, review-pending source/execution origin ledger.

No compiler, subprocess, object read, state mutation, provenance-pin installation,
or historical outcome repair occurs here. Run only after the owner closes 3591.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
OLD = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
STATE = Path('/workspace/scratch/astra-support-external-0840')
LEAN = '/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin/lean'
PLAN_SHA = 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10'
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'
BASELINE_SHA = '75c4ac16fb140e4a5b4e07f01f4dd6c3833b366be6cd1f812a3c608c458edda7'
OLD_MANIFEST_SHA = '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5'
INPUTS_SHA = '23ee1c2fe13891977f7ca907c6b65280c9d13f6514400fd267a39b1767199ba2'
OPTIONS = ['-Dpp.unicode.fun=true', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3']
COUNT = 3591
OLD_FILES = None


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(path):
    return sha(path.read_bytes())


def read(path):
    return json.loads(path.read_text())


def safe(path):
    path = Path(path)
    require(not path.is_symlink() and path.is_file(), 'not a regular evidence file: ' + str(path))
    require(path.resolve().is_relative_to(ROOT / 'research'), 'evidence escapes research')
    return path


def reference(path, locator):
    path = safe(path)
    data = path.read_bytes()
    if path.is_relative_to(OLD) and path != OLD / 'PACKET-MANIFEST.json':
        require(OLD_FILES is not None, 'baseline manifest not loaded')
        selected = OLD_FILES.get(str(path.relative_to(OLD)))
        require(selected is not None and selected['bytes'] == len(data) and
                selected['sha256'] == sha(data), 'baseline evidence differs from frozen publication')
    return dict(path=str(path.relative_to(ROOT)), bytes=len(data), sha256=sha(data), locator=locator)


def pinned(record):
    path = safe(ROOT / record['path'])
    data = path.read_bytes()
    require(len(data) == record['bytes'] and sha(data) == record['sha256'], 'pinned historical input differs')
    return path


def events(path):
    result = []
    for line in path.read_text().splitlines():
        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(entry, dict):
            result.append(entry)
    return result


def guard(path):
    path = safe(path)
    record = read(path)
    require(record.get('runner_sha256') == GUARD_SHA, 'unselected historical guard')
    require(set(record['outputs']) == {'stdout', 'stderr'}, 'guard output names differ')
    refs = [reference(path, 'actual historical guard; resource samples are sampled observations')]
    for suffix in ('stdout', 'stderr'):
        p = path.parent / suffix
        raw = p.read_bytes()
        require(record['outputs'][suffix] == dict(bytes=len(raw), sha256=sha(raw)), 'guard log differs')
        refs.append(reference(p, 'literal guard ' + suffix))
    outcome = ('ERROR' if record.get('error') else
               'SUCCESS' if record['exit_code'] == 0 and record['stop'] is None else 'FAILED_OR_STOPPED')
    return record, refs, outcome


def canonical():
    require(not (SUPPORT / 'PAUSE-BUILDS').exists() and not (HERE / 'PAUSE-BUILDS').exists(), 'paused')
    require(digest(Path(LEAN)) == LEAN_SHA, 'selected compiler executable differs')
    plan_path = SUPPORT / 'EXTERNAL-PLAN.json'
    require(digest(plan_path) == PLAN_SHA and digest(STATE / 'PLAN.json') == PLAN_SHA, 'selected plan differs')
    plan = read(plan_path)['modules']
    require(len(plan) == COUNT, 'selected plan length differs')
    paths = sorted(STATE.glob('[0-9][0-9][0-9][0-9].json'))
    require([p.stem for p in paths] == [f'{i:04d}' for i in range(COUNT)], 'original prefix incomplete or has extra receipts')
    receipts, hashes = [], []
    for index, (path, row) in enumerate(zip(paths, plan)):
        require(not path.is_symlink(), 'canonical receipt symlink')
        data = path.read_bytes()
        receipt = json.loads(data)
        for key in ('source', 'source_sha256', 'repo', 'module', 'target', 'imports'):
            require(receipt[key] == row[key], 'receipt/selected source mismatch: ' + str(index))
        require(receipt['exit_code'] == 0 and receipt['artifacts'].get(row['target']), 'unsuccessful canonical module')
        # Objects are deliberately NOT opened. The future prepare_full gate does that.
        require(digest(Path(row['source'])) == row['source_sha256'], 'selected source bytes differ')
        bare = [LEAN, '-j', '1', '-s', '8192', '-R', row['repo'], '-o', row['target'], row['source']]
        allowed = [bare, [LEAN, '-DElab.async=false', *bare[1:]]]
        if row['module'].startswith('Mathlib.'):
            allowed.append([LEAN, *OPTIONS, *bare[1:]])
        require(receipt['command'] in allowed, 'unreviewed historical compiler command')
        for suffix in ('stdout', 'stderr'):
            p = STATE / f'{index:04d}.{suffix}'
            require(not p.is_symlink() and digest(p) == receipt[suffix + '_sha256'], 'canonical compiler log differs')
        receipts.append(receipt)
        hashes.append(sha(data))
    return receipts, hashes


def captured_row(row, index, receipts, hashes):
    require(row['receipt'] == receipts[index] and row['receipt_sha256'] == hashes[index], 'captured canonical receipt differs')
    for suffix in ('stdout', 'stderr'):
        raw = (STATE / f'{index:04d}.{suffix}').read_bytes()
        require(row[suffix] == dict(bytes=len(raw), sha256=sha(raw), content_utf8=raw.decode('utf-8')), 'embedded compiler log differs')


def build():
    global OLD_FILES
    require(digest(HERE / 'HISTORICAL-INPUTS.json') == INPUTS_SHA, 'historical input registry differs')
    require(digest(OLD / 'PACKET-MANIFEST.json') == OLD_MANIFEST_SHA, 'frozen baseline manifest differs')
    old_rows = read(OLD / 'PACKET-MANIFEST.json')['files']
    OLD_FILES = {r['path']: r for r in old_rows}
    require(len(OLD_FILES) == len(old_rows), 'duplicate frozen baseline path')
    inputs = read(HERE / 'HISTORICAL-INPUTS.json')
    receipts, hashes = canonical()
    origins = {}

    def add(index, refs, outcome, recovery=None, context=None):
        require(index not in origins, 'multiple successful origins for canonical index ' + str(index))
        receipt = receipts[index]
        origins[index] = dict(index=index, receipt_sha256=hashes[index],
            stdout_sha256=receipt['stdout_sha256'], stderr_sha256=receipt['stderr_sha256'],
            compiler_sha256=LEAN_SHA, command=receipt['command'], runner_sha256=receipt.get('runner_sha256'),
            helper_sha256=receipt.get('resource_control', {}).get('helper_sha256'),
            recorded_execution=receipt.get('execution'), recorded_environment=receipt.get('environment'),
            original_outer_guard_outcome=outcome, separate_recovery_authentication=recovery or [],
            evidence=refs, context=context)

    baseline_path = OLD / 'evidence/MATHLIB-SOURCE-EXECUTION.json'
    require(digest(baseline_path) == BASELINE_SHA, 'published baseline ledger differs')
    baseline = read(baseline_path)
    require(baseline['plan']['compiler_sha256'] == LEAN_SHA and len(baseline['compiled_modules']) == 916, 'baseline scope differs')
    base_events = {}
    for directory in sorted((OLD / 'evidence').glob('mathlib-source-batch-[0-9][0-9][0-9]')):
        g, refs, outcome = guard(directory / 'RECEIPT.json')
        require(g['cwd'] in (str(ROOT), str(OLD)) and
                any(Path(x).name == 'build_mathlib_serial.py' for x in g['command']),
                'baseline guard is not the selected serial compiler job')
        for event in events(directory / 'stdout'):
            if 'index' not in event or event.get('exit_code') != 0:
                continue
            i = event['index']
            require(i not in base_events, 'duplicate baseline success event')
            base_events[i] = (event, refs, outcome, g)
    require(set(base_events) == set(range(916)), 'published baseline event coverage differs')
    for i, row in enumerate(baseline['compiled_modules']):
        captured_row(row, i, receipts, hashes)
        event, refs, outcome, g = base_events[i]
        require(event['module'] == receipts[i]['module'] and event['seconds'] == receipts[i]['seconds'], 'baseline event/receipt mismatch')
        add(i, [reference(baseline_path, f'compiled_modules[{i}] exact receipt and logs'),
                reference(OLD / 'PACKET-MANIFEST.json', 'frozen published baseline packet'), *refs], outcome,
            context=dict(outer_exit_code=g['exit_code'], outer_stop=g['stop'], origin='published916'))

    recovered_indices = {i for item in inputs['recoveries'] for i in range(item['first'], item['last'] + 1)}
    for directory in sorted((SUPPORT / 'evidence').glob('external-batch-[0-9][0-9][0-9]')):
        capture_path = directory / 'MODULE-RECEIPTS.json'
        if not capture_path.exists():
            # The three fixed recoveries are handled below; any other missing
            # successful origin remains absent and makes final coverage fail.
            continue
        cap = read(capture_path)
        g, refs, outcome = guard(directory / 'RECEIPT.json')
        expected_prefix = ['/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3',
            '-B', str(SUPPORT / 'build_external_serial.py'), '--mathlib-root',
            '/workspace/scratch/astra-mathlib-0645', '--lean-bin',
            '/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin', '--state', str(STATE), '--batch']
        number = int(directory.name.rsplit('-', 1)[1])
        if number <= 13:
            expected_prefix[2] = str(OLD / 'build_mathlib_serial.py')
        if number == 1:
            expected_prefix[0] = 'python3'
            expected_prefix[2] = str((OLD / 'build_mathlib_serial.py').relative_to(ROOT))
        require(g['cwd'] == str(ROOT) and g['command'][:-1] == expected_prefix and
                g['command'][-1].isdigit() and 1 <= int(g['command'][-1]) <= 128,
                'external capture guard command is not the selected serial job')
        require(cap['guard_receipt_sha256'] == digest(directory / 'RECEIPT.json') and
                cap['guard_exit_code'] == g['exit_code'] and cap['guard_stop'] == g['stop'], 'capture/guard binding differs')
        ev = [x for x in events(directory / 'stdout') if 'index' in x and 'module' in x]
        rows = cap['completed_compiler_invocations']
        require(len(ev) == len(rows), 'capture omits or invents an invocation')
        for position, (event, row) in enumerate(zip(ev, rows)):
            i = row['index']
            require(event['index'] == i and event['module'] == row['receipt']['module'] and
                    event['exit_code'] == row['receipt']['exit_code'], 'capture/event mismatch')
            if row['receipt']['exit_code'] != 0:
                continue  # Retained failure, never substituted for canonical success.
            require(i not in recovered_indices, 'recovered original guard unexpectedly supplied')
            captured_row(row, i, receipts, hashes)
            add(i, [reference(capture_path, f'completed_compiler_invocations[{position}] index{i}'), *refs], outcome,
                context=dict(outer_exit_code=g['exit_code'], outer_stop=g['stop'], origin=directory.name))

    for item in inputs['diagnostics']:
        repair_path, guard_path = pinned(item['repair']), pinned(item['guard'])
        repair = read(repair_path)
        i = item['index']
        require(repair[item['receipt_key']] == receipts[i] and repair[item['receipt_sha_key']] == hashes[i], 'diagnostic adoption differs')
        g, refs, outcome = guard(guard_path)
        require(outcome == 'SUCCESS', 'diagnostic origin was not successful')
        matches = [x for x in events(guard_path.parent / 'stdout') if x.get('module') == receipts[i]['module'] and x.get('exit_code') == 0]
        require(len(matches) == 1, 'diagnostic successful event missing or duplicated')
        add(i, [reference(repair_path, item['receipt_key'] + ' and explicit immutable adoption/repair context'), *refs], outcome,
            context=dict(origin='separately adopted diagnostic', limits=g['limits']))

    for item in inputs['recoveries']:
        gp, rp, fp, lp = [pinned(item[k]) for k in ('guard', 'result', 'files', 'ledger')]
        result, ledger = read(rp), read(lp)
        g, refs, outcome = guard(gp)
        require(outcome == 'SUCCESS', 'separate recovery authentication failed')
        require(result['original_outer_guard_outcome'] == 'UNKNOWN' and
                result['original_outer_guard_receipt_present'] is False and
                result['original_orchestrator_preserved_pending'] is True and
                result['freshly_compiled_in_recovery'] == 0, 'recovery promoted original outcome')
        expected = list(range(item['first'], item['last'] + 1))
        require(result['recovered_module_indices'] == expected and [x['index'] for x in ledger] == expected and
                result['recovered_module_ledger_sha256'] == digest(lp), 'recovery selection differs')
        saved_files = read(fp)['files']
        seen = set()
        for entry in saved_files:
            rel = Path(entry['path'])
            require(not rel.is_absolute() and '..' not in rel.parts and entry['path'] not in seen, 'invalid recovery inventory')
            seen.add(entry['path'])
            p = safe(fp.parent / rel)
            require(p.stat().st_size == entry['bytes'] and digest(p) == entry['sha256'], 'recovery payload differs')
        for row in ledger:
            i = row['index']
            require(row['receipt'] == receipts[i] and row['receipt_sha256'] == hashes[i], 'recovered receipt differs')
            for suffix in ('json', 'stdout', 'stderr'):
                p = lp.parent / 'modules' / f'{i:04d}.{suffix}'
                require(str(p.relative_to(fp.parent)) in seen and p.read_bytes() == (STATE / p.name).read_bytes(), 'recovery copy differs')
            recovery = [reference(rp, 'separate zero-compiler authentication, not original guard outcome'),
                        reference(fp, 'complete preserved recovery inventory'), reference(lp, f'index{i} recovered canonical receipt'), *refs]
            add(i, recovery, 'UNKNOWN', recovery=recovery,
                context=dict(original_outer_exit_code=None, original_outer_wall_seconds=None, original_outer_maxima=None))

    require(set(origins) == set(range(COUNT)), 'unresolved original execution origin(s): ' + str(sorted(set(range(COUNT)) - set(origins))))
    # Close the readback against accidental concurrent mutation. Actual object
    # hashes remain a separate consumer gate, not an inference from this ledger.
    for i, expected in enumerate(hashes):
        require(digest(STATE / f'{i:04d}.json') == expected, 'canonical receipt changed during export')
    return dict(schema='astra_complete3591_origin_ledger_v1', plan_sha256=PLAN_SHA,
        original042_057_059_outer_guards='UNKNOWN', modules=[origins[i] for i in range(COUNT)],
        status='CANDIDATE_PENDING_OWNER_REVIEW_PUBLICATION_AND_FIXED_PIN',
        compiler_objects_reauthenticated=False, source_compilation_performed=False,
        prefix_provenance_pin_installed=False, exporter_sha256=digest(Path(__file__)),
        historical_inputs_sha256=INPUTS_SHA,
        trust_boundary='Historical semantic origin attribution must be independently reviewed before installing a fixed pin; object authentication is deferred to unchanged consumer gates.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.absolute()
    require(out.parent == HERE / 'evidence' and re.fullmatch(r'PREFIX-PROVENANCE-v[1-9][0-9]*\.json', out.name), 'output must be a new own evidence ledger')
    require(not out.exists() and not out.is_symlink(), 'output already exists')
    result = build()
    out.parent.mkdir(exist_ok=True)
    with out.open('x') as handle:
        json.dump(result, handle, indent=2)
        handle.write('\n')
    print(json.dumps(dict(status=result['status'], out=str(out), bytes=out.stat().st_size, sha256=digest(out), modules=COUNT, object_reads=0, compilations=0)))


if __name__ == '__main__':
    main()
