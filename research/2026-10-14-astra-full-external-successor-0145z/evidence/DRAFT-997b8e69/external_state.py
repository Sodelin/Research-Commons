"""Source-only successor authentication; no compiler is launched by this module.

The complete original3591 provenance pin is deliberately unset until that
execution closes and its exact historical origins have been reviewed. This
blocks only this new3661 state, never the existing support adapter.
"""
import hashlib
import json
import os
from pathlib import Path
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PREVIOUS = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
STATE = Path('/workspace/scratch/astra-full-external-0145')
ORIGINAL_STATE = Path('/workspace/scratch/astra-support-external-0840')
MATHLIB = Path('/workspace/scratch/astra-mathlib-0645')
LEAN_BIN = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin')
PYTHON = '/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3'
LEAN_SHA = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
PLAN = ROOT / 'research/2026-10-14-astra-full-accepted-import-query-0100z/evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json'
PLAN_SHA = '0c64ed24f1b9d237a7ccee440e9b360cce7ba797079c02d1b0154473866b1d0a'
ORIGINAL_PLAN_SHA = 'ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10'
PREVIOUS_MANIFEST_SHA = '728246e4960472a7319eb0b979660716d52ec82aa8799a2ef17f8bb23df77ef5'
BASELINE_SHA = '75c4ac16fb140e4a5b4e07f01f4dd6c3833b366be6cd1f812a3c608c458edda7'
FROZEN_COMPILER_HELPER_SHA = '8838b18400dcb2129de366b4e95fa1c8bccdfb5295d119e6d04206b13468cf87'
FROZEN_GATE_SHA = 'f277d3f2aa477245a73abf1007ab50df57b0a24e1de34ff7c2bd414d233c98ee'
SERIAL_SHA = 'd47f2d50afd4648374d7ca1630dce71f3aa09422fe740d356b2d0d9c8ce8ca28'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'
MATHLIB_LAKEFILE_SHA = '9618b4491ba2a0ce2edde2cd29a6ff12974ccec5b331773ad0ae679cbebbc857'
# Review and publish the complete original execution ledger, then replace this
# None in an explicit source successor. A caller cannot supply a desired hash.
PREFIX_PROVENANCE_SHA = None
PREFIX_PROVENANCE = HERE / 'PREFIX-PROVENANCE.json'
PREFIX_COUNT = 3591
FULL_COUNT = 3661
MATHLIB_OPTIONS = ['-Dpp.unicode.fun=true', '-DautoImplicit=false', '-DmaxSynthPendingDepth=3']
ENV_KEYS = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_NUM_THREADS', 'LEAN_STACK_SIZE_KB',
            'LEAN_IMPORT_WORKERS', 'MIMALLOC_ARENA_RESERVE', 'RAYON_NUM_THREADS')
LIMITS = dict(cpu_seconds=600, wall_seconds=900, address_space_bytes=6*1024**3,
              file_bytes=1024**3, disk_floor=8*1024**3, ram_floor=1024**3,
              cgroup_stop=4*1024**3)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for data in iter(lambda: stream.read(1024**2), b''):
            h.update(data)
    return h.hexdigest()


LOADED_SHA = digest(__file__)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def write_new(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def load_exact(name, path, pin):
    require(digest(path) == pin, 'frozen helper source changed: ' + str(path))
    if name in sys.modules:
        module = sys.modules[name]
        require(Path(module.__file__).resolve() == path.resolve(), 'helper import collision')
        require(getattr(module, '_astra_exact_source_sha', None) == pin
                or (name == 'build_mathlib_serial' and getattr(module, 'LOADED_RUNNER_SHA', None) == pin),
                'unbound previously imported helper')
        return module
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module._astra_exact_source_sha = pin
    sys.modules[name] = module
    try:
        exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    except BaseException:
        del sys.modules[name]
        raise
    return module


def providers():
    require(digest(__file__) == LOADED_SHA, 'loaded external authenticator changed')
    require(digest(PREVIOUS/'PACKET-MANIFEST.json') == PREVIOUS_MANIFEST_SHA,
            'published original manifest changed')
    compiler = load_exact('build_mathlib_serial', PREVIOUS/'build_mathlib_serial.py',
                          FROZEN_COMPILER_HELPER_SHA)
    gate = load_exact('astra_full_external_frozen_gate', PREVIOUS/'build_lean.py', FROZEN_GATE_SHA)
    serial = load_exact('astra_full_external_serial_helper', SUPPORT/'serial_compile.py', SERIAL_SHA)
    return compiler, gate, serial


def expected_command(row):
    options = MATHLIB_OPTIONS if row['module'].startswith('Mathlib.') else []
    return [str(LEAN_BIN/'lean'), *options, '-j', '1', '-s', '8192',
            '-R', row['repo'], '-o', row['target'], row['source']]


def selected_environment(env):
    return {**{key: env[key] for key in ENV_KEYS}, 'MALLOC_ARENA_MAX': '1'}


def context(repos, lean_bin, pins):
    require(Path(lean_bin).resolve() == LEAN_BIN and repos[0].resolve() == MATHLIB,
            'fixed compiler/repository locations differ')
    require(digest(PLAN) == PLAN_SHA and digest(SUPPORT/'EXTERNAL-PLAN.json') == ORIGINAL_PLAN_SHA,
            'selected external source plan changed')
    plan, original = read(PLAN), read(SUPPORT/'EXTERNAL-PLAN.json')
    require(len(plan['modules']) == FULL_COUNT and len(original['modules']) == PREFIX_COUNT
            and plan['modules'][:PREFIX_COUNT] == original['modules'], 'literal prefix differs')
    compiler, gate, serial = providers()
    require(plan['compiler_sha256'] == compiler.LEAN_SHA and plan['mathlib_pin'] == compiler.PIN
            and plan['dependencies'] == pins, 'compiler/dependency context differs')
    require(compiler.sha(LEAN_BIN/'lean') == compiler.LEAN_SHA, 'compiler bytes changed')
    require(compiler.sha(MATHLIB/'lakefile.lean') == MATHLIB_LAKEFILE_SHA,
            'selected Mathlib option source changed')
    require(len({r['module'] for r in plan['modules']}) == FULL_COUNT
            and len({r['source'] for r in plan['modules']}) == FULL_COUNT
            and len({r['target'] for r in plan['modules']}) == FULL_COUNT,
            'duplicate source/module/target selection')
    prior = set()
    core = LEAN_BIN.parent/'src/lean'
    for row in plan['modules']:
        source, repo = Path(row['source']), Path(row['repo'])
        relative = Path(*row['module'].split('.')).with_suffix('.lean')
        require(repo in repos and source == repo/relative
                and Path(row['target']) == repo/'.lake/build/lib/lean'/relative.with_suffix('.olean'),
                'external source/target route differs')
        for imported in row['imports']:
            require(Path(imported).is_relative_to(core) or imported in prior,
                    'external import is missing or out of order')
        prior.add(row['source'])
    return plan, compiler, gate, serial


def provenance():
    require(isinstance(PREFIX_PROVENANCE_SHA, str) and len(PREFIX_PROVENANCE_SHA) == 64,
            'complete original3591 provenance has not been reviewed and pinned; new state disabled')
    require(digest(PREFIX_PROVENANCE) == PREFIX_PROVENANCE_SHA,
            'reviewed original execution provenance changed')
    data = read(PREFIX_PROVENANCE)
    require(data['schema'] == 'astra_complete3591_origin_ledger_v1'
            and data['plan_sha256'] == ORIGINAL_PLAN_SHA
            and [r['index'] for r in data['modules']] == list(range(PREFIX_COUNT)),
            'complete original execution provenance scope differs')
    require(data['original042_057_059_outer_guards'] == 'UNKNOWN',
            'historical unknown outer outcomes must remain unknown')
    evidence_pins = {}
    for origin in data['modules']:
        require(origin['evidence'], 'original execution provenance has no evidence locator')
        for evidence in origin['evidence']:
            path = ROOT/evidence['path']
            require(path.resolve().is_relative_to(ROOT/'research') and not path.is_symlink(),
                    'origin evidence must be a regular research artifact')
            pin = (evidence['bytes'], evidence['sha256'])
            if path in evidence_pins:
                require(evidence_pins[path] == pin, 'inconsistent repeated evidence binding')
            else:
                require(path.stat().st_size == evidence['bytes'] and digest(path) == evidence['sha256'],
                        'original execution evidence changed')
                evidence_pins[path] = pin
        if 2499 <= origin['index'] <= 2530 or 2894 <= origin['index'] <= 2925 or 2927 <= origin['index'] <= 2958:
            require(origin['original_outer_guard_outcome'] == 'UNKNOWN'
                    and origin['separate_recovery_authentication'],
                    'recovered module promoted its unknown historical outer guard')
    return data


def original_identity(index, receipt, origin, baseline):
    require(origin['index'] == index and receipt['command'] == origin['command'],
            'original exact compiler command/options differ')
    require(receipt.get('runner_sha256') == origin['runner_sha256']
            and receipt.get('execution') == origin['recorded_execution']
            and receipt.get('environment') == origin['recorded_environment']
            and receipt.get('resource_control', {}).get('helper_sha256') == origin['helper_sha256'],
            'original execution/helper/environment identity differs')
    require(origin['compiler_sha256'] == LEAN_SHA,
            'original compiler identity differs')
    bare = [str(LEAN_BIN/'lean'), '-j', '1', '-s', '8192', '-R', receipt['repo'],
            '-o', receipt['target'], receipt['source']]
    allowed = [bare, [bare[0], '-DElab.async=false', *bare[1:]]]
    if receipt['module'].startswith('Mathlib.'):
        allowed.append([bare[0], *MATHLIB_OPTIONS, *bare[1:]])
    require(receipt['command'] in allowed, 'unreviewed original option family')
    if index < 916:
        published = baseline[index]
        require(receipt == published['receipt'], 'early original receipt differs from published ledger')
    # Missing historical runner/helper fields remain None. The reviewed pinned
    # origin ledger supplies the actual published locator, never an invented ID.


def authenticate_record(directory, index, row, compiler, origin=None, baseline=None):
    path = directory/f'{index:04d}.json'
    receipt = read(path)
    require(all(receipt.get(key) == value for key, value in row.items())
            and receipt['exit_code'] == 0, 'failed/changed selected receipt: ' + row['module'])
    require(compiler.sha(Path(row['source'])) == row['source_sha256'], 'selected source bytes changed')
    for suffix in ('stdout', 'stderr'):
        require(compiler.sha(directory/f'{index:04d}.{suffix}') == receipt[suffix+'_sha256'],
                'original compiler log changed')
    if origin is not None:
        require(digest(path) == origin['receipt_sha256'], 'original receipt bytes changed')
        for suffix in ('stdout', 'stderr'):
            require(receipt[suffix+'_sha256'] == origin[suffix+'_sha256'], 'origin log binding differs')
        original_identity(index, receipt, origin, baseline)
    else:
        require(receipt['command'] == expected_command(row)
                and receipt['runner_sha256'] == digest(HERE/'build_external_full.py')
                and receipt['authenticator_sha256'] == LOADED_SHA
                and receipt['frozen_helpers_sha256'] == FROZEN_COMPILER_HELPER_SHA
                and receipt['resource_control']['helper_sha256'] == SERIAL_SHA
                and receipt['compiler_exit_code'] == 0
                and receipt['execution'] == 'FRESH_FULL_EXTERNAL_SOURCE_COMPILE',
                'new exact compiler/options/helper execution differs')
    return receipt


def guard_output(path):
    path = Path(path)
    require(path.parent == HERE/'evidence' and path.name.startswith(('prepare-', 'full-batch-')),
            'guard output must be a fixed successor evidence child')
    return path


def prepare_command(path):
    return [PYTHON, '-B', str(HERE/'prepare_full.py'), '--guard-output', str(guard_output(path))]


def builder_command(path, budget):
    require(type(budget) is int and budget in (1, 4, 8, 16, 32), 'unsupported explicit fresh budget')
    return [PYTHON, '-B', str(HERE/'build_external_full.py'), '--guard-output',
            str(guard_output(path)), '--batch', str(budget)]


def require_running_guard(path, command):
    """Entry-point check for the fixed direct guard, before any state mutation."""
    path = guard_output(path)
    require(not (SUPPORT/'PAUSE-BUILDS').exists() and not (HERE/'PAUSE-BUILDS').exists(),
            'build lane paused')
    expected = [PYTHON, str(PREVIOUS/'guard.py'), '--out', str(path), '--cwd', str(ROOT),
                '--wall', '900', '--cpu', '600', '--memory-mib', '6144', '--file-mib', '1024',
                '--', *command]
    argv = (Path('/proc')/str(os.getppid())/'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
    require(argv == expected and digest(PREVIOUS/'guard.py') == GUARD_SHA,
            'successor requires its exact direct frozen guard command')


def authenticate_guard(path, command):
    path = guard_output(path)
    guard = read(path/'RECEIPT.json')
    require(guard['runner_sha256'] == GUARD_SHA and digest(PREVIOUS/'guard.py') == GUARD_SHA
            and guard['limits'] == LIMITS and guard['cwd'] == str(ROOT)
            and guard['command'] == command, 'closed guard invocation/profile differs')
    require(not guard.get('error'), 'guard exception is not a completed batch')
    for suffix in ('stdout', 'stderr'):
        output = path/suffix
        require(output.stat().st_size == guard['outputs'][suffix]['bytes']
                and digest(output) == guard['outputs'][suffix]['sha256'], 'closed guard log differs')
    return guard


def reuse_wrapper(index, receipt, origin):
    return dict(schema='astra_full_external_reuse_v1', execution='AUTHENTICATED_REUSE',
        index=index, module=receipt['module'], original_state=str(ORIGINAL_STATE),
        original_plan_sha256=ORIGINAL_PLAN_SHA, original_receipt_sha256=origin['receipt_sha256'],
        prefix_provenance_sha256=PREFIX_PROVENANCE_SHA, original_execution=origin['recorded_execution'],
        original_runner_sha256=origin['runner_sha256'], original_helper_sha256=origin['helper_sha256'],
        original_outer_guard_outcome=origin['original_outer_guard_outcome'],
        separate_recovery_authentication=origin['separate_recovery_authentication'],
        evidence=origin['evidence'], source_compilation_performed=False)


def authenticate_partial(state, repos, lean_bin, pins, *, require_complete=False):
    require(Path(state).resolve() == STATE, 'new external state path differs')
    origins = provenance()
    plan, compiler, gate, serial = context(repos, lean_bin, pins)
    baseline_path = PREVIOUS/'evidence/MATHLIB-SOURCE-EXECUTION.json'
    require(digest(baseline_path) == BASELINE_SHA, 'original published execution archive changed')
    baseline = read(baseline_path)['compiled_modules']
    require((STATE/'PLAN.json').read_bytes() == PLAN.read_bytes()
            and digest(STATE/'PREFIX-PROVENANCE.json') == PREFIX_PROVENANCE_SHA,
            'new state plan/provenance copy differs')
    initialization = read(STATE/'INITIALIZATION.json')
    require(initialization['prefix_provenance_sha256'] == PREFIX_PROVENANCE_SHA
            and initialization['plan_sha256'] == PLAN_SHA
            and initialization['prepare_runner_sha256'] == digest(HERE/'prepare_full.py')
            and initialization['authenticator_sha256'] == LOADED_SHA
            and initialization['reused'] == PREFIX_COUNT and initialization['source_compilations'] == 0
            and initialization['originals_mutated'] is False
            and initialization['original042_057_059_outer_guards'] == 'UNKNOWN'
            and set(initialization['reuse_wrapper_sha256']) == {str(i) for i in range(PREFIX_COUNT)},
            'new state initialization binding differs')
    require(initialization['command'] == prepare_command(initialization['guard_output']),
            'initialization command differs from fixed preparation')
    initial_guard = authenticate_guard(initialization['guard_output'], initialization['command'])
    require(initial_guard['exit_code'] == 0 and initial_guard['stop'] is None,
            'original reuse preparation did not finish under its guard')
    initial_events = []
    for line in (Path(initialization['guard_output'])/'stdout').read_text().splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(event, dict) and event.get('status') == 'ORIGINAL_PREFIX_PRESERVED_AFTER_AUTHENTICATION':
            initial_events.append(event)
    require(initial_events == [dict(status='ORIGINAL_PREFIX_PRESERVED_AFTER_AUTHENTICATION',
        reused=PREFIX_COUNT, source_compilations=0,
        initialization_sha256=digest(STATE/'INITIALIZATION.json'))],
        'actual preparation output does not bind this initialization')
    indices = sorted(int(p.stem) for p in STATE.glob('*.json') if p.stem.isdigit())
    require(PREFIX_COUNT <= len(indices) <= FULL_COUNT and indices == list(range(len(indices))),
            'new state receipts are incomplete, gapped or out of range')
    if require_complete:
        require(len(indices) == FULL_COUNT, 'new external closure is not complete')
    rows = []
    for index in indices:
        row = plan['modules'][index]
        origin = origins['modules'][index] if index < PREFIX_COUNT else None
        receipt = authenticate_record(STATE, index, row, compiler, origin, baseline)
        source_copy = STATE/'source'/Path(*row['module'].split('.')).with_suffix('.lean')
        require(compiler.sha(source_copy) == row['source_sha256'], 'preserved source copy differs')
        if origin is not None:
            wrapper_path = STATE/'reuse'/f'{index:04d}.json'
            require(read(wrapper_path) == reuse_wrapper(index, receipt, origin)
                    and initialization['reuse_wrapper_sha256'][str(index)] == digest(wrapper_path),
                    'authenticated reuse wrapper changed')
            execution = 'AUTHENTICATED_REUSE'
            provenance_row = read(wrapper_path)
        else:
            require(receipt['builder_command'] == builder_command(receipt['guard_output'], receipt['fresh_budget']),
                    'fresh successor builder command differs')
            expected_env = dict(LEAN_PATH=os.pathsep.join(str(p/'.lake/build/lib/lean') for p in repos),
                LEAN_SRC_PATH=os.pathsep.join(map(str, [*repos, LEAN_BIN.parent/'src/lean'])),
                LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='8192', LEAN_IMPORT_WORKERS='1',
                MIMALLOC_ARENA_RESERVE='16384', RAYON_NUM_THREADS='1', MALLOC_ARENA_MAX='1')
            require(receipt['environment'] == expected_env, 'fresh external import environment changed')
            guard = authenticate_guard(receipt['guard_output'], receipt['builder_command'])
            events = []
            for line in (Path(receipt['guard_output'])/'stdout').read_text().splitlines():
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if event.get('index') == index and event.get('module') == row['module']:
                    events.append(event)
            require(len(events) == 1 and events[0]['exit_code'] == 0
                    and events[0]['receipt_sha256'] == digest(STATE/f'{index:04d}.json'),
                    'actual guarded output omits successful module event')
            execution = 'FRESH_FULL_EXTERNAL_SOURCE_COMPILE'
            provenance_row = dict(execution=execution, guard_receipt_sha256=digest(Path(receipt['guard_output'])/'RECEIPT.json'),
                                  outer_guard_exit_code=guard['exit_code'], outer_guard_stop=guard['stop'],
                                  command=receipt['command'], runner_sha256=receipt['runner_sha256'])
        actual = compiler.artifacts(Path(row['target']))
        require(str(row['target']) in actual and actual == receipt['artifacts'], 'changed external artifacts')
        rows.append(dict(module=row['module'], source_sha256=row['source_sha256'],
                         receipt_sha256=digest(STATE/f'{index:04d}.json'), artifacts=actual,
                         execution=execution, original_execution=receipt.get('execution'),
                         provenance=provenance_row))
    return plan, rows, compiler, gate, serial


def authenticate_complete(state, repos, lean_bin, pins):
    """Full-owned consumer API; complete exact evidence or an explicit refusal."""
    plan, rows, compiler, gate, serial = authenticate_partial(state, repos, lean_bin, pins,
                                                             require_complete=True)
    checked = gate.verify_dependency_state(STATE, repos, lean_bin, pins)
    basic = [{key: row[key] for key in ('module', 'source_sha256', 'receipt_sha256', 'artifacts')}
             for row in rows]
    require(checked['plan_sha256'] == PLAN_SHA and checked['modules'] == basic,
            'frozen complete object/import-shadowing gate disagrees')
    return dict(plan_sha256=PLAN_SHA, modules=rows,
        execution='Original3591 authenticated reuse plus70 actual recorded successor compilations; see per-module origins',
        original_plan_sha256=ORIGINAL_PLAN_SHA, prefix_provenance_sha256=PREFIX_PROVENANCE_SHA,
        authenticator_sha256=LOADED_SHA, original042_057_059_outer_guards='UNKNOWN',
        source_query_is_not_compilation=True, aggregate_is_not_full_fresh_rebuild=True)
