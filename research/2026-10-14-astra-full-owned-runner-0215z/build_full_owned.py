#!/usr/bin/env python3
"""Source-only full-owned runner draft; launch blocked until complete original provenance is frozen.

One explicit guarded batch, never automatic continuation. No Lake/final-audit
success follows from component receipts. All old sources/states are preserved.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import time

ROOT = Path('/workspace/Research-Commons')
HERE = ROOT / 'research/2026-10-14-astra-full-owned-runner-0215z'
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
PREVIOUS = ROOT / 'research/2026-10-13-astra-unified-solver-0645z'
SOURCE = Path('/workspace/scratch/astra-unified-extension-sources-2340')
STATE = Path('/workspace/scratch/astra-full-owned-0145')
EXTERNAL = Path('/workspace/scratch/astra-full-external-0145')
NARROW_SOURCE = Path('/workspace/scratch/astra-support-sources-0936')
NARROW_STATE = Path('/workspace/scratch/astra-support-owned-namespace-0025')
NARROW_EXTERNAL = Path('/workspace/scratch/astra-support-external-0840')
MATHLIB = Path('/workspace/scratch/astra-mathlib-0645')
LEAN_BIN = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin')
PYTHON = Path('/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3')
PYTHON_SHA = 'fa67443527ed9647f760d807e2a38f26340757123e643c4639cf273ed15d5ea7'
NARROW_SHA = '2d5c8504c9380b5b2353539560b5b8e954cb2e909a09e5e80903214fc346ccda'
OWNED_PLAN = ROOT / 'research/2026-10-14-astra-full-owned-plan-0145z/FULL-OWNED-SOURCE-PLAN.json'
OWNED_PLAN_SHA = 'b4c7448756ac891e83ebd357c24e75e0c0d2d41ac369ce33744dfdf38170a501'
SELECTION = ROOT / 'research/2026-10-14-astra-full-accepted-import-query-0100z/FULL-SOURCE-SELECTION.json'
NAMESPACE = ROOT / 'research/2026-10-14-astra-full-owned-namespace-0158z/namespace_resolution_full.py'
EXTERNAL_HELPER = ROOT / 'research/2026-10-14-astra-full-external-successor-0145z/external_state.py'
# Complete original provenance is absent; this exact source pin record blocks launch.
UPSTREAM_PINS_SHA = 'a115ecaec9c613749c20c8f14903d32e08618936412d4df1933bf39900d77340'
LOADED_SHA = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ir', '.ir.sig')


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1024**2), b''):
            h.update(block)
    return h.hexdigest()


def binding(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write_new(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        stream.write(json.dumps(value, indent=2, sort_keys=True) + '\n')


def preserve(path, destination):
    path, destination = Path(path), Path(destination)
    if path.is_symlink() or destination.exists() or destination.is_symlink():
        raise ValueError('source symlink or existing evidence destination: ' + str(path))
    destination.parent.mkdir(parents=True, exist_ok=True)
    with path.open('rb') as src, destination.open('xb') as dst:
        shutil.copyfileobj(src, dst)
    if digest(path) != digest(destination):
        raise ValueError('preserved bytes differ: ' + str(path))
    return dict(path=str(destination), sha256=digest(destination))


def relative(name):
    return Path(*name.split('.')).with_suffix('.lean')


def load(name, path):
    path = Path(path)
    if name in sys.modules:
        module = sys.modules[name]
        if Path(module.__file__).resolve() != path:
            raise ValueError('loaded helper origin differs: ' + name)
        return module
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def pin_gate():
    if Path(__file__).resolve() != HERE / 'build_full_owned.py' or digest(__file__) != LOADED_SHA:
        raise ValueError('fixed runner location or loaded source differs')
    if UPSTREAM_PINS_SHA is None:
        raise ValueError('LAUNCH_BLOCKED: full external authenticator source/provenance pins not frozen')
    path = HERE / 'UPSTREAM-PINS.json'
    if digest(path) != UPSTREAM_PINS_SHA:
        raise ValueError('upstream source-pin record differs')
    pins = read(path)
    if not pins['external_authenticator_sha256']:
        raise ValueError('LAUNCH_BLOCKED: missing authenticated helper source pin')
    for row in pins['files']:
        if digest(row['path']) != row['sha256']:
            raise ValueError('pinned helper/configuration changed: ' + row['path'])
    if digest(EXTERNAL_HELPER) != pins['external_authenticator_sha256']:
        raise ValueError('external authenticator changed')
    if not pins['launch_ready']:
        raise ValueError('LAUNCH_BLOCKED: ' + pins['remaining_launch_blocker'])
    if digest(PYTHON) != PYTHON_SHA or Path(sys.executable).resolve() != PYTHON.resolve():
        raise ValueError('Python executable differs')
    if not sys.dont_write_bytecode:
        raise ValueError('invoke pinned Python with -B; no imported-helper bytecode writes')
    return pins


def check_pause():
    paused = [str(path) for path in (SUPPORT/'PAUSE-BUILDS', HERE/'PAUSE-BUILDS')
              if path.exists() or path.is_symlink()]
    if paused:
        raise ValueError('PAUSE-BUILDS present; preserve state and stop: ' + ', '.join(paused))


def guard_context():
    command = (Path('/proc') / str(os.getppid()) / 'cmdline').read_bytes().rstrip(b'\0').decode().split('\0')
    if len(command) < 4:
        raise ValueError('the exact pinned outer guard must be the direct parent')
    guard_output = Path(command[3])
    child_command = [str(PYTHON), '-B', str(HERE/'build_full_owned.py'), *sys.argv[1:]]
    expected = [str(PYTHON), str(PREVIOUS/'guard.py'), '--out', str(guard_output),
                '--cwd', str(ROOT), '--wall', '900', '--cpu', '600',
                '--memory-mib', '6144', '--file-mib', '1024', '--', *child_command]
    if command != expected:
        raise ValueError('exact direct-parent guard argv differs')
    # The unchanged guard creates --out exclusively before launching its child.
    # Its live directory contains only the two active output streams; the
    # independent final RECEIPT.json is not yet available to this child.
    if (not guard_output.is_absolute() or guard_output.resolve() != guard_output
            or not guard_output.is_dir()
            or {p.name for p in guard_output.iterdir()} != {'stdout', 'stderr'}):
        raise ValueError('actual guard output is not its fresh canonical live directory')
    for fd, name in [(1, 'stdout'), (2, 'stderr')]:
        output = guard_output/name
        if (output.is_symlink() or not output.is_file()
                or Path(f'/proc/self/fd/{fd}').resolve() != output):
            raise ValueError('actual child output is not the pinned parent guard stream')
    limits = {resource.RLIMIT_AS: 6 * 1024**3, resource.RLIMIT_CPU: 600,
              resource.RLIMIT_FSIZE: 1024**3}
    if any(resource.getrlimit(key) != (value, value) for key, value in limits.items()):
        raise ValueError('inherited resource ceilings differ')
    return dict(parent_command=command, child_command=child_command,
                output_directory=str(guard_output),
                separate_final_receipt=str(guard_output/'RECEIPT.json'),
                guard_sha256=digest(PREVIOUS / 'guard.py'),
                virtual_bytes=6 * 1024**3, physical_stop_bytes=4 * 1024**3,
                wall_seconds=900, cpu_seconds=600, file_bytes=1024**3,
                disk_floor_bytes=8 * 1024**3, ram_floor_bytes=1024**3,
                final_guard_receipt='SEPARATE_PENDING_NOT_INFERRED_FROM_BUILDER_EXIT')


def authenticate_sources():
    if digest(OWNED_PLAN) != OWNED_PLAN_SHA:
        raise ValueError('full owned plan differs')
    plan, selection = read(OWNED_PLAN), read(SELECTION)
    if digest(SELECTION) != plan['source_selection_sha256']:
        raise ValueError('full source selection differs')
    if SOURCE.resolve() != SOURCE or STATE.resolve() != STATE:
        raise ValueError('fixed source/state path is not canonical')
    if plan['materialized_source'] != str(SOURCE) or plan['proposed_fresh_owned_state'] != str(STATE):
        raise ValueError('planned source/state differs')
    modules = plan['modules']
    if len(modules) != 1641 or len(selection['sources']) != 1642:
        raise ValueError('full source scope differs')
    selected = {r['module']: r for r in selection['sources']}
    wanted = set()
    for row in selection['sources']:
        path = Path(row['source'])
        if path != SOURCE / row['destination'] or path.resolve() != path or path.is_symlink():
            raise ValueError('selected source route differs')
        if digest(path) != row['sha256']:
            raise ValueError('selected source bytes differ: ' + row['module'])
        for origin in row['origins']:
            if digest(ROOT / origin['path']) != row['sha256']:
                raise ValueError('selected source provenance differs')
        wanted.add(path)
    actual = {p for p in SOURCE.rglob('*.lean') if '.lake' not in p.relative_to(SOURCE).parts}
    if actual != wanted:
        raise ValueError('unselected or missing materialized Lean source')
    for row in modules:
        original = selected[row['module']]
        if row['source_sha256'] != original['sha256'] or row['imports'] != original['imports']:
            raise ValueError('selected module/import mismatch')
    return plan, modules


def files_under(directory):
    if not directory.exists():
        return set()
    paths = set()
    for p in directory.rglob('*'):
        if p.is_symlink():
            raise ValueError('symlink in owned evidence/state: ' + str(p))
        if p.is_file():
            paths.add(str(p))
    return paths


def authenticate_narrow(evidence, helpers, pins):
    """Delegate the old kernel gate unchanged; never reconstruct its provenance."""
    command = [str(PYTHON), '-B', str(SUPPORT / 'build_support_namespace.py'),
               '--source-root', str(NARROW_SOURCE), '--external-state', str(NARROW_EXTERNAL),
               '--state', str(NARROW_STATE), '--mathlib-root', str(MATHLIB),
               '--lean-bin', str(LEAN_BIN), '--authenticate-only']
    out, err = evidence / 'narrow-auth.stdout', evidence / 'narrow-auth.stderr'
    if digest(SUPPORT / 'build_support_namespace.py') != NARROW_SHA:
        raise ValueError('unchanged narrow authenticator differs')
    child_env = dict(helpers['env'], MALLOC_ARENA_MAX='1', PYTHONDONTWRITEBYTECODE='1')
    write_new(evidence / 'narrow-auth-command.json', dict(command=command, cwd=str(ROOT),
        runner_sha256=NARROW_SHA, python_sha256=PYTHON_SHA,
        environment=dict(helpers['namespace'].selected_environment(child_env)),
        compiler_invocations_requested=0, complete_state_required=True))
    started = time.monotonic()
    with out.open('xb') as stdout, err.open('xb') as stderr:
        result = subprocess.run(command, cwd=ROOT, env=child_env, stdout=stdout, stderr=stderr)
    record = dict(command=command, exit_code=result.returncode, seconds=time.monotonic()-started,
                  stdout_sha256=digest(out), stderr_sha256=digest(err))
    write_new(evidence / 'narrow-auth-result.json', record)
    if result.returncode:
        raise ValueError('completed narrow state authentication failed; preserved exact child logs')
    plan = read(NARROW_STATE / 'PLAN.json')
    if len(plan['modules']) != 326 or plan['runner_sha256'] != NARROW_SHA:
        raise ValueError('narrow state is not the exact completed326 successor')
    if sorted(p.stem for p in NARROW_STATE.glob('[0-9][0-9][0-9][0-9].json')) != [f'{i:04d}' for i in range(326)]:
        raise ValueError('narrow receipt set is not exactly complete')
    parsed = [json.loads(line) for line in out.read_text().splitlines() if line.startswith('{')]
    summary = parsed[-1] if parsed else {}
    if not summary.get('complete') or summary.get('planned') != 326:
        raise ValueError('narrow child did not report the complete authenticated state')
    previous = read(NARROW_STATE / 'RESULT.json')
    if previous['status'] != 'EXACT_ACCEPTED_PROVIDER_AND_SUPPORT_ADAPTER_VERIFIED':
        raise ValueError('narrow result status differs')
    context = {name: preserve(NARROW_STATE / name, evidence / 'narrow-context' / name)
               for name in ['PLAN.json', 'NAMESPACE-RESOLUTION.json', 'RESULT.json']}
    rows = {}
    for i, row in enumerate(plan['modules']):
        receipt = NARROW_STATE / f'{i:04d}.json'
        observed = read(receipt)
        if observed['module'] != row['module'] or observed['source_sha256'] != row['sha256'] or observed['exit_code'] != 0:
            raise ValueError('narrow successful source/receipt differs')
        rows[row['module']] = dict(index=i, plan_row=row, receipt=observed,
            receipt_path=str(receipt), receipt_sha256=digest(receipt),
            source_path=str(NARROW_SOURCE / relative(row['module'])))
    return rows, dict(command=command, command_receipt_sha256=digest(evidence/'narrow-auth-command.json'),
                      result_receipt_sha256=digest(evidence/'narrow-auth-result.json'), context=context)


def authenticate_artifacts(helpers, expected, target):
    actual = helpers['base'].artifacts(target)
    if str(target) not in actual or actual != expected:
        raise ValueError('owned artifacts absent/changed: ' + str(target))
    return set(actual)


def remap_artifacts(origin, target):
    mapped = {}
    for name, sha in origin.items():
        suffix = next((x for x in sorted(SUFFIXES, key=len, reverse=True) if name.endswith(x)), None)
        if suffix is None or str(target.with_suffix(suffix)) in mapped:
            raise ValueError('invalid/ambiguous origin artifact suffix')
        mapped[str(target.with_suffix(suffix))] = sha
    if str(target) not in mapped:
        raise ValueError('origin has no Lean object')
    return mapped


def expected_origin(name, row, external_rows, external_index, narrow):
    if name.startswith('Mathlib.'):
        original = external_rows[name]
        if original['source_sha256'] != row['source_sha256']:
            raise ValueError('selected Mathlib is not byte-identical to external source')
        receipt = EXTERNAL / f'{external_index[name]:04d}.json'
        if digest(receipt) != original['receipt_sha256']:
            raise ValueError('full external canonical receipt differs from authenticator output')
        return dict(kind='AUTHENTICATED_FULL_EXTERNAL_MATHLIB', authenticated_row=original,
                    original_receipt=read(receipt), receipt_path=str(receipt),
                    receipt_sha256=digest(receipt), artifacts=original['artifacts'])
    if name in narrow:
        original = narrow[name]
        if original['receipt']['source_sha256'] != row['source_sha256']:
            raise ValueError('selected prior reuse version differs: ' + name)
        if digest(original['source_path']) != row['source_sha256']:
            raise ValueError('selected prior source bytes differ: ' + name)
        declared_imports = original['plan_row'].get('imports')
        if declared_imports is not None and declared_imports != row['imports']:
            raise ValueError('selected prior direct imports differ: ' + name)
        return dict(kind='AUTHENTICATED_COMPLETED_NARROW_STATE', original_receipt=original['receipt'],
                    receipt_path=original['receipt_path'], receipt_sha256=original['receipt_sha256'],
                    original_index=original['index'], artifacts=original['receipt']['artifacts'],
                    selected_imports=row['imports'], import_match='complete identical source body; original declared imports checked when present')
    return None


def import_bindings(row, helpers, external_rows, external_sources, completed, owned_names):
    roots = [Path(p) for p in helpers['namespace_binding']['external_roots']] + [helpers['build']]
    core = LEAN_BIN.parent / 'lib/lean'
    result = []
    for name in row['imports']:
        root = helpers['namespace'].first_namespace_root(name, roots)
        if name in external_rows:
            expected = Path(external_sources[name]['target']);origin = external_rows[name]
            mode = 'AUTHENTICATED_EXTERNAL'; sha = origin['receipt_sha256']; objs = origin['artifacts']
        elif name in owned_names:
            if name not in completed:
                raise ValueError('owned dependency is not in the authenticated contiguous prefix: ' + name)
            expected = helpers['build'] / relative(name).with_suffix('.olean')
            origin = completed[name];mode = 'AUTHENTICATED_OWNED_PREFIX'
            sha = origin['receipt_sha256'];objs = origin['receipt']['artifacts']
        else:
            if root is not None:
                raise ValueError('unselected external/owned namespace masks toolchain import: ' + name)
            root = helpers['namespace'].first_namespace_root(name, [core])
            expected = core / relative(name).with_suffix('.olean')
            if root != core or not expected.is_file():
                raise ValueError('unknown or absent toolchain import: ' + name)
            mode='TRUSTED_PINNED_TOOLCHAIN_IMPORT';sha=None;objs=helpers['base'].artifacts(expected)
        actual = root / relative(name).with_suffix('.olean') if root else None
        if actual != expected or str(expected) not in objs:
            raise ValueError('actual dependency lookup differs: ' + name)
        result.append(dict(module=name, target=str(expected), mode=mode,
                           receipt_sha256=sha, artifacts=objs))
    return result


def audit_logs(helpers, stdout, stderr):
    text = Path(stdout).read_text() + '\n' + Path(stderr).read_text()
    if "declaration uses 'sorry'" in text:
        raise ValueError('actual placeholder warning rejected')
    return helpers['audit'].audit(text)


def origin_snapshot_paths(origin):
    p = Path(origin['receipt_path']); paths = [p]
    for suffix in ['stdout', 'stderr']:
        log = p.with_suffix('.'+suffix)
        expected = origin['original_receipt'].get(suffix+'_sha256')
        if expected is not None:
            if digest(log) != expected:
                raise ValueError('authenticated origin log changed')
            paths.append(log)
    wrapper = p.parent / 'reuse' / p.name
    if origin['kind'] == 'AUTHENTICATED_FULL_EXTERNAL_MATHLIB' and wrapper.exists():
        paths.append(wrapper)
    return paths


def authenticate_prefix(modules, helpers, external_rows, external_sources, external_index, narrow, plan_sha):
    indices = sorted(int(p.stem) for p in STATE.glob('[0-9][0-9][0-9][0-9].json'))
    if indices != list(range(len(indices))) or len(indices) > len(modules):
        raise ValueError('owned receipts are not a strict contiguous prefix')
    allowed = {str(STATE/'PLAN.json'), str(STATE/'NAMESPACE-RESOLUTION.json')}
    completed = {}; owned_names={r['module'] for r in modules}
    inputs = set(helpers['base_inputs'])
    for i in indices:
        check_pause()
        row=modules[i];name=row['module'];receipt=STATE/f'{i:04d}.json';record=read(receipt)
        target=helpers['build']/relative(name).with_suffix('.olean');saved=STATE/'source'/relative(name)
        common=receipt_common(i,row,helpers,plan_sha,import_bindings(row,helpers,external_rows,external_sources,completed,owned_names))
        if any(record.get(k)!=v for k,v in common.items()) or record['exit_code']!=0:
            raise ValueError('failed/altered owned receipt: '+name)
        if digest(saved)!=row['source_sha256']:
            raise ValueError('saved selected source changed: '+name)
        attempt_path=Path(record['attempt']['path'])
        if (attempt_path.name!='ATTEMPT.json' or attempt_path.parent.parent!=HERE/'evidence'
                or digest(attempt_path)!=record['attempt']['sha256']):
            raise ValueError('original guarded attempt evidence changed')
        attempt=read(attempt_path)
        if (attempt['runner_sha256']!=LOADED_SHA or attempt['state']!=str(STATE)
                or attempt['source']!=str(SOURCE) or attempt['upstream_pin_record_sha256']!=UPSTREAM_PINS_SHA
                or attempt['guard']['guard_sha256']!=digest(PREVIOUS/'guard.py')
                or attempt['command']!=attempt['guard']['child_command']):
            raise ValueError('original guarded attempt context differs')
        allowed.update([str(receipt),str(saved)])
        allowed.update(authenticate_artifacts(helpers,record['artifacts'],target))
        origin=expected_origin(name,row,external_rows,external_index,narrow)
        if record['execution']=='AUTHENTICATED_REUSE':
            if origin is None or record['origin']!=origin or record['axioms']!={}:
                raise ValueError('reuse origin/mode differs: '+name)
            if record['artifacts']!=remap_artifacts(origin['artifacts'],target):
                raise ValueError('cloned artifacts differ from authenticated origin')
            originals=origin_snapshot_paths(origin)
            expected_snapshots=[]
            for number, original in enumerate(originals):
                snapshot=STATE/'origins'/f'{i:04d}'/f'{number:02d}-{original.name}'
                expected_snapshots.append(dict(path=str(snapshot),sha256=digest(original)))
            if record['origin_snapshots']!=expected_snapshots:
                raise ValueError('saved origin inventory differs')
            for p in expected_snapshots:
                if digest(p['path'])!=p['sha256']:raise ValueError('saved origin bytes changed')
                allowed.add(p['path'])
        elif record['execution']=='FRESH_SOURCE_COMPILE':
            if origin is not None or record['command']!=compile_command(name,target) or record['compiler_exit_code']!=0:
                raise ValueError('fresh mode or compiler command differs')
            if record['resource_control']['helper_sha256']!=digest(SUPPORT/'serial_compile.py'):
                raise ValueError('serial helper differs')
            policy = record['resource_control']
            if (policy['input_inventory_sha256'] != hashlib.sha256(json.dumps(sorted(inputs)).encode()).hexdigest()
                    or policy['input_files'] != len(inputs) or policy['malloc_arena_max'] != '1'
                    or policy['outer_limits_changed'] or policy['files_changed'] or policy['system_settings_changed']):
                raise ValueError('serial input/control binding differs')
            out,err=STATE/f'{i:04d}.stdout',STATE/f'{i:04d}.stderr'
            if digest(out)!=record['stdout_sha256'] or digest(err)!=record['stderr_sha256']:
                raise ValueError('owned compiler logs changed')
            if audit_logs(helpers,out,err)!=record['axioms']:
                raise ValueError('actual axiom metadata changed')
            allowed.update([str(out),str(err)])
        else:raise ValueError('unknown execution mode')
        completed[name]=dict(receipt=record,receipt_sha256=digest(receipt))
        inputs.update(record['artifacts'])
    complete_file=STATE/'COMPONENTS-COMPLETE.json'
    if complete_file.exists():
        if len(indices)!=len(modules) or read(complete_file)!=component_result(modules,completed,helpers,plan_sha):
            raise ValueError('component completion record changed or premature')
        allowed.add(str(complete_file))
    if files_under(STATE)!=allowed:
        raise ValueError('unreceipted leftovers or missing owned evidence; preserve and repair explicitly')
    # Empty directories can shadow a later Lean namespace even without objects.
    allowed_directories = {STATE}
    for path in allowed:
        parent = Path(path).parent
        while parent != STATE:
            if not parent.is_relative_to(STATE):raise ValueError('allowed path escapes state')
            allowed_directories.add(parent);parent=parent.parent
    actual_directories = {p for p in STATE.rglob('*') if p.is_dir()}
    if actual_directories - allowed_directories:
        raise ValueError('unreceipted owned directory/namespace; preserve and repair explicitly')
    return completed,allowed


def prefix_token(plan_sha, namespace_sha, completed):
    return binding(dict(plan_sha256=plan_sha,namespace_sha256=namespace_sha,
                        receipts={name:r['receipt_sha256'] for name,r in completed.items()}))


def receipt_common(index,row,helpers,plan_sha,imports):
    return dict(index=index,module=row['module'],kind=row['kind'],source=row['source'],
                source_sha256=row['source_sha256'],source_provenance=row['provenance'],
                selected_imports=row['imports'],resolved_imports=imports,plan_sha256=plan_sha,
                namespace_sha256=helpers['namespace_sha'],runner_sha256=LOADED_SHA,
                environment=helpers['namespace'].selected_environment(helpers['env']),
                compiler_sha256=helpers['base'].LEAN_SHA,mathlib_pin=helpers['base'].PIN,
                serial_helper_sha256=digest(SUPPORT/'serial_compile.py'))


def compile_command(name,target):
    return [str(LEAN_BIN/'lean'),'-j','1','-s','8192','-R',str(SOURCE),'-o',str(target),str(SOURCE/relative(name))]


def component_result(modules,completed,helpers,plan_sha):
    return dict(status='ALL_SELECTED_COMPONENT_RECEIPTS_AUTHENTICATED',planned=len(modules),
                plan_sha256=plan_sha,namespace_sha256=helpers['namespace_sha'],
                receipt_sha256={name:r['receipt_sha256'] for name,r in completed.items()},
                historical_fresh_receipts=sum(r['receipt']['execution']=='FRESH_SOURCE_COMPILE' for r in completed.values()),
                authenticated_reuse_wrappers=sum(r['receipt']['execution']=='AUTHENTICATED_REUSE' for r in completed.values()),
                actual_final_lake_run=False,full_declared_interface_axiom_audit=False,
                native_universal_correctness=False,physical_representative=False,
                interpretation='Component completion only; final Lake, actual interface audit and their closed guards remain separate.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--batch',type=int,choices=range(1,17))
    parser.add_argument('--resume',action='store_true')
    parser.add_argument('--resume-token',help='Exact prior prefix token from the owner-verified closed batch; never infer it from modified current files.')
    parser.add_argument('--authenticate-only',action='store_true')
    parser.add_argument('--evidence',type=Path,required=True)
    args=parser.parse_args()
    if args.authenticate_only:
        if args.batch is not None or not args.resume:parser.error('authenticate-only requires --resume and no --batch')
    elif args.batch is None:parser.error('an explicit --batch1..16 is required')
    if args.resume != (args.resume_token is not None):parser.error('--resume and --resume-token are required together')
    check_pause()
    pins=pin_gate();guard=guard_context()
    evidence=args.evidence
    if not evidence.is_absolute() or evidence.resolve()!=evidence or evidence.parent!=HERE/'evidence' or evidence.exists():
        raise ValueError('a fresh direct child of this packet evidence directory is required')
    if STATE.is_symlink() or (STATE.exists()!=args.resume):
        raise ValueError('fresh state must be absent; existing state needs explicit --resume')
    check_pause()
    evidence.mkdir(parents=True,exist_ok=False)
    write_new(evidence/'ATTEMPT.json',dict(command=guard['child_command'],guard=guard,
        upstream_pin_record_sha256=UPSTREAM_PINS_SHA,runner_sha256=LOADED_SHA,
        fresh_budget=args.batch,authenticate_only=args.authenticate_only,
        source=str(SOURCE),state=str(STATE),no_automatic_next_batch=True))
    try:
        base=load('build_mathlib_serial',PREVIOUS/'build_mathlib_serial.py')
        audit=load('astra_full_owned_audit',PREVIOUS/'build_lean.py')
        serial=load('astra_full_owned_serial',SUPPORT/'serial_compile.py')
        namespace=load('astra_full_owned_namespace',NAMESPACE)
        external_helper=load('astra_full_owned_external',EXTERNAL_HELPER)
        check_pause()
        plan_source,modules=authenticate_sources()
        check_pause()
        repos,package_pins,env=base.setup(MATHLIB,LEAN_BIN)
        check_pause()
        external=external_helper.authenticate_complete(EXTERNAL,repos,LEAN_BIN,package_pins)
        external_plan=read(namespace.EXTERNAL_PLAN)
        external_sources={r['module']:r for r in external_plan['modules']}
        external_rows={r['module']:r for r in external['modules']}
        external_index={r['module']:i for i,r in enumerate(external_plan['modules'])}
        if set(external_rows)!=set(external_sources) or len(external_rows)!=3661:
            raise ValueError('full external authenticated scope differs')
        helpers=dict(base=base,audit=audit,serial=serial,namespace=namespace,env=env,
                     build=STATE/'.lake/build/lib/lean')
        check_pause()
        narrow,narrow_context=authenticate_narrow(evidence,helpers,package_pins)
        shaped=[dict(r,sha256=r['source_sha256']) for r in modules]
        check_pause()
        env,ns=namespace.bind_routes(shaped,SOURCE,helpers['build'],repos,env,external_rows,external_sources,LEAN_BIN)
        helpers.update(env=env,namespace_binding=ns,namespace_sha=namespace.binding_digest(ns))
        base_inputs=serial.toolchain_inputs(LEAN_BIN)
        for r in external_rows.values():base_inputs.update(r['artifacts'])
        helpers['base_inputs']=base_inputs
        full_plan=dict(schema='astra_full_owned_execution_plan_v1',source_plan_sha256=OWNED_PLAN_SHA,
            selection_sha256=digest(SELECTION),modules=modules,runner_sha256=LOADED_SHA,
            upstream_pin_record_sha256=UPSTREAM_PINS_SHA,external_authentication=external,
            narrow_plan_sha256=digest(NARROW_STATE/'PLAN.json'),narrow_namespace_sha256=digest(NARROW_STATE/'NAMESPACE-RESOLUTION.json'),
            narrow_receipt_pins={name:r['receipt_sha256'] for name,r in narrow.items()},
            namespace_sha256=helpers['namespace_sha'],namespace_resolution=ns,
            compiler_sha256=base.LEAN_SHA,mathlib_pin=base.PIN,package_pins=package_pins,
            serial_helper_sha256=digest(SUPPORT/'serial_compile.py'))
        check_pause()
        if args.resume:
            if read(STATE/'PLAN.json')!=full_plan or read(STATE/'NAMESPACE-RESOLUTION.json')!=ns:
                raise ValueError('resume plan or namespace changed')
        else:
            STATE.mkdir(parents=True,exist_ok=False)
            write_new(STATE/'PLAN.json',full_plan);write_new(STATE/'NAMESPACE-RESOLUTION.json',ns)
        plan_sha=digest(STATE/'PLAN.json')
        write_new(evidence/'AUTHENTICATED-CONTEXT.json',dict(external=external,narrow=narrow_context,
            source_plan_sha256=OWNED_PLAN_SHA,execution_plan_sha256=plan_sha,
            namespace_sha256=helpers['namespace_sha']))
        check_pause()
        completed,allowed=authenticate_prefix(modules,helpers,external_rows,external_sources,external_index,narrow,plan_sha)
        if args.resume and prefix_token(plan_sha,helpers['namespace_sha'],completed)!=args.resume_token:
            raise ValueError('owned receipt prefix changed since the owner-verified checkpoint')
        resumed=len(completed);fresh=cloned=0;owned_names={r['module'] for r in modules}
        input_files=base_inputs|{p for r in completed.values() for p in r['receipt']['artifacts']}
        for i in range(resumed,len(modules)):
            if args.authenticate_only or fresh>=args.batch:break
            check_pause()
            row=modules[i];name=row['module'];source=SOURCE/relative(name);target=helpers['build']/relative(name).with_suffix('.olean')
            if digest(source)!=row['source_sha256']:raise ValueError('source changed before module action')
            imports=import_bindings(row,helpers,external_rows,external_sources,completed,owned_names)
            origin=expected_origin(name,row,external_rows,external_index,narrow)
            check_pause()
            saved=STATE/'source'/relative(name);preserve(source,saved)
            record=receipt_common(i,row,helpers,plan_sha,imports)
            record['attempt']=dict(path=str(evidence/'ATTEMPT.json'),sha256=digest(evidence/'ATTEMPT.json'))
            if origin is not None:
                snapshots=[preserve(path,STATE/'origins'/f'{i:04d}'/f'{number:02d}-{path.name}')
                           for number,path in enumerate(origin_snapshot_paths(origin))]
                copied=remap_artifacts(origin['artifacts'],target)
                for old,sha in origin['artifacts'].items():
                    suffix=next(x for x in sorted(SUFFIXES,key=len,reverse=True) if old.endswith(x))
                    if digest(old)!=sha:raise ValueError('reuse artifact changed before copy')
                    preserve(old,target.with_suffix(suffix))
                authenticate_artifacts(helpers,copied,target)
                record.update(execution='AUTHENTICATED_REUSE',origin=origin,origin_snapshots=snapshots,
                              exit_code=0,artifacts=copied,axioms={})
                cloned+=1
            else:
                target.parent.mkdir(parents=True,exist_ok=True)
                command=compile_command(name,target);out=STATE/f'{i:04d}.stdout';err=STATE/f'{i:04d}.stderr'
                started=time.monotonic()
                code,control=serial.compile_one(command,cwd=SOURCE,env=env,stdout=out,stderr=err,
                    input_files=input_files,target=target,index=i,module=name)
                record.update(execution='FRESH_SOURCE_COMPILE',command=command,exit_code=code,
                    compiler_exit_code=code,seconds=time.monotonic()-started,resource_control=control,
                    artifacts=base.artifacts(target),stdout_sha256=digest(out),stderr_sha256=digest(err))
                if code==0:
                    try:
                        record['axioms']=audit_logs(helpers,out,err)
                        authenticate_artifacts(helpers,record['artifacts'],target)
                    except ValueError as exc:record.update(exit_code=2,audit_failure=str(exc))
                fresh+=1
            receipt=STATE/f'{i:04d}.json';write_new(receipt,record)
            print(json.dumps(dict(module=name,index=i,execution=record['execution'],exit_code=record['exit_code'],
                                  receipt_sha256=digest(receipt))),flush=True)
            if record['exit_code']!=0:raise ValueError('failed component preserved; no automatic repair or next batch')
            completed[name]=dict(receipt=record,receipt_sha256=digest(receipt));input_files.update(record['artifacts'])
            base.release_own_file_cache(repos+[STATE],LEAN_BIN)
        # Recheck the complete current prefix, including saved sources, origin
        # snapshots and all unreceipted files, before issuing any batch result.
        check_pause()
        checked,_=authenticate_prefix(modules,helpers,external_rows,external_sources,external_index,narrow,plan_sha)
        complete=len(checked)==len(modules)
        check_pause()
        if complete and not args.authenticate_only and not (STATE/'COMPONENTS-COMPLETE.json').exists():
            write_new(STATE/'COMPONENTS-COMPLETE.json',component_result(modules,checked,helpers,plan_sha))
        summary=dict(status='AUTHENTICATED_COMPONENT_BATCH_ONLY',fresh_invocations=fresh,
            new_authenticated_clones=cloned,resumed_receipts=resumed,contiguous_receipts=len(checked),
            selected_modules=len(modules),component_complete=complete,plan_sha256=plan_sha,
            resume_token=prefix_token(plan_sha,helpers['namespace_sha'],checked),
            no_automatic_next_batch=True,actual_final_lake_run=False,full_type_axiom_audit=False,
            final_guard_receipt='SEPARATE_PENDING',physical_representative=False)
        write_new(evidence/'SUMMARY.json',summary);print(json.dumps(summary),flush=True)
        if args.authenticate_only and not complete:raise ValueError('full component state incomplete; no completion asserted')
    except BaseException as exc:
        write_new(evidence/'FAILURE.json',dict(status='FAILED_OR_UNVERIFIED_PRESERVE_ALL_BYTES',
            exception_type=type(exc).__name__,message=str(exc),runner_sha256=LOADED_SHA,
            no_cleanup=True,no_success_inferred=True,final_guard_receipt='SEPARATE_PENDING'))
        raise


if __name__=='__main__':
    main()
