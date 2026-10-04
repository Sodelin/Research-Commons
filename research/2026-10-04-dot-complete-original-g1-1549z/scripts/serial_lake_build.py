#!/usr/bin/env python3
"""Serial official Lake source targets, with hash-checked resume and resource pauses.
The initial workspace must contain no preinstalled proof objects. A resume may
reuse only objects freshly compiled here and bound by a prior local receipt.
Official pinned dependency caches may be used. The final default Lake check
is a distinct operation after every source target has passed.
"""
from pathlib import Path
import hashlib, json, os, re, subprocess, time, datetime, sys, shutil
root = Path(__file__).resolve().parent.parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(name, data):
    p = root / name
    tmp = p.with_name(p.name + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    tmp.replace(p)
reg = json.loads((root / 'SOURCE-REGISTRY.json').read_text())
rows = {r['module']: r for r in reg['records']}
order, done, visiting = [], set(), set()
def visit(m):
    if m in done: return
    assert m not in visiting, ('cycle', m)
    visiting.add(m)
    r = rows[m]; source = root / r['path']; data = source.read_bytes()
    assert hashlib.sha256(data).hexdigest() == r['sha256'], m
    for line in data.decode().splitlines():
        match = re.match(r'^\s*(?:(?:public|meta)\s+)*import\s+(.+)', line)
        if match:
            for dep in match.group(1).split('--', 1)[0].split():
                if dep in rows: visit(dep)
    visiting.remove(m); done.add(m); order.append(m)
for m in sorted(rows): visit(m)
assert len(order) == 467
(root / '.lake/build').mkdir(parents=True, exist_ok=True)
logs = root / 'serial-build-logs'; logs.mkdir(exist_ok=True)
config_sha = '0471edbcd58ec5d6ec4eb00f1760052f6da712c132832e1615b644b1534f52cc'
assert sha(root / 'lakefile.lean') == config_sha
object_path = lambda m: root / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')
receipts = []
pause = Path(os.environ['G1_LOCAL_RESUME_RECEIPT']) if 'G1_LOCAL_RESUME_RECEIPT' in os.environ else root / '.g1-local-resume-receipt.json'
if pause.exists():
    prior = json.loads(pause.read_text())
    assert prior.get('configuration_sha256', prior.get('restored_config_sha256')) == config_sha
    for i, r in enumerate(prior['records']):
        m = r['module']; assert m == order[i] and r['exit_code'] == 0
        assert sha(root / rows[m]['path']) == r['source_sha256'] == rows[m]['sha256']
        assert sha(root / r['log']) == r['log_sha256']
        assert sha(object_path(m)) == r['new_layout_object_sha256']
        assert object_path(m).stat().st_size == r['new_layout_object_bytes']
        receipts.append(dict(r, validated_local_fresh_resume=True))
    assert len(receipts) == prior.get('passed_fresh_targets', prior.get('passed_fresh_source_targets'))
    print(f'Validated {len(receipts)} local fresh source/log/object receipts; no replay.', flush=True)
resumed_count = len(receipts)
env = os.environ.copy(); env.pop('LEAN_PATH', None); env['LEAN_NUM_THREADS'] = '1'
start = time.monotonic()
def resources():
    mem = dict((line.split(':', 1)[0], int(line.split()[1]) * 1024)
               for line in Path('/proc/meminfo').read_text().splitlines()
               if line.startswith('MemAvailable:'))
    return {'workspace_free_bytes': shutil.disk_usage(root).free,
            'output_volume_free_bytes': shutil.disk_usage(root / '.lake/build').free,
            'memory_available_bytes': mem['MemAvailable']}
def gate(next_target):
    usage = resources()
    reasons = []
    if (root / 'PAUSE-BUILD').exists(): reasons.append('explicit_between_target_pause')
    if usage['workspace_free_bytes'] < 256 * 1024**2: reasons.append('workspace_below_256MiB')
    if usage['output_volume_free_bytes'] < 512 * 1024**2: reasons.append('output_volume_below_512MiB')
    if usage['memory_available_bytes'] < 5 * 1024**3: reasons.append('memory_below_5GiB')
    if reasons:
        write('RESUMED-RESOURCE-PAUSE.json', {'schema': 'original-G1-local-source-resume-v1',
              'status': 'PAUSED_BETWEEN_SOURCE_TARGETS',
              'configuration_sha256': config_sha,
              'utc': now(), 'reasons': reasons, 'resources': usage,
              'passed_fresh_targets': len(receipts), 'next_target': next_target,
              'next_target_not_started': True, 'records': receipts})
        print(f'Resource pause before {next_target}: {reasons} {usage}', flush=True)
        sys.exit(75)
def progress():
    write('RESUMED-SERIAL-PROGRESS.json', {'completed_targets': len(receipts),
          'total_targets': 467, 'validated_local_resume_targets': resumed_count,
          'elapsed_seconds_this_run': time.monotonic() - start, 'records': receipts})
for i, m in enumerate(order):
    if i < resumed_count: continue
    gate(m)
    assert sha(root / 'lakefile.lean') == config_sha
    cmd = ['lake', 'build', '+' + m + ':olean']
    p = logs / (m.replace('.', '_') + '.log'); ts = time.monotonic()
    with p.open('w') as out:
        run = subprocess.run(cmd, cwd=root, env=env, stdout=out,
                             stderr=subprocess.STDOUT, timeout=600)
    r = {'module': m, 'command': cmd, 'exit_code': run.returncode,
         'elapsed_seconds': time.monotonic() - ts, 'log': str(p.relative_to(root)),
         'log_sha256': sha(p), 'source_sha256': rows[m]['sha256'],
         'config_sha256': config_sha, 'freshly_compiled_in_this_workspace': True}
    if run.returncode == 0:
        r.update(new_layout_object_sha256=sha(object_path(m)),
                 new_layout_object_bytes=object_path(m).stat().st_size)
        receipts.append(r); progress()
    else:
        write('RESUMED-FAILED-TARGET.json', dict(r, utc=now(), passed_targets=len(receipts)))
    print(f'{i+1}/467 {m} exit={run.returncode} elapsed={r["elapsed_seconds"]:.2f}s', flush=True)
    if run.returncode:
        print(p.read_text()[-15000:], flush=True); sys.exit(run.returncode)
# Validate all original sources and all newly built objects before the separate check.
for r in receipts:
    assert sha(root / rows[r['module']]['path']) == r['source_sha256']
    assert sha(object_path(r['module'])) == r['new_layout_object_sha256']
gate('final-default-Lake-check')
cmd = ['lake', 'build']; final_log = root / 'FINAL-DEFAULT-LAKE.log'; ts = time.monotonic()
with final_log.open('w') as out:
    run = subprocess.run(cmd, cwd=root, env=env, stdout=out, stderr=subprocess.STDOUT, timeout=600)
print(final_log.read_text()[-15000:], flush=True)
status = {'status': 'PASS_FRESH_COMPLETE467_SOURCE_SERIAL_LAKE_AND_DEFAULT_TARGET'
          if run.returncode == 0 else 'FAIL_FINAL_DEFAULT_TARGET',
          'exit_code': run.returncode, 'utc': now(), 'fresh_proof_source_targets': 467,
          'validated_local_fresh_resume_targets': resumed_count,
          'new_targets_this_run': 467 - resumed_count,
          'inherited_proof_objects_installed': False, 'official_dependency_cache_reuse': True,
          'source_modules_unchanged': True, 'config_sha256': config_sha,
          'workflow': 'serial official Lake source targets, hash-checked local resume, then separate default Lake check',
          'default_check': {'command': cmd, 'exit_code': run.returncode,
                            'elapsed_seconds': time.monotonic() - ts,
                            'log_sha256': sha(final_log)},
          'elapsed_seconds_this_run': time.monotonic() - start, 'records': receipts}
write('SERIAL-BUILD-RECEIPT.json', status)
sys.exit(run.returncode)
