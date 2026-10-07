#!/usr/bin/env python3
"""Bounded serial verification of a frozen Cloud G5 source context.

Ordinary custom-source compilation plus actual complete declaration/axiom
inventory. Official Mathlib cache reuse is not a fresh Mathlib rebuild.
"""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

repo, build, evidence = map(lambda s: Path(s).resolve(), sys.argv[1:4])
build.mkdir(parents=True, exist_ok=True)
evidence.mkdir(parents=True, exist_ok=True)
packet = repo / 'research/2026-10-07-cloud-g5-sol-ultra-1557z'
started = time.time()
records = []

def digest(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()

def run(name, cmd, timeout=180):
    start = time.time()
    with (evidence / (name + '.log')).open('w') as log:
        try:
            process = subprocess.run(cmd, cwd=build, stdout=log, stderr=subprocess.STDOUT,
                                     timeout=timeout)
            code = process.returncode
        except subprocess.TimeoutExpired:
            code = 124
    rec = {'name': name, 'command': cmd, 'start_unix': start, 'end_unix': time.time(),
           'exit': code, 'log_sha256': digest(evidence / (name + '.log'))}
    records.append(rec)
    (evidence / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
    print(json.dumps(rec), flush=True)
    return code

assert run('reconstruct', [sys.executable, str(packet / 'scripts/reconstruct_context.py'),
                           str(repo), str(build)]) == 0
manifest = json.loads((build / 'SOURCE-CONTEXT.json').read_text())
shutil.copyfile(build / 'SOURCE-CONTEXT.json', evidence / 'SOURCE-CONTEXT.json')
baseline = repo / 'research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/lakefile.lean'
lakefile = baseline.read_text().replace('require mathlib from "deps/mathlib"',
    'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ '
    '"0df444a360eaa60ab8c11dca51a86af692955474"')
lakefile += '\nlean_lib CloudG5 where\n  srcDir := "CloudG5"\n' + \
    '  roots := #[`G5HiddenRegisterTimedProjectivity, `G5FrozenTriplePolynomialKernel, `G5FrozenTripleAnalyticSupport]\n' + \
    'lean_lib TimedG2 where\n  srcDir := "TimedG2"\n  roots := #[`G2ActualTimedAllPanelLaw]\n'
(build / 'lakefile.lean').write_text(lakefile)
(build / 'lean-toolchain').write_text(manifest['toolchain'] + '\n')
shutil.copyfile(build / 'lakefile.lean', evidence / 'lakefile.lean')
os.environ['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
assert run('lake-update', ['lake', 'update']) == 0
pin = subprocess.check_output(['git', '-C', str(build / '.lake/packages/mathlib'),
                               'rev-parse', 'HEAD'], text=True).strip()
assert pin == manifest['mathlib_commit'], pin
shutil.copyfile(build / 'lake-manifest.json', evidence / 'lake-manifest.json')
assert run('mathlib-cache', ['lake', 'exe', 'cache', 'get',
    *[x for x in manifest['external_roots'] if x.startswith('Mathlib.')]], timeout=240) == 0

# Compile the small independent analytic branch first, then the G2 context.
order = manifest['order']
early = ['G5FrozenTriplePolynomialKernel', 'G5ExponentialGermIdentification',
         'G5UnknownRateSupport', 'G5FrozenTripleAnalyticSupport']
order = early + [n for n in order if n not in early]
statuses = {}
artifact_dir = build / '.lake/build/lib/lean'
artifact_dir.mkdir(parents=True, exist_ok=True)
for name in order:
    if time.time() - started > 740:
        statuses[name] = {'status': 'NOT_RUN_JOB_BUDGET'}
        continue
    rec = manifest['modules'][name]
    deps = [d for d in rec['imports'] if d in manifest['modules']]
    if any(statuses.get(d, {}).get('status') != 'PASS' for d in deps):
        statuses[name] = {'status': 'BLOCKED_DEPENDENCY', 'dependencies': deps}
        continue
    source = build / rec['destination']
    assert digest(source) == rec['sha256']
    target = artifact_dir / Path(*name.split('.')).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    root = build if name.startswith('UnifiedLean.') else build / Path(rec['destination']).parts[0]
    code = run(name, ['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096',
        '-R', str(root), '-o', str(target), '-i', str(target.with_suffix('.ilean')), str(source)])
    assert digest(source) == rec['sha256']
    statuses[name] = {'status': 'PASS' if code == 0 else 'FAIL', 'exit': code,
                       'source_sha256': rec['sha256']}
    if code == 0:
        statuses[name]['artifact_sha256'] = digest(target)
    (evidence / 'module-results.json').write_text(json.dumps(statuses, indent=2) + '\n')

# Actual environment inventory, including generated declarations and each
# declaration's type/body references and transitive axiom set. Attribution:
# derivative of dot's connected-workspace AuditTemplate.lean.
passed = [n for n in order if statuses[n]['status'] == 'PASS']
template = (repo / 'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').read_text()
template = template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]',
    '#[' + ', '.join(json.dumps(n) for n in passed) + ']')
audit = '\n'.join('import ' + n for n in passed) + '\n' + template
(build / 'CloudG5Audit.lean').write_text(audit)
shutil.copyfile(build / 'CloudG5Audit.lean', evidence / 'CloudG5Audit.lean')
audit_exit = run('complete-custom-audit', ['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096',
                                        'CloudG5Audit.lean'])
if (build / 'AUDIT-OWNED.json').is_file():
    shutil.copyfile(build / 'AUDIT-OWNED.json', evidence / 'AUDIT-OWNED.json')
receipt = {'source_commit': manifest['source_commit'], 'mathlib_commit': pin,
           'scope': 'Fresh selected custom-source ordinary checks; official Mathlib cache reuse. '
                    'Complete selected-declaration axiom/reference inventory; no independent semantic acceptance.',
           'modules': statuses, 'audit_exit': audit_exit, 'start_unix': started, 'end_unix': time.time()}
(evidence / 'BUILD-RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
all_pass = all(statuses[n]['status'] == 'PASS' for n in order) and audit_exit == 0
print('CLOUD_G5_ALL_SELECTED_PASS', all_pass, flush=True)
sys.exit(0 if all_pass else 1)
