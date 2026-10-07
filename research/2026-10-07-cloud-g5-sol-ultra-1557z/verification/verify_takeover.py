#!/usr/bin/env python3
"""Root takeover: bounded, serial, frozen timed G5/G2 and G6 closure audit.

Contributor: internal Lean lane, CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
Derivative of the stopped G5 worker's published selection/verification route,
the successful G6 serial runner, and dot's attributed complete AuditTemplate.
Original G5 verification recipe and all source providers remain unchanged.
"""
import base64
import datetime
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

repo, build, evidence = map(lambda p: Path(p).resolve(), sys.argv[1:4])
build.mkdir(parents=True, exist_ok=True)
evidence.mkdir(parents=True, exist_ok=True)
packet = repo / 'research/2026-10-07-cloud-g5-sol-ultra-1557z'
baseline = repo / 'research/2026-10-04-dot-verified-lean-825-0203z/package/baseline'
started = time.monotonic()
records = []
pin = '0df444a360eaa60ab8c11dca51a86af692955474'
expected_lean = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

def run(label, argv, timeout=180, fatal=True):
    command = {'label': label, 'argv': argv, 'cwd': str(build), 'start': utc(),
               'timeout_seconds': min(timeout, 180)}
    print('G5_TAKEOVER_COMMAND ' + json.dumps(command), flush=True)
    try:
        result = subprocess.run(argv, cwd=build, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=min(timeout, 180))
        output, code = result.stdout, result.returncode
    except subprocess.TimeoutExpired as exc:
        output, code = exc.stdout or b'', 124
    log = evidence / (label + '.log')
    log.write_bytes(output)
    print(output.decode(errors='replace'), end='', flush=True)
    receipt = {**command, 'end': utc(), 'exit': code, 'output_sha256': digest(log)}
    records.append(receipt)
    (evidence / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
    print('G5_TAKEOVER_RECEIPT ' + json.dumps(receipt), flush=True)
    if code and fatal:
        raise SystemExit(code)
    return code

def emit_file(label, path):
    # Lossless authenticated payload recovery from ordinary workflow logs,
    # needed because this cloud workspace cannot fetch signed artifact URLs.
    data = path.read_bytes()
    encoded = base64.b64encode(gzip.compress(data, mtime=0)).decode()
    print(label + '_PAYLOAD ' + json.dumps({'file': path.name, 'bytes': len(data),
          'sha256': hashlib.sha256(data).hexdigest(), 'encoding': 'gzip+base64'}), flush=True)
    print(label + '_GZIP_BASE64_BEGIN', flush=True)
    for i in range(0, len(encoded), 4096):
        print(encoded[i:i + 4096], flush=True)
    print(label + '_GZIP_BASE64_END', flush=True)

run('reconstruct', [sys.executable, str(packet / 'scripts/reconstruct_context.py'),
                    str(repo), str(build)])
manifest = json.loads((build / 'SOURCE-CONTEXT.json').read_text())
assert manifest['mathlib_commit'] == pin
assert len(manifest['modules']) == 164
g6_packet = repo / 'research/2026-10-07-cloud-g6-sol-ultra-1601z'
g6_targets = ['UnifiedLean.G6.' + suffix for suffix in
              ['FiniteProbability', 'Conditioning', 'SourcePrefix', 'ProgramPrefix', 'TaylorCertificate']]
targets = ['G5HiddenRegisterTimedProjectivity', 'G5FrozenTriplePolynomialKernel',
           'G5FrozenTripleAnalyticSupport', 'G2ActualTimedAllPanelLaw',
           'G3ApproximateMomentBarrier', *g6_targets]
overlay = [('G3ApproximateMomentBarrier',
            repo / 'research/2026-10-07-cloud-g3-1619z/G3ApproximateMomentBarrier.lean',
            Path('CloudG5/G3ApproximateMomentBarrier.lean'))]
overlay += [(module, g6_packet / 'sources' / (module.replace('.', '/') + '.lean'),
             Path(module.replace('.', '/') + '.lean')) for module in g6_targets]
for module, source, destination in overlay:
    dependencies = []
    for line in source.read_text().splitlines():
        match = re.match(r'\s*(?:public\s+)?import\s+(.+)', line)
        if match:
            dependencies.extend(match[1].split('--')[0].split())
    assert all(d in manifest['modules'] or d.startswith(('Mathlib.', 'Lean.', 'Std.', 'Init'))
               for d in dependencies), (module, dependencies)
    manifest['external_roots'] += [d for d in dependencies if d.startswith('Mathlib.')]
    (build / destination).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, build / destination)
    manifest['modules'][module] = {'source': str(source.relative_to(repo)),
        'sha256': digest(source), 'authority': 'owned G6/G3 successful selected source overlay',
        'imports': dependencies, 'destination': str(destination)}
    manifest['order'].append(module)
manifest['external_roots'] = sorted(set(manifest['external_roots']))
manifest['requested_targets'] = targets
manifest['scope'] = 'Selected timed G5/G2 closure plus exact G6/G3 overlay; not full corpus.'
assert len(manifest['modules']) == 170

lakefile = (baseline / 'lakefile.lean').read_text()
lakefile += ('\nlean_lib CloudG5 where\n  srcDir := "CloudG5"\n'
             '  roots := #[`G5HiddenRegisterTimedProjectivity, `G5FrozenTriplePolynomialKernel, '
             '`G5FrozenTripleAnalyticSupport, `G3ApproximateMomentBarrier]\n'
             'lean_lib TimedG2 where\n  srcDir := "TimedG2"\n'
             '  roots := #[`G2ActualTimedAllPanelLaw]\n')
(build / 'lakefile.lean').write_text(lakefile)
(build / 'lean-toolchain').write_text(manifest['toolchain'] + '\n')
shutil.copyfile(build / 'lakefile.lean', evidence / 'lakefile.lean')
mathlib = build / 'deps/mathlib'
mathlib.mkdir(parents=True, exist_ok=True)
run('mathlib-init', ['git', '-C', str(mathlib), 'init', '--quiet'])
run('mathlib-remote', ['git', '-C', str(mathlib), 'remote', 'add', 'origin',
                       'https://github.com/leanprover-community/mathlib4.git'])
run('mathlib-shallow-fetch', ['git', '-C', str(mathlib), 'fetch', '--quiet',
                            '--no-tags', '--depth=1', 'origin', pin])
run('mathlib-checkout', ['git', '-C', str(mathlib), 'checkout', '--quiet',
                        '--detach', 'FETCH_HEAD'])
assert subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip() == pin
os.environ['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
run('lake-update', ['lake', 'update'])
executable = Path(shutil.which('lean')).resolve()
assert digest(executable) == expected_lean
manifest['dependencies'] = {
    'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
    'lean_executable_sha256': digest(executable), 'mathlib_commit': pin,
    'lake_manifest_sha256': digest(build / 'lake-manifest.json'),
    'baseline_lake_registration_sha256': digest(baseline / 'lakefile.lean'),
    'additive_lake_registration_sha256': digest(build / 'lakefile.lean'),
    'verification_script_sha256': digest(Path(__file__)),
    'source_selection_script_sha256': digest(packet / 'scripts/reconstruct_context.py'),
}
(build / 'SOURCE-CONTEXT.json').write_text(json.dumps(manifest, indent=2) + '\n')
shutil.copyfile(build / 'SOURCE-CONTEXT.json', evidence / 'SOURCE-CONTEXT.json')
shutil.copyfile(build / 'lake-manifest.json', evidence / 'lake-manifest.json')
emit_file('G5_TAKEOVER_INPUTS', evidence / 'SOURCE-CONTEXT.json')
run('mathlib-cache', ['lake', 'exe', 'cache', 'get',
                    *[d for d in manifest['external_roots'] if d.startswith('Mathlib.')]])

early = ['G5FrozenTriplePolynomialKernel', 'G5ExponentialGermIdentification',
         'G5UnknownRateSupport', 'G5FrozenTripleAnalyticSupport']
order = early + [module for module in manifest['order'] if module not in early]
statuses = {}
for module in order:
    rec = manifest['modules'][module]
    custom_dependencies = [d for d in rec['imports'] if d in manifest['modules']]
    if time.monotonic() - started > 740:
        statuses[module] = {'status': 'NOT_RUN_JOB_BUDGET'}
    elif any(statuses.get(d, {}).get('status') != 'PASS' for d in custom_dependencies):
        statuses[module] = {'status': 'BLOCKED_DEPENDENCY', 'dependencies': custom_dependencies}
    else:
        source = build / rec['destination']
        assert digest(source) == rec['sha256']
        target = build / '.lake/build/lib/lean' / Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        root = build if module.startswith('UnifiedLean.') else build / Path(rec['destination']).parts[0]
        code = run(module, ['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096',
                           '-R', str(root), '-o', str(target), str(source)], fatal=False)
        assert digest(source) == rec['sha256']
        statuses[module] = {'status': 'PASS' if code == 0 else 'FAIL', 'exit': code,
                            'source_sha256': rec['sha256']}
        if code == 0:
            statuses[module]['artifact_sha256'] = digest(target)
    (evidence / 'module-results.json').write_text(json.dumps(statuses, indent=2) + '\n')
emit_file('G5_TAKEOVER_MODULE_RESULTS', evidence / 'module-results.json')

passed = [module for module in order if statuses[module]['status'] == 'PASS']
template = (repo / 'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').read_text()
template = template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]',
    '#[' + ', '.join(json.dumps(module) for module in passed) + ']')
audit = '\n'.join('import ' + module for module in passed) + '\n' + template
(build / 'TakeoverCompleteAudit.lean').write_text(audit)
shutil.copyfile(build / 'TakeoverCompleteAudit.lean', evidence / 'TakeoverCompleteAudit.lean')
audit_timeout = min(180, max(1, int(825 - (time.monotonic() - started))))
audit_exit = run('complete-custom-environment-audit', ['lake', 'env', 'lean', '--trust=0',
                '-j1', '-M4096', str(build / 'TakeoverCompleteAudit.lean')],
                timeout=audit_timeout, fatal=False)
audit_pass = False
if (build / 'AUDIT-OWNED.json').is_file():
    shutil.copyfile(build / 'AUDIT-OWNED.json', evidence / 'AUDIT-OWNED.json')
    report = json.loads((evidence / 'AUDIT-OWNED.json').read_text())
    audit_pass = (audit_exit == 0 and not report['owned_axioms'] and
                  not report['nonstandard_axiom_rows'] and not report['missing_modules'] and
                  set(report['selected_modules']) == set(passed) and
                  {row['module'] for row in report['declarations']} <= set(passed))
    emit_file('G5_TAKEOVER_COMPLETE_AUDIT', evidence / 'AUDIT-OWNED.json')
receipt = {'source_commit': manifest['source_commit'], 'mathlib_commit': pin,
    'scope': manifest['scope'], 'modules': statuses, 'audit_exit': audit_exit,
    'complete_passed_environment_audit': audit_pass,
    'audit_source_sha256': digest(evidence / 'TakeoverCompleteAudit.lean'),
    'requested_targets': targets, 'end': utc(), 'elapsed_seconds': time.monotonic() - started}
(evidence / 'BUILD-RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
emit_file('G5_TAKEOVER_BUILD_RECEIPT', evidence / 'BUILD-RECEIPT.json')
if audit_pass:
    for module in targets:
        if statuses[module]['status'] == 'PASS':
            print('G5_TAKEOVER_TARGET_COMPLETE_AUDIT_PASS ' + module, flush=True)
all_pass = audit_pass and all(statuses[module]['status'] == 'PASS' for module in order)
print('G5_TAKEOVER_ALL_SELECTED_PASS ' + str(all_pass), flush=True)
sys.exit(0 if all_pass else 1)
