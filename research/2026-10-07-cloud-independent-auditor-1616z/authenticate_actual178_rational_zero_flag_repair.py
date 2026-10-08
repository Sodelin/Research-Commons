"""Static exact-diff/API/selection check; no Lean, source evaluation or Actions calls."""
from pathlib import Path
import difflib, hashlib, json, re, subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
AUTHOR = '3fb8ad532e2f9f3d22f9c6dc22571000d0807366'
FROZEN = '00863f04f69c8c97857d97c5ca63f1511019e366'
G6 = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/'
PREP = G6 + 'verification/preparation/rational-zero-flag-actual178-repair-0617z/'
PLAN = G6 + 'verification/freeze-plans/rational-zero-flag-actual178-repair-static.json'
OLDPLAN = G6 + 'verification/freeze-plans/two-followon-actual177-repair-static.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
def read(c, p):
    return subprocess.check_output(['git', 'show', c + ':' + p], cwd=ROOT)
def identity(c, p):
    b = read(c, p)
    return {'path': p, 'bytes': len(b), 'sha256': sha(b),
            'git_blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()}

pins = json.loads(read(AUTHOR, PREP + 'SOURCE-PINS.json'))
old = read(FROZEN, pins['formal_path'])
new = read(AUTHOR, pins['candidate_path'])
needle = b'simp only [rationalResidualCount, hk, hz, if_true, if_false,'
assert old.count(needle) == 1
assert old.replace(needle, needle + b' Nat.zero_le,') == new
assert sha(old) == pins['old_sha256'] == '35e3b2ef67a82c6c637b0d814fa2b217302765bb3904db3b1cca8fdb0bceb820'
assert sha(new) == pins['candidate_sha256'] == 'd9f49ca8cacdb40ec20a185db60db17e768d38d2c8632fcf2842ae682e995d3a'
assert len(new) == pins['candidate_bytes'] == 7170
diff = read(AUTHOR, pins['diff_path'])
assert sha(diff) == pins['diff_sha256'] == '357ebd8552c12eb7f9b75ed1ad4b972e82cb288d634f185f5f050fcfc3183a41'
changes = [l for l in diff.decode().splitlines() if l.startswith(('+', '-')) and not l.startswith(('+++', '---'))]
assert len(changes) == 2 and changes[1][1:] == changes[0][1:] + ' Nat.zero_le,'
headers = lambda b: re.findall(rb'^(?:noncomputable\s+)?(?:def|lemma|theorem)\s+[^\n]*', b, re.M)
assert headers(old) == headers(new)
sum_body = lambda b: b.split(b'lemma rationalResidualCount_sum', 1)[1].split(b'lemma rationalDenominator_real', 1)[0]
assert sum_body(old) == sum_body(new)

api = Path(pins['pinned_api']['local_runtime_source']).read_bytes()
assert sha(api) == pins['pinned_api']['source_sha256'] == '56de5780adc4358372fa9cfac270a70f2d03fd4f213a373aea4365483b31a544'
assert pins['pinned_api']['declaration'] in api.decode()
failed = (BASE / 'three-followon-repair-37734981680-RationalResidualCertificate-failed.log').read_bytes()
assert failed.count(b'if 0 \xe2\x89\xa4 K') == 4 and b':115:67: error: unsolved goals' in failed

plan_bytes = read(AUTHOR, PLAN)
assert sha(plan_bytes) == pins['static_plan_sha256'] == '5de11dd729ef2f6190daf8c5153b8fb9b741a691d706e4525377958dfce83521'
plan = json.loads(plan_bytes)
previous = json.loads(read(FROZEN, OLDPLAN))
actual = json.loads((BASE / 'three-followon-repair-37734981680-independent.json').read_text())
actual_inputs = json.loads(read('6529c3b8346c7ecfd48c4b9e2a9dfd17002d87d3', G6 + 'verification/evidence/g6-run-37734981680-FAILED/inputs-recovered.json'))
assert plan['custom_modules'] == 179 and plan['named_total'] == 501
assert plan['namespace_counts'] == {'G6': 352, 'G3': 134, 'G5': 15}
assert plan['targets'] == previous['targets'] == actual_inputs['targets'] and len(plan['targets']) == 45
assert plan['topological_order'] == previous['topological_order'] == actual_inputs['topological_order']
for key in ['named_counts', 'mathlib_roots', 'lean_roots', 'external_context_sha256', 'external_root_addition']:
    assert plan[key] == previous[key], key
assert len(plan['mathlib_roots']) == 68 and len(plan['lean_roots']) == 1
assert set(plan['modules']) == set(previous['modules']) == set(actual_inputs['modules'])
module = pins['module']
fixed = []
for name, rec in plan['modules'].items():
    if name == module:
        for key in set(rec) | set(previous['modules'][name]):
            if key != 'sha256': assert rec[key] == previous['modules'][name][key], key
        assert rec['sha256'] == sha(new)
    else:
        assert rec == previous['modules'][name], name
        assert rec['sha256'] == actual_inputs['modules'][name]['sha256'], name
        fixed.append(name)
assert len(fixed) == 178 and set(fixed) == set(actual['successful_module_names'])
assert plan['unchanged_accepted_custom_modules'] == 178 and not plan['new_modules']
assert plan['repair_modules'] == [module]
budget = plan['runtime_budget']
assert budget['planning_total_seconds'] == sum(budget[k] for k in ['actual179_job_seconds', 'one_repaired_module_reserve_seconds', 'audit_reserve_seconds', 'runtime_cache_variation_margin_seconds']) == 775
assert budget['job_cap_seconds'] == 900 and budget['per_command_cap_seconds'] == 180
assert budget['flags'] == ['--trust=0', '-j1', '-M4096']
for path in ['.github/workflows/g6-cloud-lean.yml', G6 + 'verification/complete_environment.py', 'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean']:
    assert read(FROZEN, path) == read(AUTHOR, path), path
canonical = plan['prior_independent_acceptance']
assert canonical['commit'] == '6f54d891a88d3410bf0b93796f7ce76fcc77a9e6'
assert sha(read(canonical['commit'], canonical['path'])) == canonical['sha256']
paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', AUTHOR, PREP], cwd=ROOT).decode().splitlines() + [PLAN]
assert len(paths) == 5
result = {'author_commit': AUTHOR, 'frozen_failed_input': FROZEN, 'artifacts': [identity(AUTHOR, p) for p in paths],
          'exact_only_change': 'Add Nat.zero_le to existing rationalResidualCount_actual simp-only proof list',
          'all_headers_definitions_other_proof_bytes_fixed': True, 'sum_and_trailing_rfl_byte_equal': True,
          'pinned_core_api': pins['pinned_api'], 'actual_failed_stdout_sha256': sha(failed),
          'static_plan_sha256': sha(plan_bytes), 'all178_actual_successful_source_hashes_fixed': fixed,
          'module_metadata_imports_order_targets_counts_external_context_fixed': True, 'runtime_budget': budget,
          'actual178_canonical': canonical, 'compiler_invoked': False, 'dispatch_or_launch_authorized_by_review': False}
(BASE / 'actual178-rational-zero-flag-authentication.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'files': len(paths), 'exact_source_sha256': sha(new), 'plan_sha256': sha(plan_bytes), 'fixed178': len(fixed), 'selection': '179/501', 'planning_seconds': 775, 'compiler_invoked': False}))
