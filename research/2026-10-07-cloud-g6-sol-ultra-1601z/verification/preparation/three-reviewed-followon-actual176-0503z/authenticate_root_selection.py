import hashlib, json, subprocess, re
from pathlib import Path

G = ['git', '--git-dir=/workspace/research-commons/.git']
PREP = '8cd0359fe0cc87cdaa942d9635f90ab0148abc18'
ACTUAL = '9331aa9c029672005b4261d9c027de878f1d31f1'
AUTHOR = 'f8fedafff2db688efd0c92d96ff6ebca0fb45bb9'
HEAD = '0657f06aadc93f546b7282731f36301c15d0c131'
ROOT = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/'
PLAN_PATH = ROOT + 'verification/freeze-plans/three-reviewed-followon-actual176-static.json'
BASE = ROOT + 'verification/evidence/g6-run-37727661477-PASS/'

def get(ref, path):
    raw = subprocess.check_output(G + ['show', ref + ':' + path])
    blob = subprocess.check_output(G + ['rev-parse', ref + ':' + path], text=True).strip()
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blob
    return raw, blob

def js(ref, path):
    return json.loads(get(ref, path)[0])

raw, blob = get(PREP, PLAN_PATH)
remote = json.load(open('/workspace/root-179-static-plan-remote.json'))
assert raw.decode() == remote['content'] and blob == remote['sha']
assert hashlib.sha256(raw).hexdigest() == 'd6b0baeaa3f8bf3dd9e77a237c5601bedb75009aa7afea0a4e41b2d76435f9af'
p = json.loads(raw)
actual = js(AUTHOR, BASE + 'inputs-recovered.json')
assert actual['source_commit'] == ACTUAL
assert len(actual['modules']) == 176 == p['unchanged_accepted_custom_modules']
assert p['targets'][:-3] == actual['targets']
assert p['topological_order'][:-3] == actual['topological_order']
assert len(p['modules']) == p['custom_modules'] == 179
assert p['targets'][-3:] == p['topological_order'][-3:] == p['new_modules']
assert set(p['modules']) - set(actual['modules']) == set(p['new_modules'])
checks = []
for name, old in actual['modules'].items():
    new = p['modules'][name]
    assert old['sha256'] == new['sha256'] and old['imports'] == new['imports']
    before, oldblob = get(ACTUAL, new['repository_path'])
    current, nowblob = get(HEAD, new['repository_path'])
    assert before == current and oldblob == nowblob
    assert hashlib.sha256(before).hexdigest() == new['sha256']
    checks.append({'module': name, 'path': new['repository_path'], 'sha256': new['sha256'], 'blob': nowblob})
assert set(p['mathlib_roots']) - set(actual['mathlib_roots']) == {'Mathlib.Algebra.BigOperators.Group.Finset.Piecewise'}
assert set(actual['mathlib_roots']) <= set(p['mathlib_roots'])
assert p['lean_roots'] == ['Lean.Elab.Tactic.Omega']
copies = []
for item in p['new_module_original_and_copy_pins']:
    ref = item.get('accepted_derivative_commit', item['original_commit'])
    path = item.get('accepted_derivative_path', item['original_path'])
    original, origblob = get(ref, path)
    staged, stageblob = get(PREP, item['staged_path'])
    assert original == staged and origblob == stageblob
    assert hashlib.sha256(staged).hexdigest() == item['sha256']
    names = re.findall(r'^(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev)\s+(\S+)', staged.decode(), re.M)
    assert names == item['selected_names'] and len(names) == item['named_count']
    copies.append({'module': item['module'], 'source_ref': ref, 'source_path': path, 'staged_path': item['staged_path'], 'sha256': item['sha256'], 'blob': stageblob, 'bytes': len(staged), 'names': names})
oldnames = re.findall(r'^#print axioms\s+(\S+)', get(AUTHOR, BASE + 'DeclarationAudit-reconstructed.lean')[0].decode(), re.M)
assert len(oldnames) == 463
assert sum(p['named_counts'].values()) == p['named_total'] == 501
assert sum(item['named_count'] for item in p['new_module_original_and_copy_pins']) == 38
assert p['namespace_counts'] == {'G6': 352, 'G3': 134, 'G5': 15}
b = p['runtime_budget']
assert b['planning_total_seconds'] == 740 + 40 + 10 + 100 == 890
assert b['job_cap_seconds'] == 900 and b['per_command_cap_seconds'] == 180
assert b['flags'] == ['--trust=0', '-j1', '-M4096']
assert p['external_root_addition']['new_transitive_source_modules'] == []
controls = []
for path in [ROOT + 'verification/verify.sh', '.github/workflows/g6-cloud-lean.yml']:
    old, ob = get(ACTUAL, path); current, cb = get(HEAD, path)
    assert old == current and ob == cb
    controls.append({'path': path, 'sha256': hashlib.sha256(current).hexdigest(), 'blob': cb})
primary = json.load(open('/workspace/root-179-primary-review-remote.json'))
assert hashlib.sha256(primary['content'].encode()).hexdigest() == '4f23e93dc359a9c3653e33254298cf668ab2cd670f4266e043b26f837fd123d9'
result = {'status': 'ROOT STATIC AUTHENTICATION PASS; no compiler invoked', 'actual_input': ACTUAL, 'author': AUTHOR, 'current_source_head': HEAD, 'prep': PREP, 'plan_path': PLAN_PATH, 'plan_sha256': hashlib.sha256(raw).hexdigest(), 'plan_blob': blob, 'all176_source_imports_and_current_bytes_exact': checks, 'old_targets_topological_prefix_exact': True, 'old_selected463_audit_count': len(oldnames), 'three_exact_sources_and_raw_selected_names': copies, 'requested_custom': 179, 'requested_named': 501, 'namespace_counts': p['namespace_counts'], 'budget': b, 'controls_unchanged': controls, 'primary_selection_sha256': hashlib.sha256(primary['content'].encode()).hexdigest(), 'compiler_invoked': False}
Path('/workspace/root-179-final-selection-auth.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({'status': result['status'], 'actual_sources': len(checks), 'copies': len(copies), 'custom': 179, 'named': 501, 'plan_sha256': result['plan_sha256'], 'budget': 890, 'controls_checked': len(controls)}))
