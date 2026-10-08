"""Read-only Git/JSON selection authentication; never invokes a Lean/source program."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess

REPO = pathlib.Path(__file__).resolve().parents[2]
OWN = pathlib.Path(__file__).resolve().parent
PREP_COMMIT = 'f6c18f8dee6ffbbd80d04df237e1fc767ceca37d'
FROZEN = '62e937a2b58f00f6ed1197133650b6da2f96f71f'
AUTHOR = 'cdf4c4c0f9e0f6de59a7701b14656565a84cc481'
VER = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/'
PREP = VER + 'preparation/finite-observation-actual179-0702z/'
PLAN_PATH = VER + 'freeze-plans/finite-observation-actual179-static.json'
PLAN_SHA = '897902afd0c20ad4b896e58b056ae2ab721af404131231fca5da5b90a57a5489'


def git(*args, cwd=REPO):
    return subprocess.check_output(['git', *args], cwd=cwd)


def at(commit, path):
    return git('show', commit + ':' + path)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def blob(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def record(commit, path, data=None):
    data = at(commit, path) if data is None else data
    b = git('rev-parse', commit + ':' + path).decode().strip()
    assert blob(data) == b
    return {'commit': commit, 'path': path, 'bytes': len(data),
            'sha256': sha(data), 'git_blob_sha': b}


def js(commit, path):
    return json.loads(at(commit, path))


def imports(data):
    source = data.decode()
    clean, depth, index = [], 0, 0
    while index < len(source):
        if source[index:index + 2] == '/-':
            depth += 1
            index += 2
        elif depth and source[index:index + 2] == '-/':
            depth -= 1
            index += 2
        elif depth:
            if source[index] == '\n':
                clean.append('\n')
            index += 1
        else:
            clean.append(source[index])
            index += 1
    result = []
    for line in ''.join(clean).splitlines():
        match = re.match(r'\s*(?:public\s+)?import\s+(.+)', line)
        if match:
            result.extend(match[1].split('--')[0].split())
    return result


def selected(data):
    source = data.decode()
    namespace = re.search(r'^namespace\s+(\S+)\s*$', source, re.MULTILINE)[1]
    return [namespace + '.' + n for n in re.findall(
        r'^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_\']+)',
        source, re.MULTILINE)]


plan = js(PREP_COMMIT, PLAN_PATH)
assert sha(at(PREP_COMMIT, PLAN_PATH)) == PLAN_SHA
old = js(FROZEN, VER + 'freeze-plans/rational-zero-flag-actual178-repair-static.json')
actual = json.loads((OWN / 'three-followon-pass-37738512508-independent.json').read_bytes())
assert actual['run']['id'] == 37738512508
assert actual['successful_custom_modules'] == 179 and actual['selected_report_count'] == 501
assert actual['complete_inventory_receipt']['declaration_count'] == 4209
assert actual['complete_inventory_receipt']['theorem_declaration_count'] == 2766
assert actual['complete_inventory_receipt']['sha256'] == plan['prior_actual_inventory_sha256']
assert not actual['failed_custom_modules'] and not actual['blocked_custom_modules']
inputs_path = VER + 'evidence/g6-run-37738512508-PASS/inputs-recovered.json'
inputs = js(AUTHOR, inputs_path)
assert inputs['source_commit'] == FROZEN
assert inputs['targets'] == old['targets']
assert inputs['topological_order'] == old['topological_order']
assert plan['targets'][:45] == inputs['targets'] and len(plan['targets']) == 47
assert plan['topological_order'][:179] == inputs['topological_order']
assert plan['topological_order'][179:] == plan['new_modules'] == plan['targets'][45:]
assert list(plan['modules'])[:179] == list(old['modules'])
assert len(plan['modules']) == plan['custom_modules'] == 181
assert plan['unchanged_accepted_custom_modules'] == 179
assert plan['mathlib_roots'] == old['mathlib_roots'] == inputs['mathlib_roots']
assert plan['lean_roots'] == old['lean_roots'] == ['Lean.Elab.Tactic.Omega']
assert len(plan['mathlib_roots']) == 68 and plan['external_root_addition'] == []
assert plan['external_context_sha256'] == old['external_context_sha256']
assert plan['actual_runtime_dependencies'] == inputs['dependencies']

prep_paths = git('ls-tree', '-r', '--name-only', PREP_COMMIT, PREP).decode().splitlines()
assert len(prep_paths) == 9
artifacts = [record(PREP_COMMIT, path) for path in [PLAN_PATH, *prep_paths]]
pins = js(PREP_COMMIT, PREP + 'SOURCE-PINS.json')
api = js(PREP_COMMIT, PREP + 'API-INPUTS.json')
unchanged = js(PREP_COMMIT, PREP + 'UNCHANGED179-AUTHENTICATION.json')
assert pins['modules'] == plan['new_module_original_and_copy_pins']
assert len(unchanged['all179_exact_hash_import_and_blob_size_comparisons']) == 179
assert not unchanged['compiler_invoked']
declared179 = {x['module']: x for x in unchanged['all179_exact_hash_import_and_blob_size_comparisons']}
actual179 = {x['module']: x for x in actual['source_checks']}
source_data, checks179 = {}, []
for module in inputs['topological_order']:
    newrec, oldrec, tested = plan['modules'][module], old['modules'][module], inputs['modules'][module]
    assert newrec == oldrec
    path = newrec['repository_path']
    data = at(FROZEN, path)
    assert data == at(PREP_COMMIT, path)
    assert sha(data) == newrec['sha256'] == tested['sha256'] == actual179[module]['sha256']
    assert imports(data) == newrec['imports'] == tested['imports']
    pin = declared179[module]
    assert pin['repository_path'] == path and pin['sha256'] == sha(data)
    assert pin['git_blob_sha'] == blob(data) and pin['bytes'] == len(data)
    assert pin['imports'] == imports(data)
    assert len(data) == actual179[module]['bytes'] and blob(data) == actual179[module]['git_blob']
    source_data[module] = data
    checks179.append({'module': module, 'repository_path': path, 'sha256': sha(data),
                      'bytes': len(data), 'git_blob_sha': blob(data), 'imports': imports(data)})

new_checks = []
for pin in pins['modules']:
    data = at(PREP_COMMIT, pin['staged_path'])
    original = at(pin['original_commit'], pin['original_path'])
    assert data == original
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes']
    assert blob(data) == pin['git_blob_sha']
    assert plan['modules'][pin['module']]['repository_path'] == pin['future_formal_path']
    assert plan['modules'][pin['module']]['sha256'] == sha(data)
    assert plan['modules'][pin['module']]['imports'] == imports(data)
    assert selected(data) == pin['selected_names_actual_runner']
    assert len(selected(data)) == pin['selected_count']
    assert len(re.findall(r'^#print axioms ', data.decode(), re.MULTILINE)) == pin['printed_count']
    source_data[pin['module']] = data
    new_checks.append({**pin, 'staged_equals_original': True, 'imports': imports(data)})
assert [x['selected_count'] for x in new_checks] == [10, 2]

derived_order, visited, externals, lean_roots = [], set(), set(), set()


def visit(module):
    if module.startswith('Mathlib.'):
        externals.add(module)
        return
    if module.startswith(('Lean.', 'Std.', 'Init.')):
        lean_roots.add(module)
        return
    if module in visited:
        return
    assert module in source_data, 'New unselected custom dependency: ' + module
    visited.add(module)
    for imp in imports(source_data[module]):
        visit(imp)
    derived_order.append(module)


for target in plan['targets']:
    visit(target)
assert derived_order == plan['topological_order']
assert sorted(externals) == plan['mathlib_roots']
assert sorted(lean_roots) == plan['lean_roots']
assert (at(PREP_COMMIT, PREP + 'REQUESTED-TARGETS.txt').decode().split()) == plan['targets']
all_names = []
for target in plan['targets']:
    names = selected(source_data[target])
    assert len(names) == plan['named_counts'][target]
    if target in old['named_counts']:
        assert old['named_counts'][target] == len(names)
    all_names.extend(names)
assert all_names[:501] == [x['name'] for x in actual['selected_reports']]
assert len(all_names) == len(set(all_names)) == plan['named_total'] == 513
counts = {'G6': sum(n.startswith(('UnifiedLean.G6.', 'CloudG6.')) for n in all_names),
          'G3': sum(n.startswith('CloudG3.') for n in all_names),
          'G5': sum(n.startswith('GProgram.G5.') for n in all_names)}
assert counts == plan['namespace_counts'] == {'G6': 364, 'G3': 134, 'G5': 15}

providers = []
for pin in pins['providers']:
    module, path = pin['module'], pin['repository_path']
    data = at(FROZEN, path)
    assert data == at(PREP_COMMIT, path) == source_data[module]
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes'] and blob(data) == pin['git_blob_sha']
    assert imports(data) == pin['imports']
    providers.append({**pin, 'matches_actual179': True})
assert api['provider_pins'] == pins['providers']
review = pins['source_review']
assert sha(at(review['commit'], review['path'])) == review['sha256']
review_pin = record(review['commit'], review['path'])

control_checks = []
for pin in plan['controls']:
    data = at(FROZEN, pin['repository_path'])
    assert data == at(PREP_COMMIT, pin['repository_path'])
    assert sha(data) == pin['sha256'] and blob(data) == pin['git_blob_sha'] and len(data) == pin['bytes']
    control_checks.append({**pin, 'frozen179_equals_preparation': True})
assert plan['controls'] == unchanged['controls']
run_source = at(FROZEN, plan['controls'][0]['repository_path']).decode()
assert "timeout=180" in run_source and "'--trust=0', '-j1', '-M4096'" in run_source
assert "{'propext', 'Classical.choice', 'Quot.sound'}" in run_source
assert 'complete_environment.prepare' in run_source and 'complete_environment.recover' in run_source
workflow = at(FROZEN, '.github/workflows/g6-cloud-lean.yml').decode()
assert 'timeout-minutes: 15' in workflow
mathlib_root = pathlib.Path('/workspace/g6-build/deps/mathlib')
mathlib = []
assert git('rev-parse', 'HEAD', cwd=mathlib_root).decode().strip() == '0df444a360eaa60ab8c11dca51a86af692955474'
for pin in api['mathlib']:
    data = (mathlib_root / pin['path']).read_bytes()
    assert sha(data) == pin['sha256'] and len(data) == pin['bytes'] and blob(data) == pin['git_blob_sha']
    assert data == git('show', pin['commit'] + ':' + pin['path'], cwd=mathlib_root)
    mathlib.append({**pin, 'actual_pinned_interface_bytes_match': True})

budget = plan['runtime_budget']
timing_path = VER + 'evidence/g6-run-37738512508-PASS/runtime-timing.json'
timing = js(AUTHOR, timing_path)
prep_timing = js(PREP_COMMIT, PREP + 'ACTUAL-TIMING-AND-BUDGET.json')
assert timing == prep_timing['actual179_timing']
assert budget == prep_timing['candidate181_budget']
assert timing['job_elapsed_seconds'] == budget['actual179_job_seconds'] == 768
assert timing['serial_step_elapsed_seconds'] == budget['actual179_serial_seconds'] == 736
assert budget['new_source_reserve_seconds_total'] == 2 * budget['new_source_reserve_seconds_each'] == 20
assert budget['planning_total_seconds'] == 768 + 20 + 10 + 100 == 898
assert budget['planning_total_seconds'] < budget['job_cap_seconds'] == 900
assert budget['per_command_cap_seconds'] == 180 and budget['flags'] == ['--trust=0', '-j1', '-M4096']
receipts = js(AUTHOR, VER + 'evidence/g6-run-37738512508-PASS/receipts-recovered.json')
comparable = []
for pin in budget['comparable_actual_receipts']:
    candidates = [x for x in receipts if pathlib.PurePosixPath(x['argv'][-1]).name == pin['source']]
    assert len(candidates) == 1
    rec = candidates[0]
    assert rec['exit'] == pin['exit'] == 0 and rec['start'] == pin['start'] and rec['end'] == pin['end']
    assert rec['output_sha256'] == pin['stdout_sha256']
    elapsed = (datetime.datetime.fromisoformat(rec['end']) - datetime.datetime.fromisoformat(rec['start'])).total_seconds()
    assert elapsed == pin['elapsed_seconds']
    comparable.append(pin)

result = {
    'status': 'PRIMARY SOURCE/API + EXACT STATIC SELECTION ACCEPT; no compiler or launch authorization',
    'preparation_commit': PREP_COMMIT, 'plan': record(PREP_COMMIT, PLAN_PATH),
    'artifact_checks': artifacts, 'actual_baseline_run': 37738512508,
    'actual_baseline_frozen': FROZEN, 'actual_author_receipt': AUTHOR,
    'actual_primary_acceptance': {'commit': '7126a5d4386652abbcfb224f075d0dcfac716797',
        'path': 'research/2026-10-07-cloud-independent-auditor-1616z/THREE-FOLLOWON-179-COMPLETE-VERIFIED-PASS-REVIEW.md',
        'sha256': 'c63888273c81902d4c3685a4099dea2684467939909648c03acf8f4d1e93101c'},
    'actual_baseline_counts': {'custom': 179, 'named': 501, 'owned': 4209, 'theorems': 2766},
    'unchanged179_comparisons': len(checks179),
    'unchanged179_comparison_json_sha256': sha((json.dumps(checks179, sort_keys=True) + '\n').encode()),
    'all179_frozen_preparation_and_actual_hash_blob_size_imports_match': True,
    'old_topological179_and_targets45_and_selected501_prefix_exact': True,
    'new_sources': new_checks, 'prior_source_review': review_pin,
    'direct_providers': providers, 'mathlib_interfaces': mathlib, 'control_checks': control_checks,
    'derived_custom_dag': 181, 'targets': 47, 'selected_names': 513,
    'selected_namespace_counts': counts, 'new_selected_names': all_names[501:],
    'external_roots': {'Mathlib': 68, 'Lean': 1, 'new_roots': [],
        'same_recorded_header_context_sha256': plan['external_context_sha256'],
        'broader_header_context_modules': 3584, 'actual_prior_cache_context_modules': 3302,
        'full_external_context_rehashed_by_reviewer': False,
        'fresh_owner_external_pin_and_runtime_guards_required_before_freeze': True},
    'actual_runtime_dependencies_identical': True, 'budget': budget,
    'actual_timing_pin': record(AUTHOR, timing_path), 'comparable_receipts_authenticated': comparable,
    'budget_is_estimate_only': True, 'launch_requires_separate_root_gate_and_fresh_owner_guards': True,
    'compiler_invoked': False, 'author_prepare_script_executed': False,
    'mathematical_or_numerical_program_executed': False,
    'scope': 'Pairwise finite-PMF shared-corruption geometry and one exact native compiled observation; no wrong-image/master closure.'
}
assert sha(at(result['actual_primary_acceptance']['commit'], result['actual_primary_acceptance']['path'])) == result['actual_primary_acceptance']['sha256']
output = OWN / 'finite-observation-actual179-181-selection-authentication.json'
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'old_fixed': 179, 'proposed_custom': 181,
                  'proposed_named': 513, 'budget_estimate': 898, 'output': str(output.relative_to(REPO))}))
