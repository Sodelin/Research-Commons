"""Static source-connected selection only: no Lean, Actions or repository mutation."""
from pathlib import Path
import ast, collections, datetime, hashlib, json, re, shutil

root = Path('/workspace/cloud-lean')
packet = 'research/2026-10-07-cloud-g6-sol-ultra-1601z'
snapshot = Path('/tmp/g6-frozen-62e937a2b58f00f6ed1197133650b6da2f96f71f')
frozen = '62e937a2b58f00f6ed1197133650b6da2f96f71f'
evidence = root / packet / 'verification/evidence/g6-run-37738512508-PASS'
prep = packet + '/verification/preparation/finite-observation-actual179-0702z'
plan_path = packet + '/verification/freeze-plans/finite-observation-actual179-static.json'
sha = lambda b: hashlib.sha256(b).hexdigest()
blob = lambda b: hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
actual = json.loads((evidence / 'inputs-recovered.json').read_text())
old = json.loads((snapshot / packet / 'verification/freeze-plans/rational-zero-flag-actual178-repair-static.json').read_text())
audit = json.loads((evidence / 'axiom-audit-recovered.json').read_text())
owned = json.loads((evidence / 'complete-environment-inventory.json').read_text())
assert actual['source_commit'] == frozen and len(actual['modules']) == 179
assert len(audit['named_declarations']) == 501 and owned['declaration_count'] == 4209
assert old['targets'] == actual['targets'] and old['topological_order'] == actual['topological_order']
control_root = Path('/tmp/g6-181-immutable-controls')
runner = (control_root / packet / 'verification/run.py').read_bytes()
assert sha(runner) == actual['dependencies']['verification_script_sha256']
tree = ast.parse(runner.decode())
node = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'lean_imports')
namespace = {'re': re}
exec(compile(ast.Module(body=[node], type_ignores=[]), '<pinned lean_imports ONLY>', 'exec'), namespace)
imports = namespace['lean_imports']
modules, source, all_current = {}, {}, []
for name, rec in old['modules'].items():
    data = (snapshot / rec['repository_path']).read_bytes()
    assert sha(data) == rec['sha256'] == actual['modules'][name]['sha256']
    assert imports(data.decode()) == rec['imports'] == actual['modules'][name]['imports']
    modules[name] = rec.copy()
    source[name] = data
    all_current.append({'module': name, 'repository_path': rec['repository_path'],
                        'sha256': sha(data), 'git_blob_sha': blob(data), 'bytes': len(data),
                        'imports': rec['imports']})

bodies = json.loads(Path('/tmp/g6-181-original-immutable-bodies.json').read_text())
new = [
    ('UnifiedLean.G6.FiniteCorruptionBoundary', 'finite',
     'proof-drafts/UnifiedLean/G6/FiniteCorruptionBoundary.lean',
     'UnifiedLean/G6/FiniteCorruptionBoundary.lean',
     '25d5afd4e2032613539d5d0d39308d4eff98d642ae8eaec361a4f3f5db3edbcf'),
    ('ActualObservationCorruption', 'actual', 'proof-drafts/ActualObservationCorruption.lean',
     'ActualObservationCorruption.lean',
     '201fe29b7efb33277625da5515cd5659f8f60a471c91d86b366c303ba55fc754'),
]
pins, counts = [], dict(audit['module_counts'])
for name, key, original_suffix, suffix, expected in new:
    data = bodies[key].encode()
    assert sha(data) == expected
    staged = root / prep / 'sources' / suffix
    staged.parent.mkdir(parents=True, exist_ok=True)
    staged.write_bytes(data)
    ns = re.search(r'^namespace\s+(\S+)\s*$', data.decode(), re.M)[1]
    selected = [ns + '.' + n for n in re.findall(
        r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)", data.decode(), re.M)]
    printed = re.findall(r'^#print axioms (\S+)', data.decode(), re.M)
    rec = {'repository_path': packet + '/sources/' + suffix,
           'sha256': expected, 'imports': imports(data.decode())}
    modules[name], source[name], counts[name] = rec, data, len(selected)
    pins.append({'module': name, 'original_commit': '525ae7abb1e29d42630c20d1d9035958745aa26d',
                 'original_path': 'research/2026-10-08-cloud-finite-corruption-source-0424z/' + original_suffix,
                 'staged_path': str(staged.relative_to(root)), 'future_formal_path': rec['repository_path'],
                 'sha256': expected, 'git_blob_sha': blob(data), 'bytes': len(data),
                 'selected_names_actual_runner': selected, 'selected_count': len(selected),
                 'printed_names': printed, 'printed_count': len(printed),
                 'byte_identical_immutable_original': True, 'compiler_status': 'UNCHECKED'})

targets = actual['targets'] + [x[0] for x in new]
order, seen, external, lean = [], set(), set(), set()
def visit(name):
    if name.startswith('Mathlib.'):
        external.add(name); return
    if name.startswith(('Lean.', 'Std.', 'Init.')):
        lean.add(name); return
    if name in seen: return
    assert name in modules, name
    seen.add(name)
    for dep in modules[name]['imports']: visit(dep)
    order.append(name)
for name in targets: visit(name)
assert len(seen) == 181 and len(targets) == 47 and sum(counts.values()) == 513
assert order[:179] == actual['topological_order']
assert sorted(external) == actual['mathlib_roots'] == old['mathlib_roots']
assert sorted(lean) == old['lean_roots']
assert all(modules[n] == old['modules'][n] for n in actual['modules'])

timing = json.loads((evidence / 'runtime-timing.json').read_text())
commands = json.loads((evidence / 'receipts-recovered.json').read_text())
dt = lambda s: datetime.datetime.fromisoformat(s.replace('Z', '+00:00'))
comparable_names = {'FiniteProbability', 'Conditioning', 'ResidualPrefix', 'MeanEnclosure', 'ProgramPrefix', 'RationalCertificate'}
comparables = []
for r in commands:
    if r['argv'][-1].split('/')[-1].removesuffix('.lean') in comparable_names:
        comparables.append({'source': r['argv'][-1].split('/')[-1], 'start': r['start'], 'end': r['end'],
                            'elapsed_seconds': (dt(r['end']) - dt(r['start'])).total_seconds(),
                            'exit': r['exit'], 'stdout_sha256': r['output_sha256']})
budget = {'actual179_job_seconds': 768, 'actual179_serial_seconds': 736,
          'new_source_reserve_seconds_each': 10, 'new_source_reserve_seconds_total': 20,
          'audit_growth_reserve_seconds': 10, 'runtime_cache_variation_margin_seconds': 100,
          'planning_total_seconds': 898, 'job_cap_seconds': 900, 'per_command_cap_seconds': 180,
          'flags': ['--trust=0', '-j1', '-M4096'],
          'justification': 'Two 4689B/2855B sources, using only already accepted imports and identical external roots. Comparable actual finite-PMF/TV provider commands take 2.99–4.10s. Reserve 10s per new source plus separate audit10/variation100. Estimate only, with enforced caps unchanged; no guarantee or retry.',
          'comparable_actual_receipts': comparables}
assert budget['planning_total_seconds'] == timing['job_elapsed_seconds'] + 20 + 10 + 100

provider_pins = []
for name in ['NaturalPastCompleteObservation', 'UnifiedLean.G6.FiniteProbability',
             'UnifiedLean.G6.MeanEnclosure', 'UnifiedLean.Source.SourceCalendarCompiler',
             'UnifiedLean.Source.SourceCalendarCompatibility', 'ActualCutJointLaw']:
    rec = modules[name]; data = source[name]
    provider_pins.append({'module': name, **rec, 'bytes': len(data), 'git_blob_sha': blob(data),
                          'compiler_status': 'Actual179 PASS'})
mathlib = Path('/workspace/g6-build/deps/mathlib')
api_pins = []
for path, facts in [
    ('Mathlib/Probability/ProbabilityMassFunction/Constructions.lean', ['PMF.ofFintype requires exact finite ENNReal mass one']),
    ('Mathlib/Data/ENNReal/BigOperators.lean', ['ofReal_sum_of_nonneg requires every finite real summand nonnegative']),
    ('Mathlib/Data/ENNReal/Basic.lean', ['toReal_ofReal requires a nonnegative real coordinate']),
]:
    data = (mathlib / path).read_bytes()
    api_pins.append({'path': path, 'commit': actual['dependencies']['mathlib_commit'],
                     'sha256': sha(data), 'bytes': len(data), 'git_blob_sha': blob(data), 'interface': facts})

controls = []
for path in [packet + '/verification/run.py', packet + '/verification/verify.sh',
             packet + '/verification/complete_environment.py', '.github/workflows/g6-cloud-lean.yml',
             '.github/workflows/cloud-g5-sol-ultra.yml',
             'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean']:
    data = (control_root / path).read_bytes()
    controls.append({'repository_path': path, 'sha256': sha(data), 'git_blob_sha': blob(data), 'bytes': len(data)})

plan = {'status': 'STATIC ONLY181/513 source-connected finite corruption boundary after actual179 PASS; no integration/build/dispatch',
        'prior_verified_input': frozen, 'prior_actual_run': 37738512508,
        'prior_actual_receipt_commit': 'cdf4c4c0f9e0f6de59a7701b14656565a84cc481',
        'prior_independent_acceptance': {'status': 'Canonical actual179 source/full-inventory/author correspondence ACCEPT; not a new launch gate',
            'commit': '7126a5d4386652abbcfb224f075d0dcfac716797',
            'path': 'research/2026-10-07-cloud-independent-auditor-1616z/THREE-FOLLOWON-179-COMPLETE-VERIFIED-PASS-REVIEW.md',
            'sha256': 'c63888273c81902d4c3685a4099dea2684467939909648c03acf8f4d1e93101c'},
        'prior_actual_custom': 179, 'prior_actual_named': 501, 'prior_actual_complete_owned': 4209,
        'prior_actual_complete_theorems': 2766, 'prior_actual_inventory_sha256': sha((evidence / 'complete-environment-inventory.json').read_bytes()),
        'targets': targets, 'custom_modules': 181, 'mathlib_roots': sorted(external), 'lean_roots': sorted(lean),
        'topological_order': order, 'modules': modules, 'named_counts': counts, 'named_total': 513,
        'namespace_counts': {'G6': 364, 'G3': 134, 'G5': 15},
        'unchanged_accepted_custom_modules': 179, 'new_modules': [x[0] for x in new],
        'new_module_original_and_copy_pins': pins, 'complete_inventory': 'Unchanged full generated/type/body/transitive-axiom audit over every actually successful custom module; failed/dependency-blocked modules excluded.',
        'external_root_addition': [], 'external_context_sha256': old['external_context_sha256'],
        'controls': controls, 'actual_runtime_dependencies': actual['dependencies'], 'runtime_budget': budget,
        'source_scope': 'PAIRWISE finite-simplex sharp shared-corruption boundary, including one actual naturally initialized original compiled-calendar joint observation on a supplied finite alphabet.',
        'scientific_premises': 'Same actual natural completion/register/calendar providers. q is a generic PMF on the common finite alphabet, not assumed to be a native biological law.',
        'claims_excluded': ['Wrong native-target image/class closure or closest wrong-law attainment', 'Paired Q/S/G1 native graph admission', 'Whole biological observational-menu/pruning equality', 'Executable backend/table correspondence and G6 master closure'],
        'review_gate': 'Both originals have canonical source/API acceptance; matching actual179 primary receipt, exact181 static gate and fresh root ONE scope/budget/launch authorization are still required.',
        'dated_prior_full_generic_plan': 'Unpublished dated /tmp/g6-corruption-real-dag-generic-local.json:185 closure, not admitted; old Rational35e disposition superseded by actuald9f.',
        'alternatives': [{'custom': 180, 'named': 511, 'new_targets': ['UnifiedLean.G6.FiniteCorruptionBoundary'], 'planning_seconds': 888, 'scope': 'Finite PMF geometry only; new actual-source observation consumer remains unverified'},
                         {'custom': 185, 'named': 556, 'planning_seconds': 918, 'budget_basis': '768+40(new generic sources)+10audit+100variation', 'status': 'Does not fit900cap; preparation only; native-source consumers still excluded'},
                         {'custom': 338, 'status': 'Separate genuine native G1/G5/source consumer DAG; not enrolled or bounded by181', 'extra_custom_vs179': 159}]}
(root / plan_path).write_text(json.dumps(plan, indent=2) + '\n')
prep_dir = root / prep
(prep_dir / 'SOURCE-PINS.json').write_text(json.dumps({'status': 'Static exact originals only, compiler UNCHECKED', 'modules': pins,
    'providers': provider_pins, 'source_review': {'commit': '0657f06aadc93f546b7282731f36301c15d0c131',
    'path': 'research/2026-10-07-cloud-independent-auditor-1616z/FINITE-CORRUPTION-BOUNDARY-SOURCE-REVIEW.md',
    'sha256': sha(bodies['sourceGate'].encode())}}, indent=2) + '\n')
(prep_dir / 'API-INPUTS.json').write_text(json.dumps({'status': 'Read-only complete source and pinned interface checks; no compiler invocation',
    'mathlib': api_pins, 'provider_pins': provider_pins, 'checks': [
    'PMF midpoint normalization is actual finite mass-one and nonnegative real coefficients.',
    'TV symmetry, triangle, exact half-distance and strict validated margin use compiled unchanged providers.',
    'Actual observation uses original once-drawn register and actual completed compiledCalendarProgram; no desired observation law premise.',
    'ActualCutJointLaw namespace resolves TaggedEndpoint; no absent date alias in this new body.',
    'All import names belong to actual181 DAG; all179 prior source hashes/imports/order are unchanged.',
    'Actual runner selects12new names despite only10literal print directives; full generated ownership separately required.']}, indent=2) + '\n')
(prep_dir / 'ACTUAL-TIMING-AND-BUDGET.json').write_text(json.dumps({'actual179_timing': timing, 'candidate181_budget': budget, 'alternatives': plan['alternatives']}, indent=2) + '\n')
(prep_dir / 'UNCHANGED179-AUTHENTICATION.json').write_text(json.dumps({'actual_run': 37738512508, 'frozen': frozen,
    'all179_exact_hash_import_and_blob_size_comparisons': all_current, 'old_topological_prefix_fixed': True,
    'old45_targets_fixed': True, 'external_roots_identical': True, 'controls': controls, 'compiler_invoked': False}, indent=2) + '\n')
(prep_dir / 'REQUESTED-TARGETS.txt').write_text('\n'.join(targets) + '\n')
(prep_dir / 'README.md').write_text('''# Static first finite-corruption source boundary\n\nPreparation only:181 custom sources/513 runner-selected declarations (364G6,134G3,15G5),47targets. The two new sources are byte-identical source/API-accepted originals; all179 actually passed source hashes/imports/order and68Mathlib+1Lean roots remain unchanged. No formal sources, current targets, workflows, compiler or Actions job are changed by this packet.\n\nFiniteCorruptionBoundary proves sharp pairwise overlap of closed TV balls, including equality, using the actual finite PMF midpoint and a validated strict approximation-margin corollary. ActualObservationCorruption applies it to one actual naturally initialized compiled-calendar observation and any other PMF on the same finite joint alphabet. A corrupted midpoint need not be biological; native wrong-image admission/class closure, closest wrong-law attainment, paired target preservation, pruning/menu equality, executable tables and fullG6 remain separate.\n\nThe unchanged runner selects10+2names, although the literal sources print9+1. The full generated/type/body/transitive-axiom ownership audit remains mandatory; named reports alone do not establish whole environment acceptance.\n\nActual prior job768s/serial736s is the current timing baseline. Six comparable finite PMF/TV provider commands take2.99–4.10s. Candidate reserve is10s per new source, plus10audit and100variation:768+20+10+100=898s, an estimate within the unchanged900s job/180s command caps. Trust0/-j1/-M4096 and controls remain exact. The small margin is explicit, not a guarantee or automatic retry.180finite-only option888s leaves this new observation consumer unverified;185generic option918s does not fit, and native338DAG remains separate.\n\nNo launch is authorized. Canonical actual179 primary receipt, matching exact181 static/source selection and separate fresh root ONE scope/budget/launch gate must precede any owner integration.\n''')
out = []
for path in [*(p for p in prep_dir.rglob('*') if p.is_file()), root / plan_path]:
    data = path.read_bytes()
    out.append({'path': str(path.relative_to(root)), 'content': data.decode(), 'sha256': sha(data),
                'git_blob_sha': blob(data), 'bytes': len(data)})
Path('/tmp/g6-181-preparation-publication.json').write_text(json.dumps(sorted(out, key=lambda x: x['path']), ensure_ascii=False))
print(json.dumps({'custom': 181, 'named': 513, 'targets': 47, 'new_sources': [p['sha256'] for p in pins],
                  'plan_sha256': sha((root / plan_path).read_bytes()), 'files': len(out), 'budget': 898}, indent=2))
