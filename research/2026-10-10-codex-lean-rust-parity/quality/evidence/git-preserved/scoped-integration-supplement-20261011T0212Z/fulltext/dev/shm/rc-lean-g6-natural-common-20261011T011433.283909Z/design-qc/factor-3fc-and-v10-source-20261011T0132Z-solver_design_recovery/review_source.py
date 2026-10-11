"""Source-only independent standard-library reader; no target module import."""
import ast
import copy
import datetime
import difflib
import hashlib
import json
from pathlib import Path
import re

R = Path('/workspace/Research-Commons')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')
P = Path('/dev/shm/rc-lean-g6-natural-common-20261011T005738.287542Z')
Q = W / 'design-qc/factor-3fc-and-v10-source-20261011T0132Z-solver_design_recovery'
B = W / 'metadata/factor-ite-true-proof-repair-3fc98f89-20261011T012921.157357Z'
C = P / 'metadata/factor-proof-repair-5f0143f9-20261011T0109Z'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def pin(p, expected):
    assert sha(p) == expected, str(p)
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': expected}

def resolved(s):
    p = Path(s)
    return p if p.is_absolute() else R / p

def imports(text):
    return [m.group(1).strip() for m in re.finditer(r'^import\s+([^\n]+)$', text, re.M)]

oldp, newp = C / 'G6NaturalCommonForestFactorization.lean', B / 'G6NaturalCommonForestFactorization.lean'
oldpin = pin(oldp, '5f0143f9f266659cb35c495c3bbb01781039d1338a2eb527e1196bd419b6c4f9')
newpin = pin(newp, '3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4')
old, new = oldp.read_text(), newp.read_text()
attribution = 'selector is transported only by evaluation at the equal named vertex.\nAll declarations, physical values, imports and premises are unchanged.'
replacement = 'selector is transported only by evaluation at the equal named vertex.\nAll declarations, physical values, imports and premises are unchanged.\n\nProof-only follow-up to the actual 5f0143f9 run, 11 October 2026.\nThe remaining pointwise residual kernel equality explicitly reduces ite True.\nAll declarations, physical values, imports and premises are unchanged.'
oldline = '      simp only [residualEpoch, if_pos rfl]'
newline = '      simp only [residualEpoch, if_pos rfl, ite_true]'
assert old.count(attribution) == old.count(oldline) == 1
assert new == old.replace(attribution, replacement, 1).replace(oldline, newline, 1)
diffp = B / 'PROOF-ONLY-DIFF.patch'
diffpin = pin(diffp, 'c6a8f730fddbf4d69f43d76b4bf64f96f2aae65316c8732e3865f403f2489fe7')
assert diffp.read_text() == ''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True), fromfile=str(oldp), tofile=str(newp)))
oldfreeze = C / 'PROPOSAL-FREEZE-V8.json'
oldfreeze_pin = pin(oldfreeze, 'fdc04904a17a0c686231e2aa09e859e4b3d7461204d84dc191c5c39642a8ccfb')
freezep = B / 'PROPOSAL-FREEZE-V10-ITE-TRUE.json'
freezepin = pin(freezep, 'd54d69c760f24b6e6a2e6fb7310c6b6d5a489250663bfafb82b0adda62d9da9f')
f0, f1 = json.loads(oldfreeze.read_bytes()), json.loads(freezep.read_bytes())
for key in ('exact_composition', 'acceptance_bindings', 'discharges', 'remaining_interfaces'):
    assert f0[key] == f1[key], key
comp = f1['exact_composition']
assert (comp['closure_size'], comp['accepted_parent_count'], comp['new_roots']) == (141, 139, 2)
assert len(comp['topological_modules']) == len(set(comp['topological_modules'])) == 141
assert len(f0['sources']) == len(f1['sources']) == 2
head_rows = []
for i, (s0, s1) in enumerate(zip(f0['sources'], f1['sources'])):
    sp = resolved(s1['path'])
    assert sha(sp) == s1['sha256']
    text = sp.read_text()
    assert imports(text) == s1['imports'] == s0['imports']
    assert s0['module'] == s1['module']
    assert len(s0['declarations']) == len(s1['declarations']) == (5 if i == 0 else 24)
    for d0, d1 in zip(s0['declarations'], s1['declarations']):
        assert (d0['name'], d0['header'], d0['sha256']) == (d1['name'], d1['header'], d1['sha256'])
        assert hashlib.sha256(d1['header'].encode()).hexdigest() == d1['sha256']
        assert d1['header'] in text
        assert d1['line'] == d0['line'] + (0 if i == 0 else 4)
        head_rows.append({'module': s1['module'], 'name': d1['name'], 'header_sha256': d1['sha256']})
assert f1['sources'][0]['sha256'] == 'a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917'
assert sum(bool(re.match(r'(?:noncomputable )?def\b', d['header'])) for d in f1['sources'][1]['declarations']) == 8
providers = []
for row in comp['accepted_providers']:
    p = resolved(row['path'])
    assert sha(p) == row['sha256']
    assert imports(p.read_text()) == row['imports']
    providers.append({'module': row['module'], 'path': str(p), 'sha256': row['sha256'], 'imports': row['imports'], 'acceptance': row['acceptance']})
assert len(providers) == len({r['module'] for r in providers}) == 139
identityp = B / 'IDENTITY.json'
identitypin = pin(identityp, '56586ecfe4484ca634da79d9eca0dc794a741180501657de7d2c9273b56bea33')
identity = json.loads(identityp.read_bytes())
for key, pinned in (('source', newpin), ('diff', diffpin), ('freeze', freezepin), ('previous_source', oldpin)):
    assert identity[key] == pinned
stdoutp = W / '.build/runs/20261011T012303.766984Z/attempts/00001-G6NaturalCommonForestFactorization/stdout'
stdoutpin = pin(stdoutp, '44a0b362bf2e1033f9a1108c040bda3860814b1bbc1b062be12f8bbb6a6ac13f')
assert identity['preserved_actual_diagnostic'] == stdoutpin
errors = re.findall(r'^.*\.lean:\d+:\d+: error:.*$', stdoutp.read_text(), re.M)
assert len(errors) == 1 and ':297:76: error: unsolved goals' in errors[0]

oldprepp = P / 'scripts/prepare_g6_natural_common_factorization_20261011_v9_shmem_metadata.py'
newprepp = W / 'scripts/prepare_g6_natural_common_factorization_20261011_v10_shmem_metadata.py'
oldpreppin = pin(oldprepp, '41e1e65485c5ae4764b963df95f10bc881eecbaffb459fe560c806a3e8db8614')
newpreppin = pin(newprepp, '7ea1b1f9d4b917bcf33d91246bfc4920e70a6783179e589b76875e9d7add181e')
a, b = ast.parse(oldprepp.read_bytes()), ast.parse(newprepp.read_bytes())
assigns = lambda tree: [n for n in tree.body if isinstance(n, ast.Assign) and len(n.targets) == 1 and isinstance(n.targets[0], ast.Name) and n.targets[0].id == 'FREEZE']
fa, fb = assigns(a), assigns(b)
assert len(fa) == len(fb) == 1
assert ast.unparse(fb[0].value) == "Path(" + repr(str(freezep)) + ")"
fb[0].value = copy.deepcopy(fa[0].value)
def dict_slot(tree):
    rows = []
    for n in ast.walk(tree):
        if isinstance(n, ast.Dict):
            for i, k in enumerate(n.keys):
                if isinstance(k, ast.Constant) and k.value == 'source_repair_derivation':
                    rows.append((n, i))
    assert len(rows) == 1
    return rows[0]
da, ia = dict_slot(a)
db, ib = dict_slot(b)
assert isinstance(da.values[ia], ast.Dict) and isinstance(db.values[ib], ast.Dict)
db.values[ib] = copy.deepcopy(da.values[ia])
newhash = [n for n in ast.walk(b) if isinstance(n, ast.Constant) and n.value == freezepin['sha256']]
oldhash = [n for n in ast.walk(a) if isinstance(n, ast.Constant) and n.value == oldfreeze_pin['sha256']]
assert len(newhash) == len(oldhash) == 1
newhash[0].value = oldhash[0].value
assert ast.dump(a) == ast.dump(b), 'Unapproved preparer AST delta'
derivationp = W / 'metadata/natural-v10-preparer/SOURCE-ONLY-DERIVATION.json'
derivationpin = pin(derivationp, '433e12e4b45f94332a6034faa587d71b9d176d562aeb92d4ed72b3b111602a72')

failurep = Q / 'OWN-INLINE-PREFLIGHT-COLUMN-ASSUMPTION-FAILURE.json'
failure = {'schema': 'independent_reader_preflight_correction_v1', 'contributor': 'Codex / solver_design_recovery', 'status': 'PRESERVED_OWN_READER_ASSUMPTION_FAILURE', 'prior_inline_reader_failure': 'Own preliminary inline reader guessed diagnostic column 297:4 after all preceding byte/header/provider checks. Actual preserved stdout is 297:76. No source/producer/import/runtime mutation occurred and no PASS receipt was emitted.', 'actual_stdout': stdoutpin, 'actual_errors': errors, 'corrected_check': 'Exactly one error with actual line/column 297:76; full stdout bytes remain strictly pinned.'}
with failurep.open('x') as f:
    json.dump(failure, f, indent=2, sort_keys=True)
    f.write('\n')
report = {
    'schema': 'natural_factor_ite_true_and_v10_preparer_static_design_qc_v1',
    'contributor': 'Codex / solver_design_recovery',
    'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'PASS_SOURCE_ONLY_SINGLE_ITE_TRUE_PROOF_REPAIR_AND_EXACT_PREPARER_DERIVATIVE',
    'source': newpin, 'preserved_parent_source': oldpin, 'proposal_freeze': freezepin, 'preserved_parent_freeze': oldfreeze_pin, 'proof_only_diff': diffpin, 'identity': identitypin, 'preserved_actual_5f_failure_stdout': stdoutpin,
    'whole_source_equality': 'Exact parent bytes after one attribution replacement and one proof-line addition of ite_true. All literal statements, eight value definitions, hypotheses, physical values, imports and options retained.',
    'authoritative_heads': head_rows, 'accepted_parent_source_import_pairs': providers,
    'composition': {'executed_prospective': 141, 'staged_prospective': 145, 'warm_prospective': 144, 'fresh_pending': 1, 'accepted_parents': 139, 'new_source_versions': 2, 'exact_composition_literal_parent_equality': True, 'acceptance_discharge_remaining_interface_metadata_unchanged': True},
    'preparer': newpreppin, 'preserved_parent_preparer': oldpreppin, 'preparer_derivation': derivationpin,
    'whole_preparer_ast': 'Exact parent AST after replacing only FREEZE absolute path, its single asserted hash constant and inert source_repair_derivation dictionary. Core, guard, caps, transport, native checks and allocation enumeration unchanged.',
    'own_preflight_correction': {'path': str(failurep), 'sha256': sha(failurep)},
    'scope': ['Natural original private seed is marginalized under explicit no-read prefix and stored selector support. No fixed-Code fresh Bernoulli mixture.', 'Old may read the entire erased initialized Code and every prefix endpoint, with full outside register and forest retained.', 'All-live-at-h support, original parent alignment, positive arm exposures and long-arm orientation remain explicit. Zero residual is an identity.', 'Actual legal whole-word/context/exit/bin instantiation, calibrated observer and positive biological graph construction remain downstream.'],
    'execution': {'target_modules_imported': 0, 'helpers_or_producers_invoked': 0, 'git_or_external_mutations': 0, 'overlay_writes': 0},
    'qualification': 'Static proposal/preparation source gate only. Prefix a080 is separately authenticated kernel component key54ae; repaired factor and full 141 aggregate/owned audit remain pending. A prepared resource gate must include all actual current roots and any counted Git object relocation before a new mathematical launch.'
}
out = Q / 'FACTOR-3FC-AND-V10-STATIC-QC-ATTEMPT2.json'
with out.open('x') as f:
    json.dump(report, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps({'receipt': str(out), 'sha256': sha(out), 'status': report['status'], 'headers': len(head_rows), 'providers': len(providers)}))
