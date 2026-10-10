"""Independent saved-artifact/Fraction QC. No provider or target imports/runs."""
from pathlib import Path
from fractions import Fraction
import ast
import gzip
import hashlib
import json

ROOT = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
REL = 'rust/evidence/source-fit-selected-reference-20261010T224953.200869Z-REPAIRED-COMPONENT8-APPLICATION4-PASS'
E = ROOT / REL
sha = lambda b: hashlib.sha256(b).hexdigest()
load = lambda p: json.loads(p.read_bytes())
wire = lambda d: json.dumps(d, sort_keys=True, separators=(',', ':'), ensure_ascii=True)
SCIENCE = ('certificate_valid', 'source_admission_verified', 'source_observation_fit_verified',
           'source_provenance_verified', 'timed_readout_verified', 'full_code_evaluated',
           'universal_native_refinement_verified', 'full_solver_verified', 'provider_work_checked',
           'provider_exhaustion_verified', 'source_witness_certified', 'statistical_confidence_verified',
           'unrestricted_exclusion_certified', 'physical_survival_image_verified',
           'observation_law_admission_verified', 'full_joint_calendar_law_verified',
           'complete_source_registry_verified', 'whole_application_lean_verified',
           'parameter_accuracy_released', 'statistical_coverage_verified',
           'resource_exhaustion_verified', 'bank_metadata_independently_checked')
BASELINE = 'eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7'
HELPER = 'ca7f78096a55a962573cdd5490cc9609f9462035f6e7ca864d1eb050ef46dfbb'
NATIVE = '443a1eb6d35154e827b3f0236ab6c5c458752fd6f5480463f390e74a99bd4f00'
INTERPRETER = 'fa67443527ed9647f760d807e2a38f26340757123e643c4639cf273ed15d5ea7'
PACKAGES = {'sympy': ('1.14.0', '4e9476348ba105feab28d82f5bcf6cdba2e3e84de6e059bbfe7a13728c0a4ab0'),
            'mpmath': ('1.3.0', 'b241584d2c1fc0304b0a1015ea923749d7b0800411dd406dcab7c82bf25d9fe8')}

def science_false(d):
    for key in SCIENCE:
        if key in d:
            assert d[key] is False, key

def q(s):
    assert type(s) is str
    n, d = s.split('/')
    n, d = int(n), int(d)
    result = Fraction(n, d)
    assert d > 0 and str(result.numerator) + '/' + str(result.denominator) == s
    return result

def tree_leaves(text):
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            assert node.value >= 0
            return [node.value]
        assert isinstance(node, ast.Tuple) and len(node.elts) == 2
        a, b = map(visit, node.elts)
        assert min(a) < min(b)
        return a + b
    return visit(ast.parse(text, mode='eval').body)

def rows_checked(native, request):
    assert native['status'] == 'TABLE' and native['observer'] == 'ROOTED_UNRANKED_COMPLETE'
    science_false(native); science_false(native['bank_result'])
    xs = [q(v['value']) for v in request['values'][:len(request['context']['edges'])]]
    config = native['configurations']
    assert len(config) == 1 and config[0]['label'] == 'natural' and q(config[0]['weight']) == 1
    assert all(v is None for v in config[0]['forcing'])
    assert wire(config[0]['outcomes']) == wire(native['mixture'])
    labels = sorted(request['context']['global_labels'])
    seen, mass, probability_mass, terms, result = set(), {}, Fraction(0), 0, {}
    for row in native['mixture']:
        assert row['tree'] not in seen
        seen.add(row['tree'])
        assert sorted(tree_leaves(row['tree'])) == labels
        ps = [tuple(p) for p, _ in row['edge_polynomial']]
        assert ps == sorted(set(ps))
        polynomial, evaluation = {}, Fraction(0)
        for powers, text in row['edge_polynomial']:
            assert len(powers) == len(xs) and all(type(p) is int and p >= 0 for p in powers)
            coefficient = q(text); assert coefficient != 0
            powers = tuple(powers); polynomial[powers] = coefficient
            product = coefficient
            for x, power in zip(xs, powers):
                product *= x ** power
            evaluation += product
            mass[powers] = mass.get(powers, Fraction(0)) + coefficient
            if not mass[powers]:
                del mass[powers]
            terms += 1
        probability = q(row['probability'])
        assert 0 < probability <= 1 and probability == evaluation
        probability_mass += probability
        result[row['tree']] = (polynomial, probability)
    assert probability_mass == 1 and mass == {(0,) * len(xs): Fraction(1)}
    return result, terms

def process_bindings(component, directory, reference=True):
    for prefix in ('solver', 'checker') + (('reference-checker',) if reference else ()):
        execution = load(directory / 'component' / (prefix + '.execution.json'))
        assert execution['process_started'] is True and execution['exit_code'] == 0
        for stream in ('stdout', 'stderr'):
            raw = (directory / 'component' / (prefix + '.' + stream)).read_bytes()
            assert sha(raw) == execution[stream + '_sha256']
            assert len(raw) == execution[stream + '_bytes']
    if reference:
        ref = load(directory / 'component/reference-checker.stdout')
        assert wire(ref) == wire(component['reference_check'])
        assert ref['result_valid'] is True and ref['status'] == 'TABLE'
        assert ref['baseline_called'] and ref['request_echo_checked']
        assert ref['baseline_source_sha256'] == BASELINE
        assert ref['request_sha256'] == component['request_sha256']
        assert ref['response_sha256'] == component['native_result_sha256']
        for key in ('independent_all_coefficients_checked', 'independent_probabilities_checked',
                    'supplied_trace_arithmetic_checked'):
            assert component[key] is True and ref[key] is True
        science_false(ref)
        runtime = load(directory / 'component/REFERENCE-RUNTIME.json')
        assert wire(runtime) == wire(component['reference_runtime_observed'])
        assert runtime['backend_called'] is True
        assert runtime['interpreter']['executable_sha256'] == INTERPRETER
        for name, (version, digest) in PACKAGES.items():
            assert runtime['packages'][name]['version'] == version
            assert runtime['packages'][name]['initializer_sha256'] == digest
        for pin in component['reference_source_pins']:
            assert sha((directory / 'component' / pin['staged_path']).read_bytes()) == pin['sha256']
        assert any(p['sha256'] == HELPER for p in component['reference_source_pins'])
        assert component['reference_identity_recheck_stable'] is True
    assert component['native_replay_verified'] is True
    assert component['semantic_request_echo_checked'] is True
    science_false(component)

manifest_raw = (E / 'PRESERVATION-MANIFEST.json').read_bytes()
assert sha(manifest_raw) == 'd1fd08652e8317ea866613c9c36bb588ee779260bab8792264e72318f0af14c7'
manifest = json.loads(manifest_raw)
stored_bytes, restored = 0, 0
for record in manifest['preserved_files']:
    raw = (E / record['path']).read_bytes()
    assert sha(raw) == record['sha256'] and len(raw) == record['bytes']
    if record.get('encoding') == 'gzip':
        original = gzip.decompress(raw)
        assert sha(original) == record['restored_sha256'] and len(original) == record['restored_bytes']
        restored += 1
    stored_bytes += len(raw)
for phase in ('component', 'application'):
    outer = load(E / phase / 'OUTER-RECEIPT.json')
    before = load(E / phase / 'PRE-LAUNCH-PINS.json')
    assert outer['status'] == 'PASS_AUTHORIZED_REFERENCE_PHASE' and outer['exit_code'] == 0
    assert outer['monitor_error'] is None and outer['compiler_invoked'] is False
    assert before == outer['post_pin_rechecks'] == manifest['pinned_source_inventory']
    assert sha((E / phase / 'OUTER-RECEIPT.json').read_bytes()) == manifest['phase_receipts'][phase]['sha256']
assert len(manifest['pinned_source_inventory']) == 33
component_receipt = load(E / 'component/review/RECEIPT.json')
application_receipt = load(E / 'application/review/RECEIPT.json')
assert component_receipt['status'] == application_receipt['status'] == 'PASS'
assert component_receipt['checks'] == 8 and application_receipt['checks'] == 4
successful = ('hybrid-common-sat', 'hybrid-independent-sat', 'hybrid-common-permuted', 'four-copy-fork')
row_count, term_count, tables = 0, 0, {}
for name in successful:
    directory = E / 'component/review' / name / 'component'
    component = load(directory / 'RESULT.json')
    request_raw = (directory / 'REQUEST.json').read_bytes(); request = json.loads(request_raw)
    native_raw = (directory / 'NATIVE-RESULT.json').read_bytes()
    assert component['status'] == 'SUPPLIED_FIT_ROOTED_LAW' and component['exit_code'] == 0
    assert component['request_sha256'] == sha(request_raw)
    assert component['native_result_sha256'] == sha(native_raw)
    assert component['reference_result_sha256'] == sha((directory / 'component/reference-checker.stdout').read_bytes())
    assert component['binary_observed_sha256'] == NATIVE
    process_bindings(component, directory)
    table, terms = rows_checked(json.loads(native_raw), request)
    assert (len(table), terms) == ((15, 22) if name == 'four-copy-fork' else (3, 13 if name == 'hybrid-independent-sat' else 7))
    row_count += len(table); term_count += terms; tables[name] = table
assert (row_count, term_count) == (24, 49)
for name in ('missing-reference', 'failed-reference', 'balanced-source-coefficient-forgery'):
    directory = E / 'component/review' / name / 'component'
    component = load(directory / 'RESULT.json')
    assert component['status'] == 'RESOURCE_OR_EXECUTION_FAILURE' and component['exit_code'] == 1
    science_false(component)
    assert component['rooted_law_evaluated'] is False
    assert component['independent_all_coefficients_checked'] is False
    assert component['independent_probabilities_checked'] is False
    if name == 'missing-reference':
        assert component['solver_called'] is False and component['checker_called'] is False
        assert component['reference_checker_called'] is False
    else:
        assert component['solver_called'] and component['checker_called'] and component['reference_checker_called']
unknown_dir = E / 'component/review/frame-only-unknown/component'
unknown = load(unknown_dir / 'RESULT.json'); ref_unknown = load(unknown_dir / 'component/reference-checker.stdout')
assert unknown['status'] == 'UNKNOWN' and unknown['exit_code'] == 2
assert ref_unknown['result_valid'] is True and ref_unknown['status'] == 'UNKNOWN'
assert unknown['reference_checker_called'] is True and ref_unknown['baseline_called'] is False
assert unknown['reference_runtime_observed']['backend_called'] is False
for key in ('independent_all_coefficients_checked', 'independent_probabilities_checked', 'supplied_trace_arithmetic_checked'):
    assert ref_unknown[key] is False and unknown[key] is False
science_false(unknown); science_false(ref_unknown)
forged_dir = E / 'component/review/balanced-source-coefficient-forgery/component'
forged = load(forged_dir / 'NATIVE-RESULT.json')
request = load(forged_dir / 'REQUEST.json')
forged_table, _ = rows_checked(forged, request)
assert sum(forged_table[t][0] != tables['hybrid-common-sat'][t][0] for t in forged_table) == 2
assert all(forged_table[t][1] == tables['hybrid-common-sat'][t][1] for t in forged_table)
assert load(forged_dir / 'component/reference-checker.stdout')['error'] == 'full rooted whole-edge coefficient table differs from inherited compiler'
assert load(forged_dir / 'component/checker.execution.json')['exit_code'] == 0
application_rows = 0
for name in ('common-reference', 'four-copy-reference', 'missing-reference', 'native-only-default'):
    directory = E / 'application/review' / name / 'application'
    app = load(directory / 'RESULT.json'); child_dir = directory / 'component'; child = load(child_dir / 'RESULT.json')
    assert wire(app['component_result']) == wire(child)
    science_false(app); science_false(child)
    request_raw = (directory / 'REQUEST.json').read_bytes()
    assert app['request_bytes_sha256'] == child['request_sha256'] == sha(request_raw)
    if name == 'missing-reference':
        assert app['status'] == child['status'] == 'RESOURCE_OR_EXECUTION_FAILURE'
        assert child['solver_called'] is False and child['checker_called'] is False
        continue
    assert app['status'] == child['status'] == 'SUPPLIED_FIT_ROOTED_LAW'
    selected = name != 'native-only-default'
    process_bindings(child, child_dir, reference=selected)
    assert app['reference_checker_called'] is selected
    for key in ('independent_all_coefficients_checked', 'independent_probabilities_checked'):
        assert app[key] is selected and child[key] is selected
    if not selected:
        assert child['reference_baseline_called'] is False
    native = load(child_dir / 'NATIVE-RESULT.json')
    table, _ = rows_checked(native, json.loads(request_raw))
    baseline_name = 'four-copy-fork' if name == 'four-copy-reference' else 'hybrid-common-sat'
    assert table == tables[baseline_name]
    application_rows += len(table)

result = {'schema': 'source_fit_reference_live_independent_saved_qc_v1', 'status': 'PASS',
          'evidence_directory': REL, 'preservation_manifest_sha256': sha(manifest_raw),
          'preserved_files': len(manifest['preserved_files']), 'preserved_bytes': stored_bytes,
          'gzip_restorations': restored, 'recorded_pre_post_pins': 33,
          'component_controls': 8, 'component_successful_tables': 4,
          'component_rooted_rows': row_count, 'component_nonzero_edge_terms': term_count,
          'four_copy_rooted_rows': 15, 'four_copy_nonzero_terms': 22,
          'application_controls': 4, 'application_successful_rows_counting_native_only_default': application_rows,
          'balanced_coefficient_forgery_preserves_all_fitted_probabilities_and_mass_but_is_rejected': True,
          'missing_reference_fails_before_native_children': True,
          'unknown_is_frame_only_without_baseline_or_exhaustion_promotion': True,
          'native_only_default_keeps_independent_check_flags_false': True,
          'original_provider_or_native_or_compiler_called_by_reviewer': False,
          'first_cli_failure_and_old_14_acceptance_preserved': True,
          'source_admission_verified': False, 'full_solver_verified': False,
          'qualification': 'Authenticates preserved process/source/runtime/response bindings and independently checks saved Fraction evaluations, shape/label coverage and coefficientwise mass. Original compiler coefficient equality comes from the authenticated recorded original-provider execution; no provider replay or universal runtime/refinement/timed/provenance claim.'}
destination = Path(__file__).with_name('RECEIPT.json')
with destination.open('x') as handle:
    json.dump(result, handle, indent=2, sort_keys=True); handle.write('\n')
print(json.dumps({'status': 'PASS', 'receipt_sha256': sha(destination.read_bytes()),
                  'files': result['preserved_files'], 'rows': row_count, 'terms': term_count}, sort_keys=True))
