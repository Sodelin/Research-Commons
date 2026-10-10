#!/usr/bin/env python3
"""Independent saved-byte and Fraction QC; never import or run target code.

Contributor: Codex / solver_design_recovery, design/QC lane, 2026-10-10.
This reviewer uses standard-library byte/JSON/AST inspection and small exact
saved polynomials. No helper, exporter, fitter, semantic checker, backend,
native adapter, native producer, replay, compiler or Lean process is launched.
"""
import argparse
import ast
from collections import defaultdict
from datetime import datetime, timezone
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path

PACKET = Path(__file__).resolve().parents[3]
REFERENCE = PACKET / 'rust/evidence/source-fit-selected-reference-20261010T224953.200869Z-REPAIRED-COMPONENT8-APPLICATION4-PASS'
TRANSPORT = PACKET / 'rust/evidence/source-fit-fitted-transport-20261010T230001.714430Z-TRANSPORT34-PIPELINE-PASS'
REF_MANIFEST = 'd1fd08652e8317ea866613c9c36bb588ee779260bab8792264e72318f0af14c7'
TRANSPORT_MANIFEST = '32ceb0a880bf2c9c731d233c3b440b0171053156b788003f3c1e1dab7c730e3c'
OLD_HELPER = '0eedff2d9ab21514e3788ae5f9310e33bd57d8ce86e4cf038bb08520ccd99fc6'
NEW_HELPER = 'ca7f78096a55a962573cdd5490cc9609f9462035f6e7ca864d1eb050ef46dfbb'
SCIENCE = ('source_admission_verified', 'source_observation_fit_verified',
    'source_provenance_verified', 'timed_readout_verified', 'full_code_evaluated',
    'universal_native_refinement_verified', 'certificate_valid', 'full_solver_verified')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    return json.loads(path.read_bytes())


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
        allow_nan=False).encode()


def demand(value, description):
    if not value:
        raise AssertionError(description)


def no_science(value):
    for key in SCIENCE:
        if key in value:
            demand(value[key] is False, 'unwarranted science flag: ' + key)


def manifest(root, expected, count, elves, pins):
    path = root / 'PRESERVATION-MANIFEST.json'
    demand(digest(path.read_bytes()) == expected, 'manifest hash changed')
    data = read_json(path)
    demand(len(data['preserved_files']) == count, 'preserved-file count')
    demand(len(data['excluded_ELF_inventory']) == elves, 'retained-ELF count')
    demand(len(data['pinned_source_inventory']) == pins, 'source pin count')
    stored_bytes = restored_bytes = compressed = 0
    for item in data['preserved_files']:
        raw = (root / item['path']).read_bytes()
        demand(len(raw) == item['bytes'] and digest(raw) == item['sha256'],
            'stored file binding: ' + item['path'])
        stored_bytes += len(raw)
        if item.get('encoding') == 'gzip':
            raw = gzip.decompress(raw)
            compressed += 1
            demand(len(raw) == item['restored_bytes'] and
                digest(raw) == item['restored_sha256'], 'gzip restoration binding')
        restored_bytes += len(raw)
        demand(digest(raw) == item['original_sha256'], 'original/restored binding')
        original = Path(item['original_path']).read_bytes()
        demand(original == raw, 'retained scratch bytes changed')
    for item in data['excluded_ELF_inventory']:
        raw = Path(item['path']).read_bytes()
        demand(raw.startswith(b'\x7fELF') and len(raw) == item['bytes'] and
            digest(raw) == item['sha256'], 'retained scratch ELF binding')
    documentation_derivatives = []
    for path, expected_pin in data['pinned_source_inventory'].items():
        observed_pin = digest(Path(path).read_bytes())
        if observed_pin != expected_pin and path.endswith('/applications/practical-solver/README.md'):
            capture = PACKET / 'quality/evidence/application-fitted-transport-docs-before-20261010T2303Z'
            before = read_json(capture / 'BEFORE.json')
            demand(before['sha256'] == expected_pin ==
                '326a03ec6bc1c86ec1c8fd75fd4921725ed4ed98940e5d5ebe059f5013b823c3' and
                digest((capture / 'README.md').read_bytes()) == expected_pin,
                'authenticated before-docs README capture')
            documentation_derivatives.append({'path':path, 'runtime_pinned_sha256':expected_pin,
                'current_docs_sha256':observed_pin, 'authenticated_runtime_capture':str(capture/'README.md'),
                'classification':'Root-owned documentation derivative after these runtime queues completed'})
        else:
            demand(observed_pin == expected_pin, 'current pin: ' + path)
    demand(data['raw_scratch_files_unchanged'] is True and
        data['native_or_compiler_processes_started_by_exporter'] == 0 and
        data['old_native_or_source_bytes_modified_by_exporter'] is False,
        'preservation scope')
    return {'manifest_sha256': expected, 'preserved_files': count,
        'stored_bytes': stored_bytes, 'restored_bytes': restored_bytes,
        'gzip_restorations': compressed, 'retained_fixed_scratch_ELFs': elves,
        'current_or_authenticated_runtime_pins': pins,
        'post_runtime_documentation_derivatives':documentation_derivatives,
        'all_stored_restored_original_bytes_checked': True}


def polynomial(terms, dimension):
    result = defaultdict(Fraction)
    for powers, coefficient in terms:
        demand(len(powers) == dimension and all(type(x) is int and x >= 0 for x in powers),
            'invalid power vector')
        result[tuple(powers)] += Fraction(coefficient)
    return {p: c for p, c in result.items() if c}


def add(a, b, multiplier=Fraction(1)):
    result = defaultdict(Fraction, a)
    for p, c in b.items():
        result[p] += multiplier * c
    return {p: c for p, c in result.items() if c}


def multiply(a, b):
    result = defaultdict(Fraction)
    for pa, ca in a.items():
        for pb, cb in b.items():
            result[tuple(x+y for x, y in zip(pa, pb))] += ca * cb
    return {p: c for p, c in result.items() if c}


def ast_polynomial(expression, variables):
    """Reconstruct the preserved tiny equation, without eval or target imports."""
    zero = (0,) * len(variables)
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return {zero: Fraction(node.value)} if node.value else {}
        if isinstance(node, ast.Name):
            demand(node.id in variables, 'unknown saved equation variable')
            return {tuple(int(i == variables.index(node.id)) for i in range(len(zero))): Fraction(1)}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return {p: -c for p, c in visit(node.operand).items()}
        demand(isinstance(node, ast.BinOp), 'unsupported saved AST')
        if isinstance(node.op, ast.Pow):
            demand(isinstance(node.right, ast.Constant) and type(node.right.value) is int
                and 0 <= node.right.value <= 64, 'saved power bound')
            answer = {zero: Fraction(1)}
            base = visit(node.left)
            for _ in range(node.right.value):
                answer = multiply(answer, base)
            return answer
        left, right = visit(node.left), visit(node.right)
        if isinstance(node.op, ast.Add):
            return add(left, right)
        if isinstance(node.op, ast.Sub):
            return add(left, right, Fraction(-1))
        if isinstance(node.op, ast.Mult):
            return multiply(left, right)
        demand(isinstance(node.op, ast.Div) and set(right) == {zero} and right[zero] != 0,
            'saved division must be constant')
        return {p: c / right[zero] for p, c in left.items()}
    return visit(ast.parse(expression, mode='eval').body)


def evaluate(poly, values):
    total = Fraction(0)
    for powers, coefficient in poly.items():
        value = coefficient
        for q, exponent in zip(values, powers):
            value *= q ** exponent
        total += value
    return total


def equation_polynomial(row, dimension):
    demand(row['dimension'] == dimension, 'equation dimension')
    return polynomial([(t['powers'], t['coefficient']) for t in row['terms']], dimension)


def table_qc(component):
    request_path = component / 'REQUEST.json'
    native_path = component / 'NATIVE-RESULT.json'
    request, native, result = read_json(request_path), read_json(native_path), read_json(component / 'RESULT.json')
    demand(native['status'] == 'TABLE', 'saved TABLE required')
    no_science(native); no_science(result)
    dimension = len(request['context']['edges'])
    values = [Fraction(v['value']) for v in request['values']]
    demand(all(Fraction(0) < v < Fraction(1) for v in values), 'strict supplied bank')
    for row in request['equations']:
        demand(evaluate(equation_polynomial(row, len(values)), values) == 0,
            'supplied rational trace equation')
    one = {(0,) * dimension: Fraction(1)}
    polynomials = {}
    terms = 0
    for row in native['mixture']:
        demand(row['tree'] not in polynomials, 'duplicate rooted outcome')
        poly = polynomial(row['edge_polynomial'], dimension)
        q = Fraction(row['probability'])
        demand(evaluate(poly, values[:dimension]) == q and 0 <= q <= 1,
            'exact polynomial/probability evaluation')
        polynomials[row['tree']] = poly
        terms += len(poly)
    total = {}
    for poly in polynomials.values():
        total = add(total, poly)
    demand(total == one, 'coefficientwise mixture mass')
    demand(sum((Fraction(row['probability']) for row in native['mixture']), Fraction(0)) == 1,
        'exact mixture probability mass')
    mixed = {}
    for configuration in native['configurations']:
        config_total = {}
        for row in configuration['outcomes']:
            poly = polynomial(row['edge_polynomial'], dimension)
            demand(evaluate(poly, values[:dimension]) == Fraction(row['probability']),
                'exact configuration evaluation')
            config_total = add(config_total, poly)
            mixed[row['tree']] = add(mixed.get(row['tree'], {}), poly, Fraction(configuration['weight']))
        demand(config_total == one, 'configuration coefficientwise mass')
    demand(mixed == polynomials, 'configuration/mixture polynomial equality')
    demand(result['request_sha256'] == digest(request_path.read_bytes()) and
        result['native_result_sha256'] == digest(native_path.read_bytes()), 'component raw binding')
    reference_dir = component / 'component'
    ref = read_json(reference_dir / 'REFERENCE-CHECK.json')
    stdout = (reference_dir / 'reference-checker.stdout').read_bytes()
    demand(json.loads(stdout) == ref and result['reference_check'] == ref and
        result['reference_result_sha256'] == digest(stdout), 'reference stdout/result binding')
    demand(ref['request_sha256'] == digest(request_path.read_bytes()) and
        ref['response_sha256'] == digest(native_path.read_bytes()), 'reference request/response binding')
    for key in ('result_valid', 'baseline_called', 'independent_all_coefficients_checked',
            'independent_probabilities_checked', 'supplied_trace_arithmetic_checked'):
        demand(ref[key] is True, 'reference TABLE flag: ' + key)
    no_science(ref)
    demand(ref['rooted_outcomes'] == len(polynomials) and ref['whole_edge_terms'] == terms,
        'reference table counts')
    for name in ('solver', 'checker', 'reference-checker'):
        execution = read_json(reference_dir / (name + '.execution.json'))
        demand(execution['process_started'] is True and execution['exit_code'] == 0
            and execution['timed_out'] is False, 'saved execution success: ' + name)
        for stream in ('stdout', 'stderr'):
            raw = (reference_dir / (name + '.' + stream)).read_bytes()
            demand(len(raw) == execution[stream + '_bytes'] and
                digest(raw) == execution[stream + '_sha256'], 'saved process stream binding')
        demand(execution['address_space_bytes'] == 536870912 and execution['cpu_limit_seconds'] == 30
            and execution['wall_timeout_seconds'] == 45 and execution['per_file_bytes'] == 16777216,
            'saved bounded child contract')
    return {'native_sha256': digest(native_path.read_bytes()), 'reference_stdout_sha256': digest(stdout),
        'rows': len(polynomials), 'terms': terms, 'supplied_equations': len(request['equations']),
        'exact_Fraction_evaluation': True, 'coefficientwise_mass': True,
        'configuration_mixture_equality': True, 'actual_saved_process_binding': True}


def path_only_repair():
    old = (PACKET / 'design/source_fit_reference.py').read_bytes()
    new = (PACKET / 'design/source_fit_reference_v2.py').read_bytes()
    demand(digest(old) == OLD_HELPER and digest(new) == NEW_HELPER, 'helper source pins')
    expected = old.replace(b'parser.add_argument("--request", required=True)',
        b'parser.add_argument("--request", type=Path, required=True)').replace(
        b'parser.add_argument("--certificate", required=True)',
        b'parser.add_argument("--certificate", type=Path, required=True)')
    demand(new == expected, 'only two CLI Path conversion lines changed')
    before, after = ast.parse(old), ast.parse(new)
    retained_before = [ast.dump(x, include_attributes=False) for x in before.body
        if isinstance(x, (ast.FunctionDef, ast.ClassDef)) and x.name != 'main']
    retained_after = [ast.dump(x, include_attributes=False) for x in after.body
        if isinstance(x, (ast.FunctionDef, ast.ClassDef)) and x.name != 'main']
    demand(retained_before == retained_after and len(retained_before) == 29,
        'unchanged non-main function/class ASTs')
    return {'original_helper_sha256': OLD_HELPER, 'v2_helper_sha256': NEW_HELPER,
        'only_two_Path_CLI_lines_changed': True, 'unchanged_non_main_function_class_ASTs': 29}


def reference_qc():
    summary = manifest(REFERENCE, REF_MANIFEST, 322, 9, 33)
    summary['path_only_repair'] = path_only_repair()
    component = read_json(REFERENCE / 'component/review/RECEIPT.json')
    application = read_json(REFERENCE / 'application/review/RECEIPT.json')
    demand(component['status'] == application['status'] == 'PASS' and
        component['checks'] == 8 and application['checks'] == 4, 'saved 8+4 review receipts')
    demand(all(x['pass_'] for x in component['tests']) and all(x['pass'] for x in application['tests']),
        'all focused controls passed')
    tables = []
    for name, rows, terms in [('hybrid-common-sat', 3, 7), ('hybrid-independent-sat', 3, 13),
        ('hybrid-common-permuted', 3, 7), ('four-copy-fork', 15, 22)]:
        saved = table_qc(REFERENCE / 'component/review' / name / 'component')
        demand((saved['rows'], saved['terms']) == (rows, terms), 'expected finite table size')
        tables.append({'fixture': name, **saved})
    controls = {}
    for name in ('missing-reference', 'failed-reference', 'frame-only-unknown', 'balanced-source-coefficient-forgery'):
        folder = REFERENCE / 'component/review' / name / 'component'
        result = read_json(folder / 'RESULT.json')
        no_science(result)
        for flag in ('independent_all_coefficients_checked', 'independent_probabilities_checked'):
            demand(result[flag] is False, 'refusal/frame-only independent flags')
        if name == 'missing-reference':
            demand(result['exit_code'] == 1 and result['solver_called'] is False and
                result['checker_called'] is False and result['reference_checker_called'] is False,
                'missing reference must stop before native launch')
        elif name == 'frame-only-unknown':
            demand(result['exit_code'] == 2 and result['status'] == 'UNKNOWN' and
                result['reference_frame_checked'] is True and result['reference_baseline_called'] is False,
                'UNKNOWN must remain frame-only')
            runtime = read_json(folder / 'component/REFERENCE-RUNTIME.json')
            demand(runtime['backend_called'] is False and runtime['packages'] == {}, 'lazy backend')
        else:
            demand(result['exit_code'] == 1 and result['native_status'] == 'TABLE' and
                result['solver_called'] is True and result['checker_called'] is True and
                result['reference_checker_called'] is True, 'post-native reference refusal')
        if name == 'balanced-source-coefficient-forgery':
            native = read_json(folder / 'NATIVE-RESULT.json')
            real = read_json(REFERENCE / 'component/review/hybrid-common-sat/component/NATIVE-RESULT.json')
            demand([(x['tree'], x['probability']) for x in native['mixture']] ==
                [(x['tree'], x['probability']) for x in real['mixture']], 'balanced forgery preserves probabilities')
            demand(native['mixture'] != real['mixture'], 'forgery actually changed coefficients')
            forged_total = {}
            for x in native['mixture']:
                forged_total = add(forged_total, polynomial(x['edge_polynomial'], 5))
            demand(forged_total == {(0,)*5: Fraction(1)}, 'balanced forgery preserves polynomial mass')
            refused = read_json(folder / 'component/reference-checker.stdout')
            demand(refused['result_valid'] is False and 'coefficient table differs' in refused['error'],
                'independent forgery refusal reason')
        controls[name] = {'status': result['status'], 'exit_code': result['exit_code'], 'saved_scope_checked': True}
    applications = []
    for name in ('common-reference', 'four-copy-reference', 'missing-reference', 'native-only-default'):
        folder = REFERENCE / 'application/review' / name / 'application'
        result = read_json(folder / 'RESULT.json')
        child = read_json(folder / 'component/RESULT.json')
        demand(result['component_result'] == child, 'application/child semantic binding')
        no_science(result); no_science(child)
        selected = name.endswith('-reference') and name != 'missing-reference'
        demand(result['independent_all_coefficients_checked'] is selected and
            result['independent_probabilities_checked'] is selected and
            result['reference_checker_called'] is selected, 'application selection flags')
        if selected:
            table_qc(folder / 'component')
        else:
            demand(result['status'] == ('RESOURCE_OR_EXECUTION_FAILURE' if name == 'missing-reference'
                else 'SUPPLIED_FIT_ROOTED_LAW'), 'application default/failure status')
        applications.append({'fixture': name, 'status': result['status'], 'selected_reference_accepted': selected})
    summary.update(tables=tables, component_controls=controls, application_controls=applications,
        rooted_rows=24, whole_edge_terms=49, component_review_sha256=digest((REFERENCE/'component/review/RECEIPT.json').read_bytes()),
        application_review_sha256=digest((REFERENCE/'application/review/RECEIPT.json').read_bytes()),
        first_actual_CLI_failure_preserved=(PACKET/'rust/evidence/source-fit-selected-reference-20261010T224426.421439Z-FIRST-COMPONENT8-REFERENCE-CLI-FAILURE').is_dir(),
        status='PASS_INDEPENDENT_SAVED_REFERENCE_DESIGN_QC')
    return summary


def transported_case(folder, name, source_name=None):
    request_path, origin_path = folder/(name+'.request.json'), folder/(name+'.origin.json')
    request, origin = read_json(request_path), read_json(origin_path)
    source = read_json(folder / ((source_name or name) + ('.BACKEND-RESULT.json' if source_name is None else '.input.json')))
    source_path = folder / ((source_name or name) + ('.BACKEND-RESULT.json' if source_name is None else '.input.json'))
    raw = source_path.read_bytes()
    selected = source['entries'][source['witness_entry']]
    demand(origin['raw_backend_sha256'] == digest(raw) and origin['raw_backend_bytes'] == len(raw), 'raw origin hash')
    demand(origin['native_request_sha256'] == digest(request_path.read_bytes()), 'transport request hash')
    demand(origin['original_request'] == source['request'] and origin['selected_entry'] == selected,
        'lossless full original request and selected entry')
    demand(origin['selected_row'] == source['request']['rows'][origin['selected_panel_row_index']], 'explicit panel selection')
    demand(digest(compact(source['request'])) == source['request_sha256'] and
        digest(compact(selected['equations'])) == selected['equation_sha256'], 'inherited canonical digests')
    demand(origin['original_request_sha256'] == source['request_sha256'] and
        origin['original_equation_sha256'] == selected['equation_sha256'], 'origin digest labels')
    demand(len(request['equations']) == len(selected['equations']) == origin['supplied_equations'],
        'panel selection must preserve every supplied equation')
    demand(origin['original_observation_rows'] == len(source['request']['rows']) and
        origin['all_original_rows_retained'] is True and origin['all_supplied_equations_retained'] is True,
        'all original rows/actions retained')
    no_science(origin)
    for flag in ('source_equation_provenance_verified', 'selected_experiment_reproduced', 'fitter_called',
        'semantic_source_checker_called', 'native_solver_called', 'provider_work_checked', 'provider_exhaustion_verified'):
        demand(origin[flag] is False, 'transport scope flag: '+flag)
    names = request['vertex_names']
    edges = selected['graph']['edges']
    demand(request['context']['edges'] == [[names.index(p), names.index(c)] for p,c in edges], 'original edge occurrences/order')
    public_taxa = source['request'].get('taxa', ['L'+str(i) for i in range(source['request']['n'])])
    demand(request['taxon_labels'] == public_taxa and request['context']['leaves'] ==
        [names.index('L'+str(i)) for i in range(len(public_taxa))], 'public taxa[i]/original L_i map')
    for i, taxon in enumerate(public_taxa):
        demand(origin['taxon_bijection'][i] == {'taxon_id':i, 'public_taxon':taxon,
            'internal_vertex':'L'+str(i), 'native_vertex':names.index('L'+str(i))}, 'taxon map record')
    row = origin['selected_row']
    copies, taxa_ids = [], []
    for i, taxon in enumerate(public_taxa):
        labels = row.get('samples', {x:[x] for x in public_taxa}).get(taxon, [])
        copies += labels; taxa_ids += [i]*len(labels)
    demand(request['copy_labels'] == copies and request['context']['local_samples'] == taxa_ids, 'selected-copy bijection')
    demand(origin['copy_bijection'] == [dict(local_copy=i,original_copy_label=c,
        taxon_id=taxa_ids[i],global_id=request['context']['global_labels'][i]) for i,c in enumerate(copies)], 'numeric global IDs retained')
    physical = selected['physical_realization']
    demand(origin['original_edge_order'] == physical['original_edges'], 'physical occurrences preserved')
    for i,(p,c) in enumerate(edges):
        r=physical['original_edges'][i]
        demand(r['original_edge_id'] == i and (r['parent'],r['child']) == (p,c) and
            r['duration'] == physical['original_vertex_ages'][p]-physical['original_vertex_ages'][c] > 0 and
            r['survival_parameter'] == 'x'+str(i) and r['survival_value'] == selected['values']['x'+str(i)] and
            r['positive_rate_definition'] == '-log(survival_value)/duration', 'saved strict calendar/rate metadata')
    for i,h in enumerate(origin['hybrid_bijection']):
        internal=h['internal_vertex']; occurrences=[j for j,e in enumerate(edges) if e[1] == internal]
        demand(h['incoming_occurrences'] == occurrences and h['old_gamma_parent'] == 0 and
            h['native_gamma_conversion'] == '1-old_gamma' and h['old_gamma_variable'] == 'g_'+internal and
            request['context']['hybrids'][i] == [names.index(internal), *occurrences], 'original gamma orientation')
    rational = all(v['kind']=='RATIONAL' for v in request['values'])
    variables=request['variables']
    for expression, dto in zip(selected['equations'],request['equations']):
        demand(ast_polynomial(expression,variables) == equation_polynomial(dto,len(variables)), 'exact AST-to-DTO polynomial equality')
    if rational:
        values=[Fraction(v['value']) for v in request['values']]
        demand(all(0<v<1 for v in values), 'strict rational bank')
        for var,value in zip(variables,values):
            demand(value == Fraction(selected['values'][var]['value']), 'old bank value retained')
        for dto in request['equations']:
            demand(evaluate(equation_polynomial(dto,len(variables)),values) == 0, 'all saved trace equations evaluate to zero')
        demand(origin['supplied_trace_arithmetic_checked'] is True, 'rational trace flag')
    else:
        demand(origin['supplied_trace_arithmetic_checked'] is False and origin['native_evaluation_supported'] is False and
            origin['native_evaluation_scope']=='UNSUPPORTED_ALGEBRAIC_EVALUATION', 'algebraic evaluation stays unsupported')
        for var,value in zip(variables,request['values']):
            if value['kind']=='ALGEBRAIC':
                old=selected['values'][var]
                demand(value['real_root_index']==old['real_root_index'] and
                    [Fraction(c) for c in value['polynomial_ascending']]==[Fraction(c) for c in old['polynomial_ascending']], 'exact algebraic descriptor retained')
    forced=bool(row.get('forced',{}))
    randomized='program' in row
    other=row.get('readout','rooted')!='rooted'
    demand(origin['selected_row_relation']==('COUNTERFACTUAL_NATURAL_ROOTED_OBSERVER' if forced or randomized or other
        else 'NATURAL_ROOTED_OBSERVER_REQUESTED_NOT_REVERIFIED'), 'natural reader/counterfactual relation')
    demand(origin['requested_observer']=='NATURAL_ROOTED_UNRANKED_COMPLETE', 'natural reader requested')
    return {'fixture':name,'raw_backend_sha256':digest(raw),'native_request_sha256':digest(request_path.read_bytes()),
        'original_rows':len(source['request']['rows']),'supplied_equations':len(request['equations']),
        'exact_AST_polynomials_equal':True, 'exact_shared_trace_evaluated':rational,
        'relation':origin['selected_row_relation'],'all_rows_actions_edges_and_maps_preserved':True}


def transport_qc():
    summary=manifest(TRANSPORT,TRANSPORT_MANIFEST,95,1,50)
    folder=TRANSPORT/'transport/review'
    review=read_json(folder/'RECEIPT.json')
    demand(review['status']=='PASS' and review['checks_passed']==len(review['checks'])==34 and
        all(x['pass'] for x in review['checks']), 'actual focused transport controls')
    demand(review['compiler_processes_started']==review['fitter_processes_started']==
        review['semantic_source_checker_processes_started']==0, 'transport target scope')
    no_science(review)
    cases=[transported_case(folder,x) for x in ('hybrid-common-sat','hybrid-independent-sat')]
    for name in ('forced_panel_counterfactual','randomized_panel_counterfactual',
        'public_taxa_reversed_graph_leaf_list','finite_seconds_metadata',
        'duplicate_zero_equations_preserved','exact_rootof_preserved_unsupported'):
        cases.append(transported_case(folder,name,name))
    for item in review['checks']:
        path=folder/(item['name']+'.input.json')
        if path.exists() and 'raw_sha256' in item:
            demand(digest(path.read_bytes())==item['raw_sha256'], 'saved control raw hash')
        if item.get('status')=='UNKNOWN':
            demand(item['code']=='TRANSPORT_RESOURCE_LIMIT' and item['limit']['required']>item['limit']['cap'],
                'bounded UNKNOWN does not claim exclusion')
    exported=folder/'exported-cli'
    demand((exported/'SOURCE-FIT-REQUEST.json').read_bytes()==(folder/'hybrid-common-sat.request.json').read_bytes() and
        (exported/'BACKEND-RESULT.json').read_bytes()==(folder/'hybrid-common-sat.BACKEND-RESULT.json').read_bytes(), 'CLI lossless export')
    cli=read_json(exported/'RESULT.json'); demand(cli['status']=='EXPORTED' and cli['exit_code']==0,'saved CLI success')
    pipeline=table_qc(folder/'application/component')
    demand(pipeline['native_sha256']=='3f21282fe0bdc8ecba4e8d4b4779ce3dfc3677bf4bccf904ff367c760b966039' and
        pipeline['rows']==3 and pipeline['terms']==7 and pipeline['supplied_equations']==12,'same saved COMMON table/full trace')
    application=read_json(folder/'application/RESULT.json')
    no_science(application)
    demand(application['status']=='SUPPLIED_FIT_ROOTED_LAW' and application['independent_all_coefficients_checked'] is True
        and application['independent_probabilities_checked'] is True,'actual application selected reference')
    summary.update(status='PASS_INDEPENDENT_SAVED_TRANSPORT_DESIGN_QC', controls=34,
        transport_review_sha256=digest((folder/'RECEIPT.json').read_bytes()), saved_transport_cases=cases,
        saved_pipeline=pipeline, source_sha256=digest((PACKET/'rust/fitted_source_request.py').read_bytes()),
        harness_sha256=digest((PACKET/'rust/review_fitted_source_request.py').read_bytes()),
        science_scope='Lossless supplied-witness representation, small exact saved AST/trace arithmetic and one natural rooted pipeline; no source admission, equation provenance, observation fit or selected-experiment reproduction.')
    return summary


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--mode',choices=('reference','transport'),required=True)
    parser.add_argument('--receipt',type=Path,required=True)
    args=parser.parse_args()
    base={'schema':'source_fit_independent_saved_design_qc_v1','contributor':'Codex / solver_design_recovery',
        'observed_utc':datetime.now(timezone.utc).isoformat(), 'reviewer_sha256':digest(Path(__file__).read_bytes()),
        'mode':args.mode, 'reviewer_target_processes_started':0, 'reviewer_compiler_processes_started':0,
        'reviewer_helper_exporter_backend_processes_started':0, 'Lean_acceptance_modified':False,
        'universal_native_refinement_verified':False,'source_admission_verified':False,
        'source_equation_provenance_verified':False,'source_observation_fit_verified':False,
        'selected_experiment_reproduced':False,'timed_readout_verified':False,'full_solver_verified':False}
    try:
        base.update(reference_qc() if args.mode=='reference' else transport_qc())
    except Exception as error:
        base.update(status='FAIL_SAVED_REVIEW',error_type=type(error).__name__,error=str(error))
    with args.receipt.open('x') as handle:
        json.dump(base,handle,sort_keys=True,indent=2);handle.write('\n')
    print(json.dumps({'status':base['status'],'receipt':str(args.receipt),'receipt_sha256':digest(args.receipt.read_bytes())}))
    return 1 if base['status']=='FAIL_SAVED_REVIEW' else 0


if __name__=='__main__':
    raise SystemExit(main())
