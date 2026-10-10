"""Capture saved fit witnesses; no target imports, solver or compiler execution.

Fraction checks authenticate supplied scalar/equation/physical fields only.
They do not establish source admission or compiled Rust behavior.
"""
from __future__ import annotations
import ast
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path('/workspace/Research-Commons')
PACKET = ROOT / 'research/2026-10-10-codex-lean-rust-parity'
HERE = Path(__file__).resolve().parent
FIXTURES = PACKET / 'rust/fixtures/source-fit'
OLD = ROOT / 'research/2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as handle:
        handle.write(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True) + '\n')


def rational(value):
    value = Fraction(value)
    return f'{value.numerator}/{value.denominator}'


def sparse(expression, variables):
    dimension = len(variables)
    zeros = (0,) * dimension
    tree = ast.parse(expression, mode='eval')
    assert sum(1 for _ in ast.walk(tree)) <= 4096

    def add(a, b, sign=1):
        result = dict(a)
        for powers, coefficient in b.items():
            result[powers] = result.get(powers, Fraction(0)) + sign * coefficient
        return {p: c for p, c in result.items() if c}

    def multiply(a, b):
        assert len(a) * len(b) <= 65536
        result = {}
        for x, cx in a.items():
            for y, cy in b.items():
                powers = tuple(i + j for i, j in zip(x, y))
                assert max(powers, default=0) <= 64
                result[powers] = result.get(powers, Fraction(0)) + cx * cy
        return {p: c for p, c in result.items() if c}

    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return {} if node.value == 0 else {zeros: Fraction(node.value)}
        if isinstance(node, ast.Name) and node.id in variables:
            powers = list(zeros)
            powers[variables.index(node.id)] = 1
            return {tuple(powers): Fraction(1)}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return {p: -c for p, c in visit(node.operand).items()}
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                assert isinstance(node.right, ast.Constant) and type(node.right.value) is int
                assert 0 <= node.right.value <= 64
                base, result = visit(node.left), {zeros: Fraction(1)}
                for _ in range(node.right.value):
                    result = multiply(result, base)
                return result
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add):
                return add(a, b)
            if isinstance(node.op, ast.Sub):
                return add(a, b, -1)
            if isinstance(node.op, ast.Mult):
                return multiply(a, b)
            if isinstance(node.op, ast.Div):
                assert set(b) == {zeros} and b[zeros]
                return {p: c / b[zeros] for p, c in a.items()}
        raise ValueError('unsupported saved polynomial AST')

    return visit(tree.body)


def evaluate(polynomial, assignment):
    return sum((coefficient * product(value ** power for value, power in zip(assignment, powers))
                for powers, coefficient in polynomial.items()), Fraction(0))


def product(values):
    result = Fraction(1)
    for value in values:
        result *= value
    return result


def mapped_tree(tree, labels):
    if isinstance(tree, str):
        return str(labels[tree]), labels[tree]
    left, first = mapped_tree(tree[0], labels)
    right, second = mapped_tree(tree[1], labels)
    if first > second:
        left, right, first, second = right, left, second, first
    return f'({left},{right})', first


def capture(name):
    path = OLD / 'runs' / name / 'RESULT.json'
    saved = json.loads(path.read_bytes())
    entry_index = saved['witness_entry']
    entry = saved['entries'][entry_index]
    assert entry['status'] == 'SAT_INDEPENDENT_EXACT_WITNESS'
    graph, original = entry['graph'], saved['request']
    names = []
    for parent, child in graph['edges']:
        for vertex in (parent, child):
            if vertex not in names:
                names.append(vertex)
    incoming = {name: [i for i, (_, child) in enumerate(graph['edges']) if child == name] for name in names}
    hybrids = sorted(name for name in names if len(incoming[name]) == 2)
    variables = [f'x{i}' for i in range(len(graph['edges']))] + [f'g_{h}' for h in hybrids]
    assert set(variables) == set(entry['values'])
    assignment = []
    for variable in variables:
        encoded = entry['values'][variable]
        assert encoded['kind'] == 'rational'
        value = Fraction(encoded['value'])
        assert 0 < value < 1
        assignment.append(value)
    equations = [sparse(expression, variables) for expression in entry['equations']]
    assert all(evaluate(poly, assignment) == 0 for poly in equations)
    taxa = original.get('taxa', [f'L{i}' for i in range(original['n'])])
    first_row = original['rows'][0]
    samples = first_row.get('samples', {taxon: [taxon] for taxon in taxa})
    copy_labels, sample = [], []
    for taxon_id, taxon in enumerate(taxa):
        for label in samples.get(taxon, []):
            sample.append(taxon_id)
            copy_labels.append(label)
    assert len(copy_labels) <= 4 and len(set(copy_labels)) == len(copy_labels)
    request = {
        'schema': 'source_fit_request_v1',
        'context': {'vertices': len(names), 'root': names.index(graph['root']),
                    'edges': [[names.index(p), names.index(c)] for p, c in graph['edges']],
                    'leaves': [names.index(leaf) for leaf in graph['leaves']],
                    'hybrids': [[names.index(h), *incoming[h]] for h in hybrids],
                    'local_samples': sample, 'global_labels': list(range(len(sample)))},
        'vertex_names': names, 'taxon_labels': taxa,
        'hybrid_labels': [original['registry']['hybrid_ids'][int(h[1:])] for h in hybrids],
        'copy_labels': copy_labels, 'variables': variables,
        'values': [{'kind': 'RATIONAL', 'value': rational(value)} for value in assignment],
        'equations': [{'dimension': len(variables), 'terms': [
            {'powers': list(powers), 'coefficient': rational(coefficient)}
            for powers, coefficient in sorted(poly.items())]} for poly in equations],
        'mechanism': entry['mechanism'].upper(), 'terminal': 'ANCESTRAL_COMPLETE',
        'compiler_limits': {'word_length': 32, 'slots': 16, 'variables': 256},
        'limits': {'equations': 4096, 'terms': 65536, 'arithmetic_steps': 1000000,
                   'rational_bits': 4096, 'power_exponent': 4096}}
    physical = entry['physical_realization']
    ages = physical['original_vertex_ages']
    for vertex in names:
        children = [c for p, c in graph['edges'] if p == vertex]
        assert ages[vertex] == (0 if vertex in graph['leaves'] else 1 + max(ages[c] for c in children))
    expected_edges = []
    dates = sorted(set(ages.values()))
    for edge_id, (parent, child) in enumerate(graph['edges']):
        duration = ages[parent] - ages[child]
        assert duration > 0
        recorded = physical['original_edges'][edge_id]
        assert recorded['original_edge_id'] == edge_id and recorded['parent'] == parent and recorded['child'] == child
        assert recorded['duration'] == duration and recorded['survival_value'] == entry['values'][f'x{edge_id}']
        active = [(i, Fraction(b - a, duration)) for i, (a, b) in enumerate(zip(dates, dates[1:]))
                  if ages[child] <= a < b <= ages[parent]]
        assert sum((exponent for _, exponent in active), Fraction(0)) == 1
        expected_edges.append({'original_edge': edge_id, 'duration': rational(duration),
                               'survival': rational(assignment[edge_id]),
                               'active_slots': [[slot, rational(exponent)] for slot, exponent in active]})
    labels = {label: i for i, label in enumerate(copy_labels)}
    expected = {'schema': 'saved_source_fit_expected_rooted_law_v1', 'fixture': name,
                'old_result_sha256': sha(path), 'entry': entry_index,
                'observer': 'ROOTED_UNRANKED_COMPLETE',
                'source_admission_claim': False, 'rust_executed': False,
                'old_declared_law': first_row['law'],
                'expected_global_rows': sorted([{'tree': mapped_tree(row['outcome'], labels)[0],
                                                 'probability': rational(row['p'])}
                                                for row in first_row['law']], key=lambda row: row['tree']),
                'expected_ages': [rational(ages[name]) for name in names],
                'expected_edges': expected_edges,
                'expected_original_gamma': [rational(1 - assignment[len(graph['edges']) + i]) for i in range(len(hybrids))],
                'all_supplied_equations_fraction_checked': len(equations)}
    write(FIXTURES / f'{name}.request.json', request)
    write(FIXTURES / f'{name}.expected.json', expected)
    # Preserve every original observed row/mixture, not just natural outputs.
    write(HERE / f'{name}.origin.json', {'path': str(path), 'sha256': sha(path),
          'entry_index': entry_index, 'request': original, 'entry': entry})
    return request, expected, equations, assignment, path


def main():
    assert sha(OLD / 'solver.py') == '42e4353d3033e807e26bc409c724fcdee2a01552a630c9364f428f92f9ffe0db'
    assert sha(ROOT / 'research/2026-10-01-g7-continuous-design/law_compiler.py') == 'eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7'
    controls = []
    common, expected, equations, assignment, path = capture('hybrid-common-sat')
    capture('hybrid-independent-sat')
    controls.append({'name': 'all_twelve_shared_COMMON_equations', 'pass': len(equations) == 12})
    wrong = dict(equations[0]); zero = (0,) * len(assignment)
    wrong[zero] -= Fraction(1,135)
    controls.append({'name': 'changed_exact_row_rejects', 'pass': evaluate(wrong, assignment) == -Fraction(1,135)})
    swapped = list(assignment); swapped[1], swapped[2] = swapped[2], swapped[1]
    controls.append({'name': 'original_edge_survivals_not_interchangeable', 'pass': evaluate(equations[0],swapped) != 0})
    controls.append({'name': 'original_gamma_complement', 'pass': expected['expected_original_gamma'] == ['2/3']})
    p0, p1 = Fraction(1,9), Fraction(2,15)
    correct, wrong_alias = Fraction(1,3)*p0+Fraction(2,3)*p1, Fraction(2,3)*p0+Fraction(1,3)*p1
    controls.append({'name': 'wrong_direct_gamma_alias_changes_observable',
                     'pass': correct == Fraction(17,135) and wrong_alias == Fraction(16,135)})
    controls.append({'name': 'randomized_label_forgotten_mixture_exact',
                     'pass': Fraction(1,4)*p0+Fraction(3,4)*p1 == Fraction(23,180)})
    permuted = json.loads(json.dumps(common))
    permuted['context']['global_labels'] = [9007199254740993,0,17]
    write(FIXTURES / 'hybrid-common-permuted.request.json',permuted)
    expected_permuted = {**expected, 'fixture': 'hybrid-common-permuted',
        'expected_global_rows': sorted([{'tree': mapped_tree(row['outcome'],dict(zip(common['copy_labels'],permuted['context']['global_labels'])))[0],
                                        'probability': rational(row['p'])} for row in expected['old_declared_law']],key=lambda row:row['tree'])}
    write(FIXTURES / 'hybrid-common-permuted.expected.json',expected_permuted)
    controls.append({'name': 'permuted_large_embedding_is_not_local_index',
                     'pass': any('9007199254740993' in row['tree'] for row in expected_permuted['expected_global_rows'])})
    assert all(control['pass'] for control in controls)
    sources = [PACKET/'rust/src/source_fit_bank.rs',PACKET/'rust/notes/SOURCE-FIT-BANK-BRIDGE-20261010T2154Z.md',
               Path(__file__), OLD/'solver.py', OLD/'verify_certificate.py',
               ROOT/'research/2026-10-01-g7-continuous-design/law_compiler.py']
    write(HERE/'SOURCE-FREEZE.json',{'schema':'source_fit_bank_source_freeze_v1','sources':[
        {'path':str(source),'sha256':sha(source),'bytes':source.stat().st_size} for source in sources]})
    (HERE/'source_fit_bank.rs').write_bytes((PACKET/'rust/src/source_fit_bank.rs').read_bytes())
    outputs = sorted([*FIXTURES.glob('*.json'),*HERE.glob('*.origin.json'),HERE/'SOURCE-FREEZE.json',HERE/'source_fit_bank.rs'])
    write(HERE/'RECEIPT.json',{'schema':'source_fit_bank_saved_reference_capture_v1',
          'status':'PASS_REFERENCE_CAPTURE_ONLY','controls':controls,
          'rust_builds':0,'native_solver_processes':0,'old_compiler_processes':0,'lean_processes':0,
          'compiled_rust_claim':False,'source_observation_fit_verified':False,'source_admission_verified':False,
          'outputs':[{'path':str(output),'sha256':sha(output),'bytes':output.stat().st_size} for output in outputs]})
    print(json.dumps({'status':'PASS_REFERENCE_CAPTURE_ONLY','controls':len(controls),'outputs':len(outputs),'receipt_sha256':sha(HERE/'RECEIPT.json')}))


if __name__ == '__main__':
    main()
