"""Exact coupled law feasibility on a COMPLETE finite original-ID registry.

No unknown-size terminal-NO claim. SMT verdicts and independently checked
witness/linear-contradiction certificates have distinct verification labels.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time, signal, platform
from fractions import Fraction
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'upstream'))
import sympy as sp
import z3
from law_compiler import Network, compile_law, forest, unrooted_law, split_signature
from source_census import census, admitted, displayed, canonical_key

class InvalidInput(ValueError):
    pass

class Unsupported(ValueError):
    pass

class TimeLimit(Exception):
    pass

def canonical_json(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode()

def digest(x):
    return hashlib.sha256(canonical_json(x)).hexdigest()

def rational(x):
    if type(x) is int:
        return sp.Rational(x)
    if not isinstance(x, str):
        raise InvalidInput('Probability values must use exact integer or rational strings, never floating estimates.')
    try:
        q = Fraction(x)
    except (ValueError, ZeroDivisionError):
        raise InvalidInput('Invalid exact rational: ' + repr(x))
    return sp.Rational(q.numerator, q.denominator)

def qtext(x):
    return str(sp.Rational(x))

def tree(x, labels):
    if isinstance(x, str):
        if x not in labels:
            raise InvalidInput('Unknown sampled copy label ' + x)
        return x
    if not isinstance(x, list) or len(x) != 2:
        raise InvalidInput('A rooted outcome is a leaf label or a binary two-child list.')
    return forest((tree(x[0], labels), tree(x[1], labels)))

def tree_labels(t):
    return [t] if isinstance(t, str) else sum((tree_labels(v) for v in t), [])

def json_tree(t):
    return t if isinstance(t, str) else [json_tree(v) for v in t]

def prune(t, keep):
    if isinstance(t, str):
        return t if t in keep else None
    a, b = (prune(v, keep) for v in t)
    return b if a is None else a if b is None else forest((a, b))

def readout_law(rooted, kind, panels):
    if kind == 'rooted':
        return rooted
    if kind == 'unrooted_splits':
        return unrooted_law(rooted)
    if kind != 'joint_quartets':
        raise Unsupported('Supported exact readouts are rooted, unrooted_splits, joint_quartets; DNA/calendar readers require separate source/channel admission.')
    out = {}
    for t, p in rooted.items():
        event = tuple((split_signature(prune(t, set(keep))) for keep in panels))
        out[event] = sp.expand(out.get(event, 0) + p)
    return out

def split_event(x, labels):
    if not isinstance(x, list):
        raise InvalidInput('Split outcome must be a list of unordered two-side splits.')
    out = []
    for cut in x:
        if not isinstance(cut, list) or len(cut) != 2:
            raise InvalidInput('Malformed split.')
        if any(not isinstance(side, list) or any(not isinstance(label, str) for label in side) for side in cut):
            raise InvalidInput('Each split side must be a finite list of copy-label strings.')
        a, b = map(tuple, (sorted(cut[0]), sorted(cut[1])))
        if len(a) < 2 or len(b) < 2 or len(set(a)) != len(a) or (len(set(b)) != len(b)) or set(a) & set(b) or (set(a) | set(b) != set(labels)):
            raise InvalidInput('A nontrivial split must partition every sampled label.')
        out.append(tuple(sorted((a, b))))
    if len(set(out)) != len(out):
        raise InvalidInput('Duplicate split.')
    return tuple(sorted(out))

def prepare_request(request):
    if not isinstance(request, dict):
        raise InvalidInput('The request must be a JSON object.')
    unknown = set(request) - {'observation_kind', 'clock_contract', 'n', 'registry', 'mechanisms', 'taxa', 'task', 'target_kind', 'limits', 'rows', 'empirical_admission'}
    if unknown:
        raise Unsupported('Unsupported request fields must receive an actual encoder: ' + ', '.join(sorted(unknown)))
    if request.get('task', 'find_source') not in ('find_source', 'identify_target'):
        raise Unsupported('Supported tasks are find_source and identify_target on the declared complete finite registry.')
    if request.get('target_kind', 'nontrivial_displayed_split_union') not in ('nontrivial_displayed_split_union', 'whole_switching_split_systems'):
        raise Unsupported('Target must be an actual nontrivial split union or whole switching cut-system family.')
    limits = request.get('limits', {})
    if not isinstance(limits, dict):
        raise InvalidInput('Limits must be a JSON object.')
    if set(limits) - {'max_sources', 'seconds', 'smt_milliseconds'}:
        raise InvalidInput('Unrecognized resource-limit field.')
    for key, default in [('max_sources', 10000), ('smt_milliseconds', 30000)]:
        value = limits.get(key, default)
        if type(value) is not int or value < 1:
            raise InvalidInput(key + ' must be a positive integer.')
    seconds = limits.get('seconds', 120)
    if type(seconds) not in (int, float) or not 0 < seconds < 86401:
        raise InvalidInput('seconds must be positive and at most86400.')
    empirical = request.get('empirical_admission', {})
    if not isinstance(empirical, dict):
        raise InvalidInput('Empirical admission metadata must be a JSON object.')
    if empirical.get('status') == 'NOT_ADMITTED_TO_EMPIRICAL_SOLVER':
        raise Unsupported('Empirical adapter explicitly NOT_ADMITTED; exact-law feasibility cannot reinterpret alignment counts or missing partitions as laws.')
    if empirical:
        raise Unsupported('No general empirical-admission validator is implemented. Nonempty empirical metadata cannot authorize a measured-data source fit.')
    if request.get('observation_kind') != 'exact_unranked_law':
        raise Unsupported('This engine requires declared exact unranked law inputs, not finite frequencies, sequences, calendar values or latent-route oracles.')
    if request.get('clock_contract', 'free_positive_edge_specific') != 'free_positive_edge_specific':
        raise Unsupported('Shared clock/rate ties need their actual joint source encoding; independent survival variables cannot substitute for them.')
    n = request.get('n')
    registry = request.get('registry', {})
    if not isinstance(registry, dict):
        raise InvalidInput('Registry must be a JSON object.')
    if set(registry) - {'complete', 'hybrid_ids'}:
        raise Unsupported('Additional registry constraints need their actual source encoder.')
    ids = registry.get('hybrid_ids', [])
    if type(n) is not int or n < 2:
        raise InvalidInput('n must be an integer at least2.')
    if registry.get('complete') is not True:
        raise Unsupported('UNKNOWN_UNBOUNDED_SOURCE_CLASS: a complete finite original hybrid registry is required for catalogue-NO.')
    if not isinstance(ids, list) or any((not isinstance(x, str) for x in ids)) or len(set(ids)) != len(ids):
        raise InvalidInput('Original hybrid IDs must be distinct strings.')
    modes = request.get('mechanisms', ['independent', 'common'])
    if not isinstance(modes, list) or not modes or any((x not in ['independent', 'common'] for x in modes)) or (len(set(modes)) != len(modes)):
        raise InvalidInput('Mechanisms must be a finite tagged subset of common/independent, fixed once for each candidate source across rows.')
    taxa = request.get('taxa', [f'L{i}' for i in range(n)])
    if not isinstance(taxa, list) or len(taxa) != n or any((not isinstance(t, str) for t in taxa)) or (len(set(taxa)) != n):
        raise InvalidInput('Taxa must be n distinct labels.')
    if not isinstance(request.get('rows', []), list):
        raise InvalidInput('Rows must be a finite list.')
    rows = []
    for original in request.get('rows', []):
        if not isinstance(original, dict):
            raise InvalidInput('Each row must be a JSON object.')
        if set(original) - {'samples', 'forced', 'program', 'readout', 'quartets', 'law'}:
            raise Unsupported('Additional row constraints/readers cannot be silently omitted.')
        samples = original.get('samples', {t: [t] for t in taxa})
        if not isinstance(samples, dict) or not set(samples) <= set(taxa):
            raise InvalidInput('Unknown sampling taxon.')
        if any((not isinstance(v, list) for v in samples.values())):
            raise InvalidInput('Sampling panels must be lists of copy labels.')
        labels = sum(samples.values(), [])
        if not labels or len(set(labels)) != len(labels) or any((not isinstance(x, str) for x in labels)):
            raise InvalidInput('This inherited rooted-tree engine requires nonempty globally unique sample labels; empty-panel law is a separate explicit readout.')
        force = original.get('forced', {})
        if not isinstance(force, dict) or not set(force) <= set(ids) or any((type(v) is not int or v not in [0, 1] for v in force.values())):
            raise InvalidInput('Forcing addresses only an original named hybrid and its declared incoming0/1bit.')
        program = original.get('program', [{'forced': force, 'weight': '1'}])
        if 'program' in original and 'forced' in original:
            raise InvalidInput('Use either one deterministic forced row or one randomized program.')
        if not isinstance(program, list) or not program:
            raise InvalidInput('A randomized program needs a finite nonempty list of rows.')
        operations = []
        for operation in program:
            if not isinstance(operation, dict):
                raise InvalidInput('Each program operation must be a JSON object.')
            if set(operation) - {'forced', 'weight'}:
                raise Unsupported('A programme operation has unsupported source/action constraints.')
            forcing = operation.get('forced', {})
            if not isinstance(forcing, dict) or not set(forcing) <= set(ids) or any((type(v) is not int or v not in [0, 1] for v in forcing.values())):
                raise InvalidInput('A randomized operation must address the same original hybrid registry.')
            weight = rational(operation.get('weight', '1'))
            if not 0 < weight <= 1:
                raise InvalidInput('Randomized-program support weights must be strictly positive exact rationals.')
            operations.append((weight, {f'H{ids.index(h)}': v for h, v in forcing.items()}))
        if sum((w for w, _ in operations), sp.S.Zero) != 1:
            raise InvalidInput('Randomized-program weights must sum exactly to1.')
        kind = original.get('readout', 'rooted')
        panels = original.get('quartets', [])
        if kind == 'joint_quartets' and (not isinstance(panels, list) or not panels or any((not isinstance(v, list) or len(v) != 4 or any((not isinstance(x, str) for x in v)) or (len(set(v)) != 4) or (not set(v) <= set(labels)) for v in panels))):
            raise InvalidInput('Joint quartet records require four distinct sampled copy labels per record.')
        observed = {}
        if not isinstance(original.get('law', []), list):
            raise InvalidInput('A law must be a finite list of probability/outcome objects.')
        for event in original.get('law', []):
            if not isinstance(event, dict):
                raise InvalidInput('Each law event must be a JSON object.')
            if set(event) != {'outcome', 'p'}:
                raise InvalidInput('A probability event has exactly outcome and p fields.')
            if kind == 'rooted':
                key = tree(event['outcome'], labels)
                ls = tree_labels(key)
            elif kind == 'unrooted_splits':
                key = split_event(event['outcome'], labels)
                ls = labels
            elif kind == 'joint_quartets':
                if len(event['outcome']) != len(panels):
                    raise InvalidInput('Joint outcome dimension differs from quartet record count.')
                key = tuple((split_event(v, p) for v, p in zip(event['outcome'], panels)))
                ls = labels
            else:
                raise Unsupported('Unsupported readout; no unadmitted sequence-to-topology factorization.')
            if sorted(ls) != sorted(labels):
                raise InvalidInput('A rooted tree must contain each sampled copy exactlyonce.')
            p = rational(event['p'])
            if p < 0 or p > 1 or key in observed:
                raise InvalidInput('Probability outside[0,1]or duplicated canonical outcome.')
            observed[key] = p
        if sum(observed.values(), sp.S.Zero) != 1:
            raise InvalidInput('Each exact probability law must sum to1.')
        rows.append({'samples': {f'L{taxa.index(t)}': tuple(v) for t, v in samples.items()}, 'program': operations, 'kind': kind, 'quartets': panels, 'observed': observed})
    if not rows:
        raise InvalidInput('At least one complete finite exact-law row is required.')
    return (n, ids, modes, taxa, rows)

def equations(net, mode, rows):
    eq = []
    compiled = []
    for row in rows:
        law = {}
        for weight, forcing in row['program']:
            actual = readout_law(compile_law(net, mode, forced=forcing, samples=row['samples']), row['kind'], row['quartets'])
            for outcome, probability in actual.items():
                law[outcome] = sp.expand(law.get(outcome, 0) + weight * probability)
        for k in sorted(set(law) | set(row['observed']), key=repr):
            eq.append(sp.expand(law.get(k, 0) - row['observed'].get(k, 0)))
        compiled.append(law)
    return (eq, compiled)

def as_z3(expr, variables):
    if expr.is_Rational:
        return z3.RealVal(str(expr))
    if expr.is_Symbol:
        return variables[expr]
    if expr.is_Add:
        return sum((as_z3(x, variables) for x in expr.args), z3.RealVal(0))
    if expr.is_Mul:
        out = z3.RealVal(1)
        for x in expr.args:
            out = out * as_z3(x, variables)
        return out
    if expr.is_Pow and expr.exp.is_Integer and (expr.exp >= 0):
        return as_z3(expr.base, variables) ** int(expr.exp)
    raise Unsupported('Non-polynomial source expression; unsupported encoding must not become NO.')

def exact_backend_solver(eq, variables, timeout=30000):
    zz = {v: z3.Real(str(v)) for v in variables}
    result = z3.SolverFor('QF_NRA')
    result.set(timeout=timeout)
    result.add(*[z3.And(zz[v] > 0, zz[v] < 1) for v in variables])
    result.add(*[as_z3(e, zz) == 0 for e in eq])
    return (result, zz)

def encode_value(v):
    if z3.is_rational_value(v):
        return {'kind': 'rational', 'value': str(v.as_fraction())}
    if isinstance(v, z3.AlgebraicNumRef):
        return {'kind': 'algebraic', 'polynomial_ascending': [str(x.as_fraction()) for x in v.poly()], 'real_root_index': v.index()}
    raise Unsupported('SMT model value is not an exact rational/algebraic witness.')

def decode_value(v):
    if v['kind'] == 'rational':
        return rational(v['value'])
    if v['kind'] != 'algebraic':
        raise InvalidInput('Invalid witness encoding.')
    x = sp.Symbol('_isolated_root')
    poly = sum((rational(c) * x ** i for i, c in enumerate(v['polynomial_ascending'])))
    roots = sp.real_roots(poly)
    k = v['real_root_index']
    if type(k) is not int or k < 1 or k > len(roots):
        raise InvalidInput('Invalid real algebraic root index.')
    return roots[k - 1]

def exact_zero(e):
    e = sp.cancel(e)
    if e == 0:
        return True
    if e.is_zero is not None:
        return bool(e.is_zero)
    return all((c == 0 for c in sp.to_number_field(e).coeffs()))

def verify_witness(net, mode, rows, values):
    xs, gs = net.parameters()
    variables = list(xs) + list(gs.values())
    assignment = {v: decode_value(values[str(v)]) for v in variables}
    for v, a in assignment.items():
        if a.is_positive is not True or (1 - a).is_positive is not True:
            raise InvalidInput('Witness positivity cannot be independently established exactly: ' + str(v))
    eq, laws = equations(net, mode, rows)
    if not all((exact_zero(e.subs(assignment)) for e in eq)):
        raise InvalidInput('Witness fails a shared-source row.')
    return assignment

def linear_contradiction(eq, variables):
    linear = [(i, e) for i, e in enumerate(eq) if sp.Poly(e, *variables).total_degree() <= 1]
    if not linear:
        return None
    matrix = []
    weights = []
    for i, e in linear:
        matrix.append([sp.Rational(e.coeff(x)) for x in variables] + [sp.Rational(e.subs({x: 0 for x in variables}))])
        w = [sp.S.Zero] * len(eq)
        w[i] = 1
        weights.append(w)
    k = 0
    for col in range(len(variables)):
        pivot = next((j for j in range(k, len(matrix)) if matrix[j][col] != 0), None)
        if pivot is None:
            continue
        matrix[k], matrix[pivot] = (matrix[pivot], matrix[k])
        weights[k], weights[pivot] = (weights[pivot], weights[k])
        c = matrix[k][col]
        matrix[k] = [v / c for v in matrix[k]]
        weights[k] = [v / c for v in weights[k]]
        for j in range(len(matrix)):
            if j == k:
                continue
            c = matrix[j][col]
            if c:
                matrix[j] = [a - c * b for a, b in zip(matrix[j], matrix[k])]
                weights[j] = [a - c * b for a, b in zip(weights[j], weights[k])]
        k += 1
    for row, w in zip(matrix, weights):
        active = [i for i, a in enumerate(row[:-1]) if a]
        cert = {'kind': 'EXACT_LINEAR_IDEAL_CONTRADICTION', 'multipliers': [qtext(v) for v in w]}
        if not active and row[-1] != 0:
            cert.update(reason='nonzero_constant', constant=qtext(row[-1]))
            return cert
        if len(active) == 1:
            j = active[0]
            value = -row[-1] / row[j]
            if value <= 0 or value >= 1:
                cert.update(reason='strict_unit_domain', variable=str(variables[j]), coefficient=qtext(row[j]), constant=qtext(row[-1]), forced_value=qtext(value))
                return cert
    return None

def verify_linear_certificate(eq, variables, cert):
    if len(cert['multipliers']) != len(eq):
        return False
    expression = sp.expand(sum((rational(w) * e for w, e in zip(cert['multipliers'], eq))))
    if cert['reason'] == 'nonzero_constant':
        return exact_zero(expression - rational(cert['constant'])) and rational(cert['constant']) != 0
    var = next((v for v in variables if str(v) == cert['variable']), None)
    if var is None:
        return False
    a, c = (rational(cert['coefficient']), rational(cert['constant']))
    if a == 0:
        return False
    b = -c / a
    return exact_zero(expression - (a * var + c)) and b == rational(cert['forced_value']) and (b <= 0 or b >= 1)

def graph_json(net):
    return {'edges': [list(e) for e in net.edges], 'root': net.root, 'leaves': list(net.leaves)}

def physical_realization(net, values):
    """Realize free positive edge clocks on one strict contemporaneous calendar."""
    _, outgoing, order, _ = net.structure()
    age = {}
    for vertex in reversed(order):
        age[vertex] = 0 if vertex in net.leaves else 1 + max(age[net.edges[e][1]] for e in outgoing[vertex])
    edges = []
    for edge_id, (parent, child) in enumerate(net.edges):
        duration = age[parent] - age[child]
        if duration <= 0:
            raise InvalidInput('Calendar construction did not produce a strict original edge.')
        symbol = f'x{edge_id}'
        edges.append({'original_edge_id': edge_id, 'parent': parent, 'child': child,
                      'duration': duration, 'survival_parameter': symbol,
                      'survival_value': values[symbol],
                      'positive_rate_definition': '-log(survival_value)/duration'})
    return {'original_vertex_ages': dict(sorted(age.items())),
            'contemporaneous_tip_age': 0, 'original_edges': edges,
            'ancestral_root_rate': '1',
            'natural_inheritance_values': {key: value for key, value in values.items() if key.startswith('g_')},
            'clock_scope': 'free positive edge-specific rates; exact real logarithmic definitions, not decimal approximations'}

def target_json(net):
    return {'nontrivial_displayed_split_union': sorted(set((s for v in displayed(net).values() for s in v))), 'whole_switching_split_systems': sorted(set(displayed(net).values()))}

def identity():
    d = json.loads((ROOT / 'UPSTREAM-IDENTITY.json').read_bytes())
    for r in d['files']:
        b = (ROOT / r['path']).read_bytes()
        if hashlib.sha256(b).hexdigest() != r['sha256']:
            raise InvalidInput('Pinned upstream source bytes changed.')
    return d

def solve(request, outdir):
    start = time.monotonic()
    outdir.mkdir(parents=True, exist_ok=True)
    up = identity()
    base = {'schema': 'actual-finite-original-registry-coupled-source-solver-v1', 'request': request, 'request_sha256': digest(request), 'upstream': up, 'software': {'python': platform.python_version(), 'sympy': sp.__version__, 'z3': z3.get_version_string()}, 'unknown_size_termination_or_global_NO_claimed': False, 'Lean_verification_claimed': False, 'empirical_admission_claimed': False}
    entries = []
    target_witnesses = {}
    task = request.get('task', 'find_source') if isinstance(request, dict) else 'find_source'
    target_kind = request.get('target_kind', 'nontrivial_displayed_split_union') if isinstance(request, dict) else 'nontrivial_displayed_split_union'
    try:
        n, ids, modes, taxa, rows = prepare_request(request)
    except Unsupported as e:
        return {**base, 'status': 'UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT', 'reason': str(e), 'entries': entries}
    except (InvalidInput, KeyError, TypeError) as e:
        return {**base, 'status': 'INVALID_INPUT', 'reason': str(e), 'entries': entries}
    limits = request.get('limits', {})
    maximum = limits.get('max_sources', 10000)
    seconds = limits.get('seconds', 120)
    timeout = limits.get('smt_milliseconds', 30000)

    def expired(*_):
        raise TimeLimit()
    oldhandler = signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, float(seconds))
    count = 0
    unknown = False
    try:
        z3.set_option(proof=True)
        for net in census(n, len(ids)):
            if count >= maximum:
                raise TimeLimit()
            count += 1
            if not admitted(net):
                raise InvalidInput('Census returned a source not admitted by its own original contract.')
            for mode in modes:
                eq, laws = equations(net, mode, rows)
                xs, gs = net.parameters()
                variables = list(xs) + list(gs.values())
                cert = linear_contradiction(eq, variables)
                entry = {'graph': graph_json(net), 'mechanism': mode, 'equations': [str(e) for e in eq], 'equation_sha256': digest([str(e) for e in eq]), 'target': target_json(net)}
                if cert:
                    if not verify_linear_certificate(eq, variables, cert):
                        raise InvalidInput('Internal linear certificate recomputation failed.')
                    entry.update(status='UNSAT_INDEPENDENT_EXACT_LINEAR_CERTIFICATE', certificate=cert)
                    entries.append(entry)
                    continue
                solver, zz = exact_backend_solver(eq, variables, timeout)
                smt = solver.to_smt2()
                qi = len(entries)
                query = outdir / f'query-{qi}.smt2'
                query.write_text(smt)
                entry.update(query=query.name, query_sha256=hashlib.sha256(query.read_bytes()).hexdigest())
                result = solver.check()
                if result == z3.sat:
                    values = {str(v): encode_value(solver.model().eval(zz[v], model_completion=True)) for v in variables}
                    try:
                        verify_witness(net, mode, rows, values)
                    except (InvalidInput, ValueError, NotImplementedError) as e:
                        entry.update(status='SAT_CANDIDATE_INDEPENDENT_CHECK_PENDING', values=values, reason=str(e))
                        unknown = True
                        entries.append(entry)
                        continue
                    entry.update(status='SAT_INDEPENDENT_EXACT_WITNESS', values=values,
                                 physical_realization=physical_realization(net, values))
                    entries.append(entry)
                    if task == 'find_source':
                        return {**base, 'status': 'SAT_ONE_COHERENT_ADMITTED_SOURCE', 'verification': 'INDEPENDENT_EXACT_SYMPY_WITNESS_AND_SOURCE_ADMISSION_CHECK', 'scope': 'declared complete finite registry; one graph/assignment shared across every row', 'source_count_examined': count, 'catalogue_exhausted': False, 'entries': entries, 'witness_entry': len(entries) - 1, 'elapsed_seconds': time.monotonic() - start}
                    target_witnesses.setdefault(digest(entry['target'][target_kind]), len(entries) - 1)
                    if len(target_witnesses) > 1:
                        return {**base, 'status': 'AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES', 'verification': 'INDEPENDENT_EXACT_SYMPY_WITNESSES_AND_SOURCE_ADMISSION_CHECK', 'target_kind': target_kind, 'witness_entries': list(target_witnesses.values())[:2], 'source_count_examined': count, 'catalogue_exhausted': False, 'entries': entries, 'elapsed_seconds': time.monotonic() - start}
                    continue
                if result == z3.unsat:
                    proof = outdir / f'query-{qi}.z3-proof'
                    proof.write_text(solver.proof().sexpr())
                    entry.update(status='UNSAT_EXACT_BACKEND_PROOF_NOT_INDEPENDENTLY_CHECKED', proof=proof.name, proof_sha256=hashlib.sha256(proof.read_bytes()).hexdigest())
                else:
                    entry.update(status='UNKNOWN_EXACT_BACKEND', reason=solver.reason_unknown())
                    unknown = True
                entries.append(entry)
        independent = all((e['status'] in ('UNSAT_INDEPENDENT_EXACT_LINEAR_CERTIFICATE', 'SAT_INDEPENDENT_EXACT_WITNESS') for e in entries))
        if task == 'identify_target' and target_witnesses and (not unknown):
            return {**base, 'status': 'IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY', 'verification': 'INDEPENDENT_EXACT_ALGEBRAIC_AND_LINEAR_CERTIFICATES' if independent else 'EXACT_WITNESSES_AND_BACKEND_PROOF_REPLAY_REQUIRED', 'target_kind': target_kind, 'identified_target': entries[next(iter(target_witnesses.values()))]['target'][target_kind], 'witness_entry': next(iter(target_witnesses.values())), 'source_count_examined': count, 'catalogue_exhausted': True, 'entries': entries, 'elapsed_seconds': time.monotonic() - start}
        return {**base, 'status': 'UNKNOWN_INCOMPLETE_DECISION' if unknown else 'UNSAT_COMPLETE_KNOWN_REGISTRY', 'verification': 'INDEPENDENT_EXACT_LINEAR_CERTIFICATES' if independent else 'EXACT_BACKEND_PROOF_AND_REPLAY_REQUIRED', 'scope': 'complete supplied n/original-ID registry ONLY; not unknown-size global NO', 'source_count_examined': count, 'catalogue_exhausted': True, 'entries': entries, 'elapsed_seconds': time.monotonic() - start}
    except TimeLimit:
        return {**base, 'status': 'UNKNOWN_RESOURCE_LIMIT', 'source_count_examined': count, 'catalogue_exhausted': False, 'entries': entries, 'elapsed_seconds': time.monotonic() - start}
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, oldhandler)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request')
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    out = Path(args.output)
    request = json.loads(Path(args.request).read_bytes())
    result = solve(request, out)
    (out / 'RESULT.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in ['status', 'verification', 'source_count_examined', 'catalogue_exhausted', 'elapsed_seconds', 'reason'] if k in result}, indent=2))
    return 0 if result['status'] in ['SAT_ONE_COHERENT_ADMITTED_SOURCE', 'UNSAT_COMPLETE_KNOWN_REGISTRY', 'AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES', 'IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY'] else 2
if __name__ == '__main__':
    raise SystemExit(main())
