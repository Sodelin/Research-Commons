"""Meaningful adversarial and source-history controls; no mesh-based sign claim."""
import argparse
from copy import deepcopy
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path
import runpy

from genealogy_workbench import g4_certificates as G

ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent
HISTORY = ROOT/'applications/genealogy-compatibility-workbench/tests/independent_forest_oracle.py'
ORACLE = runpy.run_path(str(HISTORY))
CHECKS = []


def check(name, value):
    if not value:
        raise AssertionError(name)
    CHECKS.append(name)


def refused(name, callback):
    try:
        callback()
    except (G.InputError, ValueError):
        CHECKS.append(name)
        return
    raise AssertionError('Accepted invalid evidence: '+name)


def word(a=Q(4, 5), b=Q(3, 5), q=Q(1, 2), g=Q(1, 2), extras=()):
    bank = {'a': str(a), 'b': str(b), 'q': str(q), 'g': str(g)}
    sequence = [{'kind': 'ordinary', 'occurrence_id': 'leading-original', 'survival': 'a'},
                {'kind': 'bigon', 'occurrence_id': 'body-original', 'arm_ids': ['body-left', 'body-right'], 'left': 'q', 'right': 'q', 'weight': 'g'}]
    for index, (extra_q, extra_g) in enumerate(extras):
        bank.update({f'q{index}': str(extra_q), f'g{index}': str(extra_g)})
        sequence.append({'kind': 'bigon', 'occurrence_id': f'extra{index}',
                         'arm_ids': [f'extra{index}-left', f'extra{index}-right'],
                         'left': f'q{index}', 'right': f'q{index}', 'weight': f'g{index}'})
    sequence.append({'kind': 'ordinary', 'occurrence_id': 'trailing-original', 'survival': 'b'})
    return {'kind': 'same_source_private_word_v1', 'source_id': 'control-word', 'cap': 4,
            'roots': [{'copy_id': f'A{i}', 'original_taxon_id': 'A'} for i in range(4)],
            'parameters': bank, 'chronology': sequence}


def historical_law(request, k, mode):
    _, operations = G.word_data(request)
    canonical, edge, hybrid, push = [ORACLE[n] for n in ('canonical', 'edge', 'hybrid', 'push')]
    dist = {canonical(f'A{i}' for i in range(k)): Q(1)}
    for kind, values in operations:
        if kind == 'ordinary':
            dist = push(dist, lambda f: edge(f, values[0]))
        elif mode == 'independent':
            dist = push(dist, lambda f: hybrid(f, *values))
        else:
            x, y, g = values
            def common(f):
                left, right = edge(f, x), edge(f, y)
                return {h: g*left.get(h, Q(0))+(1-g)*right.get(h, Q(0)) for h in set(left)|set(right)}
            dist = push(dist, common)
    return dist


def canonical_decoded(value):
    def tree(t):
        return t if isinstance(t, str) else ORACLE['join'](tree(t[0]), tree(t[1]))
    return ORACLE['canonical'](tree(t) for t in value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=PACKET,
                        help='Use a fresh scratch directory to preserve published evidence')
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    cone_request = json.loads((PACKET/'cone-request.json').read_text())
    cone_certificate = json.loads((PACKET/'cone-certificate.json').read_text())
    cone_result = G.check_cone(cone_request, cone_certificate)
    check('cone exact positive solution enclosure', Q(cone_result['solution_error_bound']) < Q(cone_result['minimum_proposed_weight']))
    altered = deepcopy(cone_request)
    altered['target']['g'] = '1/3'
    refused('cone rejects request substitution', lambda: G.check_cone(altered, cone_certificate))
    damaged = deepcopy(cone_certificate)
    damaged['inverse_integers'][0][0] = '0'
    refused('cone rejects damaged preconditioner', lambda: G.check_cone(cone_request, damaged))
    damaged = deepcopy(cone_certificate)
    damaged['weight_integers'][0] = '-1'
    refused('cone rejects negative proposed conic weight', lambda: G.check_cone(cone_request, damaged))
    local_request = json.loads((PACKET/'local-request.json').read_text())
    local_certificate = json.loads((PACKET/'local-certificate.json').read_text())
    local_result = G.check_separator(local_request, local_certificate)
    check('local exact interval Bernstein lower bound', min(map(Q, local_result['bernstein_coefficients'])) > 0)
    check('local explicit positive eta epsilon', all(Q(local_result['neighbourhood_constants'][k]) > 0 for k in ('epsilon', 'eta_p_y_max_norm')))
    check('local all-rival localization remains unverified', local_result['all_rival_neighbourhood_verified'] is False)
    altered = deepcopy(local_request)
    altered['common_clock'] = '1/3'
    refused('local rejects changed clock without rebinding', lambda: G.check_separator(altered, local_certificate))
    altered['target_p'] = '1/4'
    refused('local biased provider rejects fair tangent boundary', lambda: G.separator_request(altered))
    damaged = deepcopy(local_certificate)
    damaged['coefficients'][0] = '0'
    refused('local rejects tangent mismatch', lambda: G.check_separator(local_request, damaged))
    # Rebuild binomial polynomials at genuine rational coins, not inferred meshes.
    for n in range(2, 9):
        for q, g in ((Q(1, 2), Q(1, 4)), (Q(9, 10), Q(1, 10**12)), (1-Q(1, 10**12), Q(1, 2))):
            check(f'actual R polynomial arity{n} q={q} g={g}', G.evaluate(G.cell_polynomial(n), g*(1-g), 1/q) == G.normalized_diagonal(q, g, n))
    epsilon = Q(local_result['neighbourhood_constants']['epsilon'])
    extras = ((Q(9, 10), Q(1, 10**15)), (1-Q(1, 10**15), Q(1, 2)))
    a, q, clock = Q(19, 20), Q(1, 2), Q(2, 5)
    product_q = extras[0][0]*extras[1][0]
    weak_word = word(a=a, b=clock/(a*q*product_q), q=q, g=Q(1, 4), extras=extras)
    inspected = G.inspect_local_rival(weak_word, local_request, local_certificate, 'body-original')
    check('actual rare/weak array shared COMMON clock and neighbourhood', inspected['local_neighbourhood_verified'])
    check('actual rare/weak array exact mismatch', inspected['exact_diagonal_mismatch_within_neighbourhood'])
    check('rare coin non-small duration is weak under w criterion', extras[0][1]*(1-extras[0][1])*(1/extras[0][0]-1) < epsilon)
    # Algebraic coin retuning matches the first two normalized diagonals exactly.
    # This is a diagonal control, not a complete forest collision.
    p0, y0, _ = G.separator_request(local_request)
    extra_p, extra_y = extras[0][1]*(1-extras[0][1]), 1/extras[0][0]
    totals = [G.evaluate(G.cell_polynomial(n), p0, y0)/G.evaluate(G.cell_polynomial(n), extra_p, extra_y) for n in (2, 3)]
    w = (totals[0]-1)/2
    ybody = 2*(totals[1]-1)/(3*(totals[0]-1))-1
    pbody = w/(ybody-1)
    eta = Q(local_result['neighbourhood_constants']['eta_p_y_max_norm'])
    check('retuned actual algebraic coin strict admission', 0 < pbody < Q(1, 4) and 1 < ybody < Q(5, 2))
    check('retuned body in exact local rectangle', max(abs(pbody-p0), abs(ybody-y0)) < eta)
    residuals = []
    for n in (2, 3, 4):
        gap = G.evaluate(G.cell_polynomial(n), pbody, ybody)*G.evaluate(G.cell_polynomial(n), extra_p, extra_y)-G.evaluate(G.cell_polynomial(n), p0, y0)
        residuals.append({'arity': n, 'exact_gap': str(gap)})
        check(f'retuned array arity{n} exact expected equality', (gap == 0) == (n < 4))
    retuned = {'pbody': str(pbody), 'ybody': str(ybody), 'body_coin_polynomial': 'g^2-g+pbody=0; choose unique root in (0,1/2)',
               'extra_p': str(extra_p), 'extra_y': str(extra_y), 'residuals': residuals,
               'scope': 'One strict algebraic body coin and one strict rare extra. Pair/triple equalities are exact; arity4 differs. No whole-forest collision or global rival family.'}
    # Complete current-root historical oracle in both mechanisms, all coordinates.
    fixtures = {'fair-target': word(), 'chronology-rival': word(a=Q(3, 5), b=Q(4, 5)),
                'biased-target': word(a=Q(8, 9), b=Q(9, 10), g=Q(1, 4)), 'rare-weak-word': weak_word,
                'weak-many': word(extras=tuple((1-Q(1, 10**8), Q(1, 2)) for _ in range(8)))}
    certificates = {}
    for name, request in fixtures.items():
        cert = G.word_certificate(request)
        G.check_word(request, cert)
        certificates[name] = cert
        for row in cert['rows']:
            direct = historical_law(request, row['entering_roots'], row['mode'])
            computed = {canonical_decoded(entry['forest']): Q(entry['probability']) for entry in row['coordinates']}
            check(f'{name} independent history whole row {row["mode"]} cap{row["entering_roots"]}', all(computed.get(f, Q(0)) == direct.get(f, Q(0)) for f in set(computed)|set(direct)))
        (output/(name+'-request.json')).write_text(json.dumps(request, indent=2)+'\n')
        (output/(name+'-certificate.json')).write_text(json.dumps(cert, indent=2)+'\n')
    target, rival = certificates['fair-target'], certificates['chronology-rival']
    diagnostics = ('common_clock', 'r', 's', 'paired_nonlinear_gap')
    check('chronology rivals share paired diagonal diagnostics', all(target['diagnostics'][k] == rival['diagnostics'][k] for k in diagnostics))
    check('chronology rivals differ in whole forest C H', (target['diagnostics']['C'], target['diagnostics']['H']) != (rival['diagnostics']['C'], rival['diagnostics']['H']))
    damaged = deepcopy(target)
    damaged['rows'][0]['coordinates'].pop()
    refused('full word checker rejects omitted whole forest entry', lambda: G.check_word(fixtures['fair-target'], damaged))
    altered = deepcopy(fixtures['fair-target'])
    altered['parameters']['q'] = 0.5
    refused('full word checker rejects floating point parameter', lambda: G.word_certificate(altered))
    altered = deepcopy(fixtures['fair-target'])
    altered['roots'][1]['copy_id'] = altered['roots'][0]['copy_id']
    refused('full word checker rejects duplicate original copy ID', lambda: G.word_certificate(altered))
    altered = deepcopy(fixtures['fair-target'])
    altered['chronology'][1]['arm_ids'] = ['same', 'same']
    refused('full word checker rejects arm occurrence alias', lambda: G.word_certificate(altered))
    altered = deepcopy(fixtures['fair-target'])
    altered['parameters']['unused'] = '1/2'
    refused('full word checker rejects unused bank parameter', lambda: G.word_certificate(altered))
    altered = deepcopy(fixtures['fair-target'])
    altered['chronology'].reverse()
    refused('full word checker rejects chronology certificate substitution', lambda: G.check_word(altered, target))
    result = {'status': 'PASS', 'checks': len(CHECKS), 'check_names': CHECKS,
              'historical_oracle_sha256': sha256(HISTORY.read_bytes()).hexdigest(),
              'local_supplied_rare_weak_inspection': inspected, 'retuned_pair_triple_control': retuned,
              'whole_forest_chronology_control': {'target': target['diagnostics'], 'rival': rival['diagnostics']},
              'limitations': G.LIMITATIONS+' Independent historical algorithm shares the classical pure-death identity.'}
    (output/'controls.json').write_text(json.dumps(result, indent=2)+'\n')
    print(f'PASS {len(CHECKS)} exact/adversarial/source-history controls')


if __name__ == '__main__':
    main()
