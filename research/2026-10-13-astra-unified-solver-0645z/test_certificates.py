"""Bounded arithmetic/transport controls; no universal checker proof."""
import copy
from fractions import Fraction
import unittest

from certificates import (MAX_BITS, MAX_BYTES, Refused, checked, common_packet,
                          generate_singleton, loads, rational, wire)


def singleton(a=Fraction(1, 2)):
    result = generate_singleton(['1', str(a), str(a**3)])
    assert result['status'] == 'GENERATED_AND_CHECKED', result
    return result['certificate']


def endpoint_one():
    return dict(schema='common_sparse_certificate_v1', level=2,
                coefficients=['1', '-1'], moments=['1', '1'],
                nonnegative_terms=[dict(weight='1', left=0, right=1, square=['1'])])


def endpoint_zero():
    # Exact certificate arithmetic is meaningful even when a putative actual
    # survival distribution supported on (0,1] cannot realize these moments.
    return dict(schema='common_sparse_certificate_v1', level=2,
                coefficients=['0', '1'], moments=['1', '0'],
                nonnegative_terms=[dict(weight='1', left=1, right=0, square=['1'])])


def menu():
    taxa = ['A', 'B', 'C', 'D']
    return dict(schema='supplied_common_menu_v1', taxa=taxa,
                protected_edges=['e:shared'], protected_hybrids=['h:left', 'h:right'],
                parameter_constraints=[],
                configurations=[
                    dict(id='coupled.left', weight='1/3', mask={'h:left': 0, 'h:right': 1}),
                    dict(id='coupled.right', weight='2/3', mask={'h:left': 1, 'h:right': 0}),
                    dict(id='zero', weight='0', mask={'h:left': None, 'h:right': None})],
                pairs=[dict(i=i, j=j, certificate=endpoint_one() if i == j else singleton())
                       for i in taxa for j in taxa])


def valid_cases():
    """A deterministic finite corpus, including several representations per law."""
    yield 'endpoint-one', endpoint_one()
    yield 'endpoint-zero-arithmetic-only', endpoint_zero()
    values = sorted({Fraction(p, q) for q in range(1, 14) for p in range(1, q+1)})
    for a in values:
        c = singleton(a)
        yield f'singleton-{a}', c
        # Scaling and splitting must preserve the identity and expectation.
        scaled = copy.deepcopy(c)
        scaled['coefficients'] = [str(3*Fraction(x)) for x in c['coefficients']]
        for term in scaled['nonnegative_terms']:
            term['weight'] = str(3*Fraction(term['weight']))
        yield f'scaled-{a}', scaled
        split = copy.deepcopy(c)
        term = split['nonnegative_terms'].pop()
        term['weight'] = str(Fraction(term['weight'])/2)
        split['nonnegative_terms'] += [copy.deepcopy(term), copy.deepcopy(term)]
        yield f'split-{a}', split
    # Nonzero coefficients and denominator are bounded after exact reduction.
    reduced = endpoint_one()
    reduced['coefficients'] = ['2/2', '-2/2']
    reduced['moments'] = ['7/7', '3/3']
    yield 'equivalent-reduced-fractions', reduced
    padded = singleton()
    padded['level'] = 8
    padded['coefficients'] += ['0']*5
    padded['moments'] += ['1/64', '1/1024', '1/32768', '1/2097152', '1/268435456']
    yield 'all-eight-sparse-levels', padded


def invalid_cases():
    c = singleton()
    for key, value in [('schema', 'other'), ('level', 0), ('level', 9), ('level', True),
                       ('coefficients', ['0', '0', '0']), ('moments', ['1', '1/2', '1/7']),
                       ('moments', ['0', '1/2', '1/8']), ('moments', ['1', '2', '1/8']),
                       ('moments', ['1', '-1/2', '1/8']),
                       ('coefficients', ['1/3', '-3/4', '1']),
                       ('coefficients', ['1/4', '-3/4']),
                       ('coefficients', ['0.25', '-3/4', '1']),
                       ('nonnegative_terms', []), ('nonnegative_terms', c['nonnegative_terms']*9)]:
        bad = copy.deepcopy(c)
        bad[key] = value
        yield f'bad-{key}-{value}', bad
    for key, value in [('weight', '-1'), ('left', 2), ('left', True), ('right', -1),
                       ('square', []), ('square', ['1']*16), ('square', ['1/0']),
                       ('square', ['1', '1']), ('weight', str(1 << MAX_BITS))]:
        bad = copy.deepcopy(c)
        bad['nonnegative_terms'][0][key] = value
        yield f'bad-term-{key}-{value}', bad
    bad = copy.deepcopy(c)
    bad['unknown'] = None
    yield 'unknown-field', bad


class CertificateTests(unittest.TestCase):
    def test_bounded_deterministic_valid_corpus(self):
        for name, c in valid_cases():
            with self.subTest(name=name):
                result = checked(c)
                self.assertEqual(result['status'], 'CHECKED_RATIONAL_CERTIFICATE')
                self.assertFalse(result['source_existence_certified'])
                self.assertEqual(result['positive_support_cardinality_at_most'], c['level']-1)
                self.assertTrue(wire(c).startswith('COMMON_CERT_V1 '))

    def test_malformed_or_false_certificates(self):
        for name, c in invalid_cases():
            with self.subTest(name=name), self.assertRaises(Refused):
                checked(c)

    def test_exact_parser_profile_and_reduced_bit_cap(self):
        for token in ['0', '-0', '1', '-1', '2/4', '-2/4', str((1 << 128)-1),
                      f'{1 << 128}/{1 << 128}']:
            self.assertEqual(rational(token), Fraction(token))
        for token in ['', '01', '-01', '+1', '0.5', '1e0', '1/0', '1/-2', '1/+2',
                      '1/02', '1_0', ' 1', '1 ', '١', '1/2/3', '--1', '-',
                      str(1 << 128), '1/'+str(1 << 128), '1'*81, 1, True, None]:
            with self.subTest(token=token), self.assertRaises(Refused):
                rational(token)

    def test_json_profile(self):
        self.assertEqual(loads(b'{"answer":"1/2"}'), {'answer': '1/2'})
        for raw in [b'{"x":1,"x":2}', b'{"x":0.5}', b'NaN', b'Infinity', b'\xff',
                    b'[', '['*2000+']'*2000, '"'+'\u00e9'*(MAX_BYTES//2)+'"',
                    b' '*(MAX_BYTES+1), '\ud800', {}, None]:
            with self.subTest(raw=str(raw)[:50]), self.assertRaises(Refused):
                loads(raw)

    def test_generator_unknown_is_not_no(self):
        for moments in [['1', '1/2', '1/7'], ['1', '0', '0'], ['1', '2', '8'],
                        ['0', '1/2', '1/8']]:
            self.assertEqual(generate_singleton(moments)['status'], 'UNKNOWN')
        # Near-cap accepted data and a genuine coefficient-cap exhaustion.
        a = Fraction((1 << 42)-1, 1 << 42)
        self.assertEqual(generate_singleton(['1', str(a), str(a**3)])['status'],
                         'GENERATED_AND_CHECKED')
        a = Fraction(6000000000000, 6000000000001)
        self.assertLessEqual((a.numerator**3).bit_length(), MAX_BITS)
        self.assertEqual(generate_singleton(['1', str(a), str(a**3)])['status'], 'UNKNOWN')
        a = Fraction((1 << 42)+1, (1 << 42)+2)
        self.assertEqual(generate_singleton(['1', str(a), str(a**3)])['status'],
                         'GENERATED_AND_CHECKED')

    def test_joint_menu_is_exact_and_remains_unknown(self):
        request = menu()
        result = common_packet(request)
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertEqual(result['supported_configurations'], ['coupled.left', 'coupled.right'])
        self.assertEqual(result['protected_count'], 3)
        self.assertEqual(result['conditional_hybrid_budget'], 54)
        self.assertTrue(result['joint_configuration_preserved'])
        self.assertFalse(result['source_existence_certified'])
        self.assertFalse(result['budget_applied_to_search'])
        self.assertEqual(request['configurations'][0]['weight'], '1/3')

    def test_joint_menu_refuses_incomplete_or_renormalized_input(self):
        changes = [lambda m: m['taxa'].append('A'),
                   lambda m: m['protected_edges'].append('e:shared'),
                   lambda m: m['configurations'][0].update(weight='1/2'),
                   lambda m: m['configurations'][0].update(weight='-1/3'),
                   lambda m: m['configurations'][1].update(id='coupled.left'),
                   lambda m: m['configurations'][0]['mask'].pop('h:left'),
                   lambda m: m['configurations'][0]['mask'].update({'h:left': True}),
                   lambda m: m['pairs'].pop(),
                   lambda m: m['pairs'][-1].update(i='A', j='A'),
                   lambda m: m['pairs'][0].update(i='outside'),
                   lambda m: m.update(parameter_constraints=[{'tie': ['h:left', 'h:right']}])]
        for i, change in enumerate(changes):
            request = menu()
            change(request)
            with self.subTest(i=i), self.assertRaises(Refused):
                common_packet(request)


if __name__ == '__main__':
    unittest.main(verbosity=2)
