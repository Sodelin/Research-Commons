#!/usr/bin/env python3
"""UNEXECUTED owner-run tests of unchanged certificate/query providers only.

No compiler, native executable, backend search, network or mocked source witness.
Use the owner's existing small-process guard and a fresh output directory.
"""
import argparse
import copy
import hashlib
import importlib
import io
import json
from pathlib import Path
import sys
import unittest

PINS = {
    'certificates.py': 'ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3',
    'external_encoding.py': '78dfd11a8157a5102c520be85a5fc42f4b4137250846ce510df9df98a90f4d69',
}
C = E = None


def singleton(a='1/2', cube='1/8'):
    return C.generate_singleton(['1', a, cube])['certificate']


def menu(n=4):
    taxa = [chr(65+i) for i in range(n)]
    return dict(schema='supplied_common_menu_v1', taxa=taxa,
                protected_edges=[], protected_hybrids=['H:1', 'H:2'],
                parameter_constraints=[],
                configurations=[dict(id='left', weight='1/2', mask={'H:1': 0, 'H:2': 0}),
                                dict(id='right', weight='1/2', mask={'H:1': 1, 'H:2': 1}),
                                dict(id='zero', weight='0', mask={'H:1': None, 'H:2': None})],
                pairs=[dict(i=i, j=j, certificate=singleton('1', '1') if i == j else singleton())
                       for i in taxa for j in taxa])


class ContractTests(unittest.TestCase):
    def test_exact_json_refusals(self):
        for raw in [b'{"x":1,"x":2}', b'{"x":0.5}', b'NaN', b'\xff']:
            with self.subTest(raw=raw), self.assertRaises(C.Refused):
                C.loads(raw)

    def test_singleton_generic_bound_is_two_not_one(self):
        result = C.generate_singleton(['1', '1/2', '1/8'])
        self.assertEqual(result['status'], 'GENERATED_AND_CHECKED')
        self.assertEqual(result['check']['positive_support_cardinality_at_most'], 2)
        self.assertFalse(result['check']['source_existence_certified'])

    def test_non_singleton_generation_is_unknown(self):
        self.assertEqual(C.generate_singleton(['1', '1/2', '1/16'])['status'], 'UNKNOWN')

    def test_forged_identity_is_refused(self):
        cert = singleton()
        cert['coefficients'][0] = '1/3'
        with self.assertRaises(C.Refused):
            C.checked(cert)

    def test_level_one_cannot_annihilate_normalized_bank(self):
        cert = dict(schema='common_sparse_certificate_v1', level=1,
                    coefficients=['1'], moments=['1'],
                    nonnegative_terms=[dict(weight='1', left=0, right=0, square=['1'])])
        with self.assertRaises(C.Refused):
            C.checked(cert)

    def test_valid_arithmetic_can_have_no_positive_bank(self):
        cert = dict(schema='common_sparse_certificate_v1', level=2,
                    coefficients=['0', '1'], moments=['1', '0'],
                    nonnegative_terms=[dict(weight='1', left=1, right=0, square=['1'])])
        result = C.checked(cert)
        self.assertEqual(result['status'], 'CHECKED_RATIONAL_CERTIFICATE')
        self.assertFalse(result['source_existence_certified'])

    def test_endpoint_one_is_kept(self):
        cert = dict(schema='common_sparse_certificate_v1', level=2,
                    coefficients=['1', '-1'], moments=['1', '1'],
                    nonnegative_terms=[dict(weight='1', left=0, right=1, square=['1'])])
        result = C.checked(cert)
        self.assertEqual(result['positive_support_cardinality_at_most'], 1)
        self.assertEqual(result['survival_domain'], '(0,1]')
        self.assertFalse(result['source_existence_certified'])

    def test_unsupported_ties_are_refusal_not_no(self):
        value = menu()
        value['parameter_constraints'] = [{'tie': ['H:1', 'H:2']}]
        with self.assertRaises(C.Refused):
            C.common_packet(value)

    def test_malformed_pmf_and_mask(self):
        for kind in ['mass', 'negative', 'missing']:
            value = menu()
            if kind == 'mass':
                value['configurations'][0]['weight'] = '0'
            elif kind == 'negative':
                value['configurations'][0]['weight'] = '-1/2'
            else:
                del value['configurations'][0]['mask']['H:1']
            with self.subTest(kind=kind), self.assertRaises(C.Refused):
                C.common_packet(value)

    def test_larger_schema_is_refusal_not_source_exclusion(self):
        with self.assertRaises(C.Refused):
            C.common_packet(menu(9))
        cert = singleton()
        cert['level'] = 9
        with self.assertRaises(C.Refused):
            C.checked(cert)

    def test_joint_masks_and_zero_mass_records_are_forwarded(self):
        original = menu()
        other = copy.deepcopy(original)
        other['configurations'][0]['mask']['H:2'] = 1
        other['configurations'][1]['mask']['H:2'] = 0
        first, second = E.fixed_queries(original), E.fixed_queries(other)
        self.assertNotEqual(first['queries'][0]['row_sha256'], second['queries'][0]['row_sha256'])
        self.assertTrue(all(q['configuration_table'] == original['configurations'] for q in first['queries']))
        natural = copy.deepcopy(original)
        natural['configurations'][0]['mask']['H:1'] = None
        self.assertNotEqual(first['queries'][0]['row_sha256'], E.fixed_queries(natural)['queries'][0]['row_sha256'])
        self.assertEqual(C.common_packet(original)['supported_configurations'], ['left', 'right'])

    def test_tiny_positive_mass_is_not_zero(self):
        value = menu()
        denominator = 2**100
        value['configurations'][0]['weight'] = f'1/{denominator}'
        value['configurations'][1]['weight'] = f'{denominator-1}/{denominator}'
        self.assertEqual(C.common_packet(value)['supported_configurations'], ['left', 'right'])

    def test_typed_namespace_reuse_is_legal(self):
        value = menu()
        value['protected_edges'] = ['A']
        value['protected_hybrids'][0] = 'A'
        value['configurations'][0]['id'] = 'A'
        for cfg in value['configurations']:
            cfg['mask']['A'] = cfg['mask'].pop('H:1')
        self.assertEqual(C.common_packet(value)['status'], 'UNKNOWN')

    def test_tagged_copies_cannot_collide_with_taxon_text(self):
        value = menu()
        value['taxa'][0] = 'selected:A1'
        for pair in value['pairs']:
            for key in ['i', 'j']:
                if pair[key] == 'A':
                    pair[key] = 'selected:A1'
        query = E.fixed_queries(value)['queries'][0]
        self.assertIn('baseline:selected:A1', query['allocation'])
        self.assertIn('selected:A1', query['allocation'])
        self.assertEqual(len(query['allocation']), 6)

    def test_informative_rows_keep_padding_direction_event_and_normalization(self):
        value = menu()
        rows = [q for q in E.fixed_queries(value)['queries'] if q['directed_pair'] == ['A', 'B']]
        self.assertEqual([len(q['allocation']) for q in rows], [6, 7, 8])
        self.assertEqual([q['normalized_moment'] for q in rows], ['1', '1/2', '1/8'])
        self.assertEqual([q['comb_coefficient'] for q in rows], ['1', '1/3', '1/18'])
        self.assertEqual([q['required_event_probability'] for q in rows], ['1', '1/6', '1/144'])
        self.assertEqual(rows[2]['readout']['forest'],
                         [[[['selected:B', 'selected:A1'], 'selected:A2'], 'selected:A3']])
        for q in rows:
            self.assertEqual(q['allocation']['selected:B'], 'B')
            self.assertTrue(all(q['allocation'][x] == 'A' for x in q['readout']['keep'][1:]))
            self.assertEqual(len(q['readout']['keep']), q['level']+1)

    def test_full_menu_reaches_seventeen_copies(self):
        value = menu(8)
        for pair in value['pairs']:
            cert = pair['certificate']
            a = C.rational(cert['moments'][1])
            cert['level'] = 8
            cert['coefficients'] += ['0']*5
            cert['moments'] = [str(a**(k*(k-1)//2)) for k in range(1, 9)]
        rows = E.fixed_queries(value)['queries']
        self.assertEqual(max(len(q['allocation']) for q in rows), 17)

    def test_conditional_budget_is_not_search_completeness(self):
        result = C.common_packet(menu())
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertEqual(result['conditional_support_cap'], 2)
        self.assertFalse(result['budget_applied_to_search'])
        self.assertFalse(result['source_existence_certified'])
        self.assertFalse(result['unknown_size_exclusion_certified'])

    def test_fraction_aliases_do_not_rewrite_request_identity(self):
        value = menu()
        other = copy.deepcopy(value)
        other['configurations'][0]['weight'] = '2/4'
        self.assertEqual(C.common_packet(other)['status'], 'UNKNOWN')
        self.assertNotEqual(C.digest(value), C.digest(other))


def main():
    global C, E
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    base = args.repo.resolve() / 'research/2026-10-13-astra-unified-solver-0645z'
    for name, expected in PINS.items():
        path = base / name
        if path.is_symlink() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit('Source identity mismatch: ' + name)
    sys.path.insert(0, str(base))
    C, E = importlib.import_module('certificates'), importlib.import_module('external_encoding')
    for module in (C, E):
        if Path(module.__file__).resolve().parent != base:
            raise SystemExit('Unexpected provider origin')
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(ContractTests))
    (args.output / 'TEST-OUTPUT.txt').write_text(stream.getvalue())
    receipt = dict(status='PASS' if result.wasSuccessful() else 'FAIL',
                   test_count=result.testsRun, failures=len(result.failures), errors=len(result.errors),
                   test_source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   provider_sha256=PINS, scope='Pure certificate/query contract tests only',
                   compiler_invocations=0, native_invocations=0, source_backend_invocations=0,
                   source_feasibility_certified=False, universal_native_refinement_proved=False)
    (args.output / 'RESULT.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt))
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    raise SystemExit(main())
