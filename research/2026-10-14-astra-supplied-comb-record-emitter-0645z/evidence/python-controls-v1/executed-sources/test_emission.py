#!/usr/bin/env python3
"""Prepared bounded Python controls. No compiler/native subprocess is invoked.

These tests have NOT been run at the source-only draft cutoff. Literal Lean
proof checking and negative generated-proof mutations are separate owner jobs.
"""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tempfile
import types
import unittest
from unittest import mock

import emit_supplied_menu as target


def cubic(a='1/2'):
    # Fixture values only, not an alternate acquisition path in production.
    x = Fraction(a)
    return dict(schema='common_sparse_certificate_v1', level=3,
                coefficients=[str(2*x**3), str(-3*x*x), '1'],
                moments=['1', a, str(x**3)], nonnegative_terms=[
                    dict(weight=str(2*x), left=0, right=0, square=[str(-x), '1']),
                    dict(weight='1', left=1, right=0, square=[str(-x), '1'])])


def monomial(level):
    power = level*(level-1)//2
    return dict(schema='common_sparse_certificate_v1', level=level,
                coefficients=['0']*(level-1)+['1'], moments=['1']+['0']*(level-1),
                nonnegative_terms=[dict(weight='1', left=power % 2, right=0,
                                        square=['0']*(power//2)+['1'])])


def menu():
    taxa = ['D', 'A', 'C', 'B']  # Deliberately nonlexical; namespaces may overlap.
    return dict(schema='supplied_common_menu_v1', taxa=taxa,
                protected_edges=['A'], protected_hybrids=['A'], parameter_constraints=[],
                configurations=[dict(id='natural', weight='1/2', mask={'A': None}),
                                dict(id='forced', weight='1/2', mask={'A': 1}),
                                dict(id='zero', weight='0', mask={'A': 0})],
                pairs=[dict(i=i, j=j, certificate=cubic()) for i in taxa for j in taxa])


def raw(value):
    return json.dumps(value, separators=(',', ':')).encode()


class EmissionControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.providers = target.dependencies()
        cls.api = cls.providers['certificates']

    def render(self, m):
        return target.render_menu(raw(m))

    def test_complete_identity_and_existing_sources(self):
        m = menu()
        payload, manifest = self.render(m)
        ledger = json.loads(payload['IDENTITY-LEDGER.json'])
        self.assertEqual(payload['INPUT.json'], raw(m))
        self.assertEqual(ledger['input_bytes_sha256'], hashlib.sha256(raw(m)).hexdigest())
        self.assertEqual(ledger['canonical_menu_sha256'], self.api.digest(m))
        self.assertEqual(ledger['distinct_certificate_count'], 1)
        self.assertEqual(len(ledger['pair_references']), 16)
        self.assertEqual([x['label'] for x in ledger['taxa']], m['taxa'])
        self.assertEqual(ledger['original_joint_configuration_table'], m['configurations'])
        self.assertEqual(ledger['protected_edges'], ledger['protected_hybrids'])
        ident, base, support, _ = self.providers['emit_support'].render(m['pairs'][0]['certificate'])
        self.assertEqual(payload['lean/Certificate_'+ident+'.lean'], base.encode())
        self.assertEqual(payload['lean/Support_'+ident+'.lean'], support.encode())
        self.assertEqual(json.loads(payload['FIXED-QUERIES.json']),
                         self.providers['external_encoding'].fixed_queries(m))
        self.assertEqual(manifest['status'], 'UNKNOWN')
        self.assertFalse(manifest['compiled'])
        self.assertFalse(manifest['source_existence_certified'])
        for item in manifest['payload']:
            self.assertEqual(hashlib.sha256(payload[item['path']]).hexdigest(), item['sha256'])

    def test_original_pair_order_and_distinct_rows(self):
        m = menu()
        m['pairs'][0]['certificate'] = cubic('1')
        m['pairs'][3]['certificate'] = monomial(2)
        m['pairs'][5]['certificate'] = monomial(8)
        m['pairs'].reverse()
        payload, manifest = self.render(m)
        ledger = json.loads(payload['IDENTITY-LEDGER.json'])
        source = payload['lean/'+manifest['module']+'.lean'].decode()
        for index, reference in enumerate(ledger['pair_references']):
            original = m['pairs'][index]
            self.assertEqual(reference['original_pair_index'], index)
            self.assertEqual((reference['fin_i'], reference['fin_j']),
                             (m['taxa'].index(original['i']), m['taxa'].index(original['j'])))
            self.assertEqual(reference['certificate_sha256'], self.api.digest(original['certificate']))
            self.assertEqual(reference['normalized_values'],
                             [str(Fraction(x)) for x in original['certificate']['moments']])
            for k in range(1, original['certificate']['level']+1):
                self.assertIn('theorem pair_'+str(index)+'_value_'+str(k)+' :', source)
                self.assertIn('theorem pair_'+str(index)+'_coeff_'+str(k)+' :', source)
        self.assertEqual(ledger['distinct_certificate_count'], 4)
        self.assertIn('SuppliedCombCertificates (Fin 4)', source)

    def test_canonical_identity_separate_from_bytes_and_rational_value(self):
        m = menu()
        p1, _ = self.render(m)
        spaced = json.dumps(m, indent=2).encode()
        p2, _ = target.render_menu(spaced)
        a, b = (json.loads(p['IDENTITY-LEDGER.json']) for p in (p1, p2))
        self.assertEqual(a['canonical_menu_sha256'], b['canonical_menu_sha256'])
        self.assertNotEqual(a['input_bytes_sha256'], b['input_bytes_sha256'])
        m['pairs'][0]['certificate']['moments'][1] = '2/4'
        p3, _ = self.render(m)
        c = json.loads(p3['IDENTITY-LEDGER.json'])
        self.assertEqual(c['distinct_certificate_count'], 2)
        self.assertNotEqual(c['pair_references'][0]['certificate_sha256'],
                            c['pair_references'][1]['certificate_sha256'])
        self.assertEqual(c['pair_references'][0]['normalized_values'],
                         c['pair_references'][1]['normalized_values'])

    def test_every_nontrivial_level_and_nonzero_away_from_zero(self):
        m = menu()
        for index, level in enumerate(range(2, 9)):
            m['pairs'][index]['certificate'] = monomial(level)
        payload, _ = self.render(m)
        ledger = json.loads(payload['IDENTITY-LEDGER.json'])
        for level, ref in zip(range(2, 9), ledger['pair_references']):
            self.assertEqual(ref['exponents'], [k*(k-1)//2 for k in range(1, level+1)])
            base = payload['lean/Certificate_'+ref['certificate_sha256']+'.lean'].decode()
            self.assertIn('polynomial 1 ≠ 0', base)
        # Level1 cannot satisfy nonzero c and c*y1=0 when y1=1.
        impossible = dict(schema='common_sparse_certificate_v1', level=1,
                          coefficients=['1'], moments=['1'],
                          nonnegative_terms=[dict(weight='1', left=0, right=0, square=['1'])])
        m['pairs'][0]['certificate'] = impossible
        with self.assertRaises(self.api.Refused):
            self.render(m)

    def test_malformed_ordered_pair_and_joint_tables(self):
        variants = []
        x = menu(); x['pairs'].pop(); variants.append(x)
        x = menu(); x['pairs'][1] = copy.deepcopy(x['pairs'][0]); variants.append(x)
        x = menu(); x['pairs'][0]['i'] = 'absent'; variants.append(x)
        x = menu(); x['taxa'][1] = x['taxa'][0]; variants.append(x)
        x = menu(); x['parameter_constraints'] = [{'tie': ['A', 'B']}]; variants.append(x)
        x = menu(); x['configurations'][0]['weight'] = '2/3'; variants.append(x)
        x = menu(); x['configurations'][0]['mask'] = {}; variants.append(x)
        x = menu(); x['configurations'][0]['mask']['A'] = True; variants.append(x)
        for x in variants:
            with self.subTest(value=x), self.assertRaises(self.api.Refused):
                self.render(x)

    def test_malformed_certificate_and_transport(self):
        variants = []
        x = menu(); x['pairs'][0]['certificate']['coefficients'][0] = '1'; variants.append(x)
        x = menu(); x['pairs'][0]['certificate']['moments'][2] = '1/7'; variants.append(x)
        x = menu(); x['pairs'][0]['certificate']['nonnegative_terms'][0]['weight'] = '-1'; variants.append(x)
        x = menu(); x['pairs'][0]['certificate']['coefficients'][0] = str(2**129); variants.append(x)
        x = menu(); x['pairs'][0]['certificate']['moments'][1] = 0.5; variants.append(x)
        for x in variants:
            with self.subTest(value=x), self.assertRaises(self.api.Refused):
                self.render(x)
        for data in [b'{"schema":1,"schema":2}', b'\xff', b'['*66+b'0'+b']'*66,
                     b' '*262145, b'{"x":NaN}']:
            with self.subTest(data=data[:80]), self.assertRaises(self.api.Refused):
                target.render_menu(data)

    def test_output_budget_preserves_unknown_and_no_directory(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)/'emitted'
            with mock.patch.object(target, 'MAX_OUTPUT_BYTES', 64):
                with self.assertRaises(target.Unavailable):
                    target.emit(raw(menu()), output)
            self.assertFalse(output.exists())

    def test_dependency_shadow_refused(self):
        alien = types.ModuleType('certificates')
        alien.__file__ = '/wrong/certificates.py'
        with mock.patch.dict(target.sys.modules, {'certificates': alien}):
            with self.assertRaises(target.Unavailable):
                target.dependencies()

    def test_exclusive_emission_and_no_proof_placeholders(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)/'emitted'
            manifest = target.emit(raw(menu()), output)
            before = {p.relative_to(output): p.read_bytes() for p in output.rglob('*') if p.is_file()}
            with self.assertRaises(FileExistsError):
                target.emit(raw(menu()), output)
            after = {p.relative_to(output): p.read_bytes() for p in output.rglob('*') if p.is_file()}
            self.assertEqual(before, after)
            self.assertEqual(json.loads((output/'EMISSION.json').read_bytes()), manifest)
            for name, data in before.items():
                if str(name).endswith('.lean'):
                    # Scope lint only, not a proof or comprehensive axiom audit.
                    text = data.decode()
                    self.assertNotIn('sorry', text)
                    self.assertNotIn('admit', text)
                    self.assertNotIn('native_decide', text)
                    self.assertNotIn('\naxiom ', text)


if __name__ == '__main__':
    print(json.dumps({'status': 'STARTING_PYTHON_CONTROLS_NOT_LEAN',
                      'source_pins': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                      for p in [Path(__file__), Path(target.__file__),
                                                target.HERE/'lean/Astra/SuppliedCombCertificateAssembly.lean']}}), flush=True)
    unittest.main(verbosity=2)
