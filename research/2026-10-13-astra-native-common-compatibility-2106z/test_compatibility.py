#!/usr/bin/env python3
"""Bounded contract/ID tests. No native execution, Lean or Rust compiler."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import compatibility as subject

RESTORED = Path(os.environ.get('ASTRA_RESTORED_PARITY', '/workspace/scratch/astra-recovered-parity-0702'))


def request():
    return json.loads((subject.BASELINE / 'examples/correlated-menu.json').read_text())


def encode(value):
    return json.dumps(value, separators=(',', ':')).encode()


def renamed(value, old, new):
    """Rename one existing protected-hybrid symbol in its own namespace."""
    value['input']['protected_hybrids'] = [new if x == old else x
                                        for x in value['input']['protected_hybrids']]
    for configuration in value['input']['configurations']:
        configuration['mask'][new] = configuration['mask'].pop(old)


class CompatibilityTests(unittest.TestCase):
    def test_exact_existing_example_preserves_all_padded_copies(self):
        supplied = request()
        raw = encode(supplied)
        report = subject.report(raw, RESTORED)
        self.assertEqual(report['status'], 'UNKNOWN')
        self.assertTrue(report['compatibility_report_complete'])
        self.assertFalse(report['source_feasibility_certified'])
        self.assertFalse(report['native_execution_performed'])
        self.assertFalse(report['arbitrary_input_G3_resolved'])
        self.assertEqual(report['original_input_bytes_sha256'], hashlib.sha256(raw).hexdigest())
        self.assertEqual(report['original_joint_configurations'], supplied['input']['configurations'])
        for row in report['rows']:
            self.assertEqual(row['required_copy_count'], len(supplied['input']['taxa']) + row['level'] + 1)
            self.assertGreaterEqual(row['required_copy_count'], 6)
            self.assertFalse(row['fits_native_copy_profile'])
            self.assertEqual(len({x['copy_id'] for x in row['fixed_copy_allocation']}), row['required_copy_count'])
            self.assertEqual(len(row['selected_keep']), row['level'] + 1)
        binding = report['source_parameter_binding']
        self.assertEqual(binding['status'], 'UNBOUND')
        self.assertEqual(binding['established_fit_conversion'], 'Gamma = 1 - old_parent_zero_probability')
        self.assertTrue(binding['original_incoming_order_must_be_preserved'])
        self.assertFalse(binding['actual_parameter_conversion_performed'])

    def test_text_is_legal_in_distinct_typed_namespaces(self):
        supplied = request()
        name = supplied['input']['taxa'][0]
        supplied['input']['protected_edges'].append(name)
        renamed(supplied, supplied['input']['protected_hybrids'][0], name)
        supplied['input']['configurations'][0]['id'] = name
        report = subject.report(encode(supplied), RESTORED)
        for namespace in ['taxon', 'protected_edge', 'protected_hybrid', 'configuration']:
            self.assertIn(name, [x['id'] for x in report['typed_ids'][namespace]])
        self.assertFalse(report['input_ordinals_are_candidate_indices'])

    def test_tagged_copy_labels_do_not_collide_with_taxon_text(self):
        supplied = request()
        old = supplied['input']['taxa'][0]
        supplied['input']['taxa'][0] = 'selected:A1'
        for row in supplied['input']['pairs']:
            for key in ['i', 'j']:
                if row[key] == old:
                    row[key] = 'selected:A1'
        report = subject.report(encode(supplied), RESTORED)
        copies = report['rows'][0]['fixed_copy_allocation']
        self.assertIn('baseline:selected:A1', [x['copy_id'] for x in copies])
        self.assertIn('selected:A1', [x['copy_id'] for x in copies])

    def test_original_bytes_and_semantics_are_separate(self):
        supplied = request()
        compact = subject.report(encode(supplied), RESTORED)
        pretty = subject.report(json.dumps(supplied, indent=2).encode(), RESTORED)
        self.assertNotEqual(compact['original_input_bytes_sha256'], pretty['original_input_bytes_sha256'])
        self.assertEqual(compact['canonical_request_sha256'], pretty['canonical_request_sha256'])
        supplied['input']['configurations'].reverse()
        reordered = subject.report(encode(supplied), RESTORED)
        self.assertNotEqual(compact['canonical_request_sha256'], reordered['canonical_request_sha256'])
        self.assertEqual(compact['derived_mask_pmf']['sha256'], reordered['derived_mask_pmf']['sha256'])
        self.assertEqual(reordered['original_joint_configurations'], supplied['input']['configurations'])

    def test_zero_mass_and_exact_fraction_alias_are_not_renormalized(self):
        supplied = request()
        certificates, _ = subject.providers()
        original = subject.report(encode(supplied), RESTORED)
        for row in supplied['input']['configurations']:
            value = certificates.rational(row['weight'])
            row['weight'] = f'{2*value.numerator}/{2*value.denominator}'
        report = subject.report(encode(supplied), RESTORED)
        self.assertNotEqual(original['canonical_request_sha256'], report['canonical_request_sha256'])
        self.assertEqual(original['derived_mask_pmf']['sha256'], report['derived_mask_pmf']['sha256'])
        self.assertFalse(report['derived_mask_pmf']['renormalized'])
        self.assertEqual(report['original_joint_configurations'], supplied['input']['configurations'])
        self.assertTrue(any(certificates.rational(x['weight']) == 0 for x in report['original_joint_configurations']))

    def test_joint_correlation_is_not_replaced_by_marginals(self):
        supplied = request()
        ids = supplied['input']['protected_hybrids']
        self.assertEqual(len(ids), 2)
        supplied['input']['configurations'] = [
            dict(id='left', weight='1/2', mask={ids[0]: 0, ids[1]: 1}),
            dict(id='right', weight='1/2', mask={ids[0]: 1, ids[1]: 0})]
        first = subject.report(encode(supplied), RESTORED)
        supplied['input']['configurations'][0]['mask'][ids[1]] = 0
        supplied['input']['configurations'][1]['mask'][ids[1]] = 1
        second = subject.report(encode(supplied), RESTORED)
        self.assertNotEqual(first['derived_mask_pmf']['sha256'], second['derived_mask_pmf']['sha256'])
        supplied['input']['configurations'][0]['mask'][ids[1]] = None
        natural = subject.report(encode(supplied), RESTORED)
        self.assertNotEqual(second['derived_mask_pmf']['sha256'], natural['derived_mask_pmf']['sha256'])

    def test_existing_refusals_for_duplicates_ties_and_pmf(self):
        certificates, _ = subject.providers()
        changes = [lambda m: m['taxa'].append(m['taxa'][0]),
                   lambda m: m['protected_edges'].extend(['edge:one', 'edge:one']),
                   lambda m: m['protected_hybrids'].append(m['protected_hybrids'][0]),
                   lambda m: m['configurations'][1].update(id=m['configurations'][0]['id']),
                   lambda m: m['configurations'][0].update(weight='1/3'),
                   lambda m: m['configurations'][0].update(weight='-1'),
                   lambda m: m['configurations'][0]['mask'].pop(m['protected_hybrids'][0]),
                   lambda m: m.update(parameter_constraints=[{'tie': m['protected_hybrids']}])]
        for i, change in enumerate(changes):
            supplied = request()
            change(supplied['input'])
            with self.subTest(case=i), self.assertRaises(certificates.Refused):
                subject.report(encode(supplied), RESTORED)

    def test_duplicate_fields_float_and_malformed_bytes(self):
        certificates, _ = subject.providers()
        for raw in [b'{"schema":1,"schema":2}', b'{"x":0.5}', b'NaN', b'\xff', b' ' * 262145]:
            with self.subTest(raw=raw[:40]), self.assertRaises(certificates.Refused):
                subject.report(raw, RESTORED)

    def test_missing_native_source_is_unknown_and_no_output_overwrite(self):
        with tempfile.TemporaryDirectory(prefix='astra-compatibility-') as folder:
            directory = Path(folder)
            incoming = directory / 'request.json'
            incoming.write_bytes(encode(request()))
            output = directory / 'result'
            args = [sys.executable, '-B', str(subject.HERE / 'compatibility.py'),
                    '--request', str(incoming), '--output', str(output),
                    '--native-sources', str(directory / 'absent')]
            run = subprocess.run(args, capture_output=True, timeout=3)
            self.assertEqual(run.returncode, 2)
            result = json.loads((output / 'RESULT.json').read_text())
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertFalse(result['compatibility_report_complete'])
            preserved = (output / 'RESULT.json').read_bytes()
            repeat = subprocess.run(args, capture_output=True, timeout=3)
            self.assertNotEqual(repeat.returncode, 0)
            self.assertEqual((output / 'RESULT.json').read_bytes(), preserved)

    def test_report_cannot_mutate_shared_authentication_pins(self):
        report = subject.report(encode(request()), RESTORED)
        report['reused_python_sources']['certificates.py'] = 'changed'
        report['selected_native_profile']['source_pins']['law.rs'] = 'changed'
        again = subject.report(encode(request()), RESTORED)
        self.assertEqual(again['reused_python_sources'], subject.PYTHON_PINS)
        self.assertEqual(again['selected_native_profile']['source_pins'], subject.RUST_PINS)


if __name__ == '__main__':
    print(json.dumps({'test_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                      'implementation_sha256': hashlib.sha256(Path(subject.__file__).read_bytes()).hexdigest(),
                      'native_source_inventory': str(RESTORED), 'native_compiler_invocations': 0}), flush=True)
    unittest.main(verbosity=2)
