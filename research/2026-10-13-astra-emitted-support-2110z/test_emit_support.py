#!/usr/bin/env python3
"""Transport/validation controls; these do not check Lean elaboration."""
import copy
from fractions import Fraction
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import emit_support
from prepare_cases import examples


class EmissionControls(unittest.TestCase):
    def test_original_three_literal_proof_bytes_remain_exact(self):
        expected = {
            'quarter': 'e06de07c68a4b2596b47deba5d46bc7d492ceabd0037a5e2b92c0d1c8536a16a',
            'half': '7f3818afac78dd66642eaf4971ae949f68818f85c1f096404c1fae4d86feb0bc',
            'one': '03514f3f24b5ab3473159ea105ca521a6977668f89c76a02f8b4e36f10d2859e',
        }
        for name, digest in expected.items():
            _, base, _, _ = emit_support.render(examples()[name])
            self.assertEqual(hashlib.sha256(base.encode()).hexdigest(), digest)

    def test_bounded_corpus_preserves_original_checker_identity(self):
        api, _ = emit_support.dependencies()
        for certificate in examples().values():
            ident, _, _, interface = emit_support.render(certificate)
            check = api.checked(certificate)
            self.assertEqual(ident, check['certificate_sha256'])
            self.assertEqual(interface['support_cap'], check['positive_support_cardinality_at_most'])
            powers = interface['exponents']
            point = interface['nonzero_test_point']
            value = sum(Fraction(c) * point**power
                        for c, power in zip(certificate['coefficients'], powers))
            self.assertNotEqual(value, 0)
        # This certificate has p(0)=p(1)=0; the proven nonzero evaluation
        # lies outside the survival interval. A constant-only check would fail.
        self.assertEqual(emit_support.render(examples()['zero-constant'])[3]['nonzero_test_point'], 2)

    def test_invalid_certificate_never_creates_output(self):
        mutations = []
        wrong_identity = copy.deepcopy(examples()['half'])
        wrong_identity['nonnegative_terms'][0]['weight'] = '2'
        mutations.append(wrong_identity)
        wrong_moment = copy.deepcopy(examples()['half'])
        wrong_moment['moments'][2] = '1/9'
        mutations.append(wrong_moment)
        wrong_level = copy.deepcopy(examples()['half'])
        wrong_level['level'] = 9
        mutations.append(wrong_level)
        target_input = copy.deepcopy(examples()['half'])
        target_input['desired_support_cap'] = 1
        mutations.append(target_input)
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'output'
            for certificate in mutations:
                with self.assertRaises(ValueError):
                    emit_support.emit(certificate, output)
                self.assertFalse(output.exists())

    def test_output_collision_preserves_existing_evidence(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / 'output'
            emitted = emit_support.emit(examples()['half'], output)
            before = {p.name: p.read_bytes() for p in output.iterdir()}
            with self.assertRaises(FileExistsError):
                emit_support.emit(examples()['half'], output)
            self.assertEqual(before, {p.name: p.read_bytes() for p in output.iterdir()})
            self.assertFalse(emitted['compiled'])
            self.assertFalse(emitted['physical_representative_certified'])
            self.assertFalse(emitted['source_existence_certified'])

    def test_dependency_pin_and_module_shadow_fail_closed(self):
        selected = next(iter(emit_support.PINS))
        pins = dict(emit_support.PINS)
        pins[selected] = '0' * 64
        with mock.patch.object(emit_support, 'PINS', pins):
            with self.assertRaisesRegex(ValueError, 'dependency differs'):
                emit_support.render(examples()['half'])
        api, _ = emit_support.dependencies()
        with mock.patch.object(api, '__file__', '/tmp/other/certificates.py'):
            with self.assertRaisesRegex(ValueError, 'shadowed'):
                emit_support.render(examples()['half'])


if __name__ == '__main__':
    unittest.main()
