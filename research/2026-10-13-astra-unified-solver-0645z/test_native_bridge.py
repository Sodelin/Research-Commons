"""Finite request identity, joint law and certificate controls for the facade."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import native_bridge

BINARY = None
RESTORED = None
CASE_OUTPUT = None
SAT = 'RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLT 1/1 1/1\n'
UNSAT = 'RC1 AFFINE 1 2 1\nLT 0/1 1/1\nLE 0/1 -1/1\n'
FORK = ('RC1 LAW 3 2 2 0 3 256 4096 256\nMECHANISM COMMON\nROOT 0\n'
        'EDGE 0 0 1\nEDGE 1 0 2\nLEAF 0 1\nLEAF 1 2\n'
        'SAMPLE 0 0\nSAMPLE 1 0\nSAMPLE 2 1\n')
HYBRID = ('RC1 LAW 5 5 2 1 3 256 4096 256\nMECHANISM COMMON\nROOT 0\n'
          'EDGE 0 0 1\nEDGE 1 0 2\nEDGE 2 2 3\nEDGE 3 2 3\nEDGE 4 3 4\n'
          'LEAF 0 1\nLEAF 1 4\nHYBRID 0 3 2 3\n'
          'SAMPLE 0 1\nSAMPLE 1 1\nSAMPLE 2 0\n')


def request(raw, certificate=None):
    value = dict(schema='native_rc1_operation_v1', operation='solve', request=raw)
    if certificate is not None:
        value.update(operation='check', certificate=certificate)
    return value


class NativeBridgeTests(unittest.TestCase):
    def setUp(self):
        self.temporary = None
        if CASE_OUTPUT is None:
            self.temporary = tempfile.TemporaryDirectory(prefix='astra-native-bridge-test-')
            self.out = Path(self.temporary.name)
        else:
            self.out = CASE_OUTPUT/self._testMethodName
            self.out.mkdir(parents=True, exist_ok=False)
        self.counter = 0

    def tearDown(self):
        if self.temporary is not None:
            self.temporary.cleanup()

    def consume(self, value, binary=BINARY, restored=RESTORED):
        self.counter += 1
        out = self.out/str(self.counter)
        result = native_bridge.consume(value, out, binary, restored)
        self.assertFalse(result['source_feasibility_certified'])
        self.assertFalse(result['unknown_size_exclusion_certified'])
        return result, out

    def test_exact_affine_shared_vector_and_independent_native_check(self):
        for raw, expected in [(SAT, 'CERTIFIED_AFFINE_WITNESS'), (UNSAT, 'CERTIFIED_AFFINE_EXCLUSION')]:
            result, out = self.consume(request(raw))
            self.assertEqual(result['status'], expected)
            self.assertTrue(result['native_checker_algorithm_independent'])
            self.assertTrue(result['certificate_checked'])
            self.assertEqual((out/'REQUEST.rc1').read_text(), raw)
            certificate = (out/'RESPONSE.rc1').read_text()
            checked, _ = self.consume(request(raw, certificate))
            self.assertEqual(checked['status'], expected)

    def test_affine_mutation_and_wrong_request_refused(self):
        _, out = self.consume(request(SAT))
        certificate = (out/'RESPONSE.rc1').read_text()
        for raw, altered in [(SAT, certificate.replace('WITNESS 1 1/2', 'WITNESS 1 2/1')),
                             (UNSAT, certificate), (SAT, certificate+'garbage\n')]:
            result, _ = self.consume(request(raw, altered))
            self.assertEqual(result['status'], 'REFUSED_REQUEST')

    def test_joint_forward_and_explicit_replay_boundary(self):
        for raw in [FORK, HYBRID, HYBRID.replace('COMMON', 'INDEPENDENT')]:
            result, out = self.consume(request(raw))
            self.assertEqual(result['status'], 'CHECKED_SYMBOLIC_FORWARD_TABLE')
            self.assertFalse(result['native_checker_algorithm_independent'])
            self.assertFalse(result['physical_source_admission_verified'])
            certificate = (out/'RESPONSE.rc1').read_text()
            self.assertIn('GATE SOURCE_ADMISSION_NOT_ESTABLISHED\n', certificate)
            self.assertIn(raw, certificate)
            if raw == HYBRID:
                self.assertIn('VARIABLES 6 X:0 X:1 X:2 X:3 X:4 G:0\n', certificate)
            if raw == FORK:
                self.assertIn('ROOTED 3\n', certificate)
                self.assertIn('TREE ((0,1),2) 2\nTERM 1/1 0 0\nTERM -2/3 1 0\n', certificate)
                self.assertIn('TREE ((0,2),1) 1\nTERM 1/3 1 0\n', certificate)
                self.assertIn('TREE (0,(1,2)) 1\nTERM 1/3 1 0\n', certificate)
                corrupted = certificate.replace('TERM -2/3 1 0', 'TERM -1/3 1 0')
                rejected, _ = self.consume(request(raw, corrupted))
                self.assertEqual(rejected['status'], 'REFUSED_REQUEST')

    def test_budget_unknown_never_exclusion(self):
        for raw in [SAT.replace('1 2 1\n', '1 2 0\n'),
                    FORK.replace('256 4096 256', '0 4096 256')]:
            result, out = self.consume(request(raw))
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertFalse(result['certificate_checked'])
            self.assertNotIn('check_execution', result)
            rejected, _ = self.consume(request(raw, (out/'RESPONSE.rc1').read_text()))
            self.assertEqual(rejected['status'], 'REFUSED_REQUEST')
            self.assertEqual(rejected['supplied_native_status'], 'UNKNOWN')
            self.assertEqual(rejected['mathematical_decision'], 'UNKNOWN')
            self.assertFalse(rejected['certificate_checked'])
            self.assertEqual(rejected['check_execution']['exit_code'], 1)
            self.assertIn('not a feasibility or exclusion certificate', rejected['reason'])

    def test_native_malformed_source_and_transport_controls(self):
        malformed = [SAT.replace('1/1', '1.0'), SAT.replace('0/1', '0/2'),
                     SAT.replace(' 1 2 1', ' 01 2 1'), SAT.rstrip('\n'), SAT+'\n',
                     FORK.replace('EDGE 1 0 2', 'EDGE 1 0 1'),
                     FORK.replace('SAMPLE 2 1', 'SAMPLE 2 2'),
                     HYBRID.replace('HYBRID 0 3 2 3', 'HYBRID 0 3 2 2')]
        for raw in malformed:
            result, _ = self.consume(request(raw))
            self.assertEqual(result['status'], 'REFUSED_REQUEST')
        for value in [request('RC1 COUNT 1/1 1/1 1/1 1/1\n'), request('é'),
                      request('X'*65537), {**request(SAT), 'source_admitted': True}]:
            result, _ = self.consume(value)
            self.assertEqual(result['status'], 'REFUSED_REQUEST')
            self.assertNotIn('runtime', result)

    def test_runtime_identity_and_unavailable_stay_explicit(self):
        missing, _ = self.consume(request(SAT), None, None)
        self.assertEqual(missing['status'], 'UNKNOWN')
        self.assertNotIn('solve_execution', missing)
        fake = self.out/'untrusted-binary'
        fake.write_bytes(b'not the executed binary')
        refused, _ = self.consume(request(SAT), fake, RESTORED)
        self.assertEqual(refused['status'], 'REFUSED_REQUEST')
        self.assertNotIn('solve_execution', refused)
        fake_root = self.out/'fake-root'
        fake_root.mkdir()
        (fake_root/'RESTORED-SOURCES.json').write_text('{}')
        refused, _ = self.consume(request(SAT), BINARY, fake_root)
        self.assertEqual(refused['status'], 'REFUSED_REQUEST')
        self.assertNotIn('solve_execution', refused)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--restored', type=Path, required=True)
    parser.add_argument('--case-output', type=Path)
    arguments = parser.parse_args()
    BINARY = arguments.binary.resolve()
    RESTORED = arguments.restored.resolve()
    if arguments.case_output is not None:
        CASE_OUTPUT = arguments.case_output.resolve()
    # Defaults are bound at function definition; bind the selected configuration
    # explicitly for this test process after parsing its separate runtime flags.
    NativeBridgeTests.consume.__defaults__ = (BINARY, RESTORED)
    unittest.main(argv=['test_native_bridge.py'], verbosity=2)
