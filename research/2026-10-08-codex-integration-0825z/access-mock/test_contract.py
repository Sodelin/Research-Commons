import tempfile
import unittest
from pathlib import Path
from offline_policy_contract import MockPolicy, SCENARIOS, comparison, request


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.path = Path(self.directory.name) / 'attempts.sqlite'
        self.policy = MockPolicy(self.path)

    def tearDown(self):
        self.policy.close()
        self.directory.cleanup()

    def test_retryable_failure_consumes_one_then_restart_preserves_it(self):
        for scenario, outcome in zip(SCENARIOS, ('UNAVAILABLE', 'RESOURCE_EXHAUSTED', 'TIMEOUT', 'CRASH')):
            self.assertEqual(self.policy.exercise(request(scenario), outcome), {'status': outcome, 'attempts': 1})
        self.policy.close()
        self.policy = MockPolicy(self.path)
        self.assertEqual(self.policy.used(), 4)
        self.assertEqual(self.policy.exercise({'mode': 'OFFLINE_MOCK', 'operation': 'metadata'})['attempts'], 1)
        self.assertEqual(self.policy.exercise(request('A')), {'status': 'RESOURCE_LIMIT', 'attempts': 0})
        self.assertEqual(self.policy.used(), 5)

    def test_metadata_and_scenario_cannot_repeat_even_after_retryable_failure(self):
        metadata = {'mode': 'OFFLINE_MOCK', 'operation': 'metadata'}
        self.policy.exercise(metadata)
        self.assertEqual(self.policy.exercise(metadata), {'status': 'REPEAT_DISABLED', 'attempts': 0})
        self.policy.exercise(request('REF'), 'UNAVAILABLE')
        self.assertEqual(self.policy.exercise(request('REF')), {'status': 'REPEAT_DISABLED', 'attempts': 0})
        self.assertEqual(self.policy.used(), 2)

    def test_live_unrestricted_fields_and_mismatched_settings_refuse_before_reservation(self):
        tests = [({**request('REF'), 'mode': 'LIVE'}, 'LIVE_DISABLED'),
                 ({**request('REF'), 'api_key': 'fixture-never-a-real-key'}, 'INVALID_FIELDS'),
                 ({**request('REF'), 'address': 'arbitrary-destination'}, 'INVALID_FIELDS'),
                 ({**request('REF'), 'operation': 'http_proxy'}, 'UNSUPPORTED_OPERATION'),
                 ({**request('REF'), 'settings': 'other'}, 'SETTINGS_MISMATCH'),
                 ({**request('REF'), 'length': 1048576}, 'INVALID_INPUT'),
                 ({**request('REF'), 'phase': 'cis'}, 'PHASE_EVIDENCE_REQUIRED')]
        for data, expected in tests:
            self.assertEqual(self.policy.exercise(data), {'status': expected})
        self.assertEqual(self.policy.used(), 0)

    def test_four_scenarios_separate_endpoints_and_missing_pas(self):
        self.policy.exercise({'mode': 'OFFLINE_MOCK', 'operation': 'metadata'})
        rows = {name: self.policy.exercise(request(name)) for name in SCENARIOS}
        result = comparison(rows)
        self.assertEqual(result['expression_linear'], {'additive_change': '5', 'combined_change': '12', 'interaction': '7'})
        self.assertEqual(result['splice_usage_fraction'], {'additive_change': '1/20', 'combined_change': '9/100', 'interaction': '1/25'})
        self.assertEqual(result['PAS'], 'UNAVAILABLE')
        self.assertEqual(result['model_confidence'], 'NOT_CALIBRATED')
        self.assertFalse(result['biological_conclusion_established'])
        self.assertFalse(rows['A+B']['combined_is_observed'])

    def test_single_variant_scores_cannot_supply_combined_effect(self):
        rows = {name: self.policy.exercise(request(name)) for name in ('REF', 'A', 'B')}
        with self.assertRaises(ValueError):
            comparison(rows)


if __name__ == '__main__':
    unittest.main()
