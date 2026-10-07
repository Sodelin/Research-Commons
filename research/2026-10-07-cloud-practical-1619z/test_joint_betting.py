"""Bounded deterministic mathematical/interface controls; no sampling."""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import copy
import hashlib
import json
import unittest

import joint_betting as jb

BASE = Path(__file__).resolve().parents[2]
OLD = BASE / 'research/2026-10-05-dot-msci-phased-confidence-protocol-controls-1709z/controls/literal_two'
CORE = BASE / 'research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/integration_core.py'


def box(q):
    return {name: [str(q), str(q)] for name in jb.FEATURES}


def plan(direction=None):
    return [{'weight': '1', 'direction': direction or ['1'] + ['0'] * 8}]


class JointBettingControls(unittest.TestCase):
    def test_authentic_old_literal_fixture(self):
        req = json.loads((OLD / 'ANALYSIS-REQUEST.json').read_text())
        rows, extraction = jb.literal_rows(OLD / 'DATASET.json', req['dataset_sha256'],
                                          2, req['selection_sha256'], CORE)
        self.assertEqual(rows, ((1,) * 9, (1, 1, 0, 0, 1, 0, 1, 1, 1)))
        self.assertEqual(extraction['m'], 2)
        result = jb.replay(rows, box(Q(3, 4)), plan())
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertFalse(result['data_confidence_certificate_issued'])

    def test_fixture_identity_rejected(self):
        req = json.loads((OLD / 'ANALYSIS-REQUEST.json').read_text())
        with self.assertRaises(Exception):
            jb.literal_rows(OLD / 'DATASET.json', '0' * 64, 2, req['selection_sha256'], CORE)

    def test_direction_weight_and_budget_guards(self):
        rows = ((1,) * 9,)
        bad = plan(['1', '1'] + ['0'] * 7)
        with self.assertRaises(jb.Invalid):
            jb.replay(rows, box(Q(1, 2)), bad)
        bad = plan(); bad[0]['weight'] = '1/2'
        with self.assertRaises(jb.Invalid):
            jb.replay(rows, box(Q(1, 2)), bad)
        for delta in ('0', '1', '1.0'):
            with self.assertRaises(jb.Invalid):
                jb.replay(rows, box(Q(1, 2)), plan(), delta)

    def test_complete_rows_not_pseudoreplicated(self):
        with self.assertRaises(jb.Invalid):
            jb.replay(((1,) * 9, (1,) * 8), box(Q(1, 2)), plan())
        with self.assertRaises(jb.Invalid):
            jb.replay(((True,) + (1,) * 8,), box(Q(1, 2)), plan())

    def test_first_locus_uses_no_current_outcome(self):
        mu = jb.Interval.point(Q(3, 4))
        for z in (Q(0), Q(1)):
            self.assertEqual(jb.factor(z, mu, Q(0), Q(0), 0), jb.Interval.point(1))

    def test_exact_martingale_on_perfectly_dependent_joint_law(self):
        # Every coordinate is identical at each locus. Independence of the nine
        # features would be false; the conditional-mean identity still holds.
        probability = Q(2, 3)
        directions = [(Q(1),) + (Q(0),) * 8,
                      (Q(1, 2), Q(1, 2)) + (Q(0),) * 7,
                      (Q(1, 2), Q(-1, 2)) + (Q(0),) * 7]
        mu = tuple(jb.Interval.point(probability) for _ in jb.FEATURES)
        for direction in directions:
            projected_mu = jb.project_box(direction, mu)
            for prefix_length in range(4):
                for prefix in product((0, 1), repeat=prefix_length):
                    values = [sum(direction) * v for v in prefix]
                    total, squares = sum(values, Q(0)), sum((v * v for v in values), Q(0))
                    factors = [jb.factor(sum(direction) * v, projected_mu, total, squares,
                                         prefix_length) for v in (0, 1)]
                    self.assertEqual((1 - probability) * factors[0].lo + probability * factors[1].lo, 1)
                    self.assertTrue(all(f.lo == f.hi and Q(1, 2) <= f.lo <= Q(3, 2) for f in factors))

    def test_interval_factor_contains_every_sampled_candidate_grid_point(self):
        direction = (Q(1, 2), Q(-1, 2)) + (Q(0),) * 7
        bounds = (jb.Interval(Q(1, 4), Q(3, 4)),) * 9
        enclosure = jb.factor(Q(1, 2), jb.project_box(direction, bounds), Q(1, 2), Q(1, 4), 2)
        for x, y in product((Q(1, 4), Q(1, 2), Q(3, 4)), repeat=2):
            value = jb.factor(Q(1, 2), jb.Interval.point((x - y) / 2), Q(1, 2), Q(1, 4), 2)
            self.assertLessEqual(enclosure.lo, value.lo)
            self.assertLessEqual(value.hi, enclosure.hi)

    def test_joint_direction_can_exclude_without_marginal_tail_union(self):
        # Algebraic row controls only, not a generated source dataset. Direction
        # couples two coordinates from each original-size locus vector.
        rows = (((1, 0) + (0,) * 7),) * 40
        direction = ['1/2', '-1/2'] + ['0'] * 7
        result = jb.replay(rows, box(Q(1, 2)), plan(direction))
        self.assertEqual(result['status'], 'CONDITIONAL_MEAN_BOX_EXCLUDED')
        self.assertGreaterEqual(Q(result['best_prefix_mixture_lower']), 20)
        self.assertLessEqual(result['prefix_processed'], 40)
        self.assertFalse(result['physical_source_box_excluded'])

    def test_resource_stop_is_unknown(self):
        rows = ((1,) * 9,) * 40
        result = jb.replay(rows, box(Q(7, 13)), plan(), max_bits=16)
        self.assertEqual(result['status'], 'UNKNOWN')
        self.assertEqual(result['arithmetic_refusal'], 'ARITHMETIC_BITS')
        self.assertLess(result['prefix_processed'], result['loci_supplied'])

    def test_full_domain_mean_box_stays_unknown(self):
        bounds = {name: ['0', '1'] for name in jb.FEATURES}
        result = jb.replay(((1,) * 9,) * 40, bounds, plan())
        self.assertEqual(result['status'], 'UNKNOWN')

    def test_plan_hash_binds_direction_change(self):
        rows = ((1,) * 9,)
        first = jb.replay(rows, box(Q(1, 2)), plan())
        changed = jb.replay(rows, box(Q(1, 2)), plan(['-1'] + ['0'] * 8))
        self.assertNotEqual(first['predeclared_strategy_plan_sha256'], changed['predeclared_strategy_plan_sha256'])


if __name__ == '__main__':
    unittest.main(verbosity=2)
