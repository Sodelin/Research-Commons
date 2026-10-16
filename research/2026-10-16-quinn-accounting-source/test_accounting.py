"""Finite synthetic controls; never import or execute the analyzed script."""
from dataclasses import replace
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
import hashlib
import json
import tempfile
import unittest
import zipfile
from accounting import Artifact, BooleanRaster, Event, Grid, Registry, STAGES, missing_envelope, threshold_decisions, weighted_sum
from source_contract import ARCHIVE_SHA256, ORIGINAL_SHA256, inspect_pinned_quinn, inspect_python

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'source' / 'make_viewsheds_gdal_code_share.py.original.txt'

def grid(mask=(True, True, False)):
    return Grid('fixture-grid-with-declared-CRS-and-transform', len(mask), 1, mask)

def artifact(g, cells=(1, 0, 0), **changes):
    return replace(Artifact('a' * 64, BooleanRaster(g, cells), True, True, True, True, True), **changes)

def event(identity, row='a', kind='attempt', **changes):
    return Event(identity, row, changes.pop('run_id', 'run-1'), changes.pop('config_id', 'config-1'), kind, **changes)

def validate(registry, row='a', cells=(1, 0, 0)):
    for stage in STAGES:
        registry.record(event(row + '-' + stage, row, 'stage', stage=stage, exit_code=0))
    registry.record(event(row + '-artifact', row, 'artifact', artifact=artifact(registry.grid, cells)))

class SourceControls(unittest.TestCase):
    def test_exact_archive_member_and_original_bytes(self):
        raw = SOURCE.read_bytes()
        archive = (SOURCE.parent / 'gh-77-165-2022-supplement.zip').read_bytes()
        self.assertEqual(hashlib.sha256(archive).hexdigest(), ARCHIVE_SHA256)
        with zipfile.ZipFile(SOURCE.parent / 'gh-77-165-2022-supplement.zip') as z:
            self.assertEqual(z.read('make_viewsheds_gdal_code_share.py'), raw)
        self.assertEqual(hashlib.sha256(raw).hexdigest(), ORIGINAL_SHA256)
        self.assertEqual((len(raw), raw.count(b'\r\n')), (3705, 82))

    def test_static_contract_positions_and_distinct_curvatures(self):
        report = inspect_pinned_quinn(SOURCE.read_bytes())
        self.assertEqual([c['line'] for c in report['system_calls']], [52, 56, 63, 67])
        self.assertEqual([c['line'] for c in report['remove_calls']], [59, 70])
        self.assertEqual(set(report['CSV_fields']), {'X', 'Y', 'TARGET_FID', 'AADT'})
        self.assertEqual(report['source_curvature_literals'], ['0.85714'])
        self.assertEqual(report['paper_curvature_literal'], '0.85417')
        self.assertEqual(report['finally_counters'][0]['name'], 'itemsProcessed')
        self.assertEqual([row['name'] for row in report['row_extractions_before_try']], ['xCoord', 'yCoord', 'id', 'aadt'])
        self.assertFalse(report['published_run_failure_established'])
        self.assertFalse(report['analyzed_source_executed'])

    def test_hash_mismatch_rejected_before_parse(self):
        with self.assertRaises(ValueError):
            inspect_pinned_quinn(SOURCE.read_bytes() + b'\n')

    def test_side_effect_fixture_is_only_parsed(self):
        with tempfile.TemporaryDirectory() as directory:
            sentinel = Path(directory) / 'NEVER_CREATED'
            raw = ('from pathlib import Path\nPath(' + repr(str(sentinel)) + ').write_text("executed")\nraise RuntimeError("must not run")\n').encode()
            report = inspect_python(raw, hashlib.sha256(raw).hexdigest())
            self.assertTrue(report['AST_only'])
            self.assertFalse(sentinel.exists())

class RegistryControls(unittest.TestCase):
    def setUp(self):
        self.registry = Registry(('a', 'b', 'c'), 'run-1', 'config-1', grid())

    def test_missing_and_attempted_are_pending_not_validated(self):
        self.registry.record(event('attempt-a'))
        snap = self.registry.snapshot()
        self.assertEqual(snap['attempted'], ['a'])
        self.assertEqual(snap['pending'], ['a', 'b', 'c'])
        self.assertFalse(snap['all_expected_validated'])

    def test_all_stages_and_artifact_required(self):
        for stage in STAGES:
            self.registry.record(event(stage, kind='stage', stage=stage, exit_code=0))
            self.assertEqual(self.registry.status('a'), 'pending')
        self.registry.record(event('artifact', kind='artifact', artifact=artifact(grid())))
        self.assertEqual(self.registry.status('a'), 'validated')

    def test_artifact_alone_never_counts_as_process(self):
        self.registry.record(event('artifact', kind='artifact', artifact=artifact(grid())))
        self.assertEqual(self.registry.snapshot()['attempted'], [])
        self.assertEqual(self.registry.status('a'), 'pending')

    def test_nonzero_latches_despite_later_zero_and_valid_artifact(self):
        self.registry.record(event('bad', kind='stage', stage=STAGES[0], exit_code=1))
        validate(self.registry)
        self.assertEqual(self.registry.status('a'), 'failed')

    def test_unconfirmed_exit_is_pending(self):
        self.registry.record(event('unconfirmed', kind='stage', stage=STAGES[0], exit_code=None))
        for stage in STAGES[1:]:
            self.registry.record(event(stage, kind='stage', stage=stage, exit_code=0))
        self.registry.record(event('artifact', kind='artifact', artifact=artifact(grid())))
        self.assertEqual(self.registry.status('a'), 'pending')

    def test_stale_run_and_wrong_configuration_fail(self):
        for field in ('run_id', 'config_id'):
            with self.subTest(field=field):
                reg = Registry(('a',), 'run-1', 'config-1', grid())
                reg.record(event('stale', **{field: 'other'}))
                validate(reg)
                self.assertEqual(reg.status('a'), 'failed')

    def test_idempotent_and_conflicting_replay(self):
        e = event('one')
        self.assertTrue(self.registry.record(e))
        self.assertFalse(self.registry.record(e))
        with self.assertRaises(ValueError):
            self.registry.record(replace(e, row_id='b'))
        self.assertEqual(self.registry.status('a'), 'failed')
        self.assertEqual(self.registry.status('b'), 'failed')
        with self.assertRaises(ValueError):
            self.registry.validated_rasters()

    def test_unknown_id_blocks_global_acceptance(self):
        with self.assertRaises(ValueError):
            self.registry.record(event('alien', row='outside'))
        for row in ('a', 'b', 'c'):
            validate(self.registry, row)
        self.assertFalse(self.registry.snapshot()['all_expected_validated'])

    def test_duplicate_or_empty_expected_universe_rejected(self):
        for ids in (('a', 'a'), (), 'abc'):
            with self.subTest(ids=ids), self.assertRaises(ValueError):
                Registry(ids, 'r', 'c', grid())

    def test_bad_artifact_each_validation_and_hash(self):
        changes = [{name: False} for name in ('checksum_checked', 'grid_checked', 'crs_checked', 'nodata_checked', 'binary_checked')]
        changes += [{'sha256': 'bad'}, {'raster': BooleanRaster(Grid('wrong', 3, 1, (True, True, False)), (1, 0, 0))}]
        for change in changes:
            with self.subTest(change=change):
                reg = Registry(('a',), 'run-1', 'config-1', grid())
                reg.record(event('bad', kind='artifact', artifact=artifact(grid(), **change)))
                self.assertEqual(reg.status('a'), 'failed')

    def test_partition_is_complete_disjoint_and_attempted_orthogonal(self):
        validate(self.registry, 'a')
        self.registry.record(event('bad-b', 'b', 'stage', stage='weight', exit_code=-9))
        snap = self.registry.snapshot()
        self.assertEqual([snap[k] for k in ('validated', 'failed', 'pending')], [['a'], ['b'], ['c']])
        self.assertEqual(snap['attempted'], ['a', 'b'])
        self.assertEqual(sum(len(snap[k]) for k in ('validated', 'failed', 'pending')), 3)

    def test_arbitrary_receipt_arrival_order_preserves_validation(self):
        events = [event(stage, kind='stage', stage=stage, exit_code=0) for stage in STAGES]
        events.append(event('artifact', kind='artifact', artifact=artifact(grid())))
        for order in permutations(events):
            reg = Registry(('a',), 'run-1', 'config-1', grid())
            for receipt in order:
                reg.record(receipt)
            self.assertTrue(reg.snapshot()['all_expected_validated'])

    def test_malformed_exit_and_unknown_stage_fail(self):
        for stage, code in (('viewshed', True), ('viewshed', 0.0), ('unknown', 0)):
            with self.subTest(stage=stage, code=code):
                reg = Registry(('a',), 'run-1', 'config-1', grid())
                reg.record(event('bad', kind='stage', stage=stage, exit_code=code))
                self.assertEqual(reg.status('a'), 'failed')

class ExactArithmeticControls(unittest.TestCase):
    def test_partitions_and_reorder_above_uint32(self):
        g = grid()
        rasters = {'a': BooleanRaster(g, (1, 0, 1)), 'b': BooleanRaster(g, (1, 1, 0)), 'c': BooleanRaster(g, (0, 1, 0))}
        weights = {'a': 2**64 + 9, 'b': 2**32 + 7, 'c': 13}
        expected = (2**64 + 2**32 + 16, 2**32 + 20, None)
        for order in permutations(rasters):
            self.assertEqual(weighted_sum(weights, rasters, g, [[row] for row in order]), expected)
        self.assertEqual(weighted_sum(weights, rasters, g, [('b', 'a'), ('c',)]), expected)

    def test_invalid_weights(self):
        g = grid()
        for weight in (-1, 0.5, True, Fraction(1, 2), '1'):
            with self.subTest(weight=weight), self.assertRaises(ValueError):
                weighted_sum({'a': weight}, {'a': BooleanRaster(g, (1, 0, 0))}, g)

    def test_invalid_cells_even_at_masked_positions(self):
        for cells in ((1, 0, 2), (1, 0, -1), (1, 0, 0.0), (1, 0)):
            with self.subTest(cells=cells), self.assertRaises(ValueError):
                BooleanRaster(grid(), cells)

    def test_grid_and_mask_mismatch(self):
        for other in (Grid('other', 3, 1, (True, True, False)), grid((True, False, False))):
            with self.assertRaises(ValueError):
                weighted_sum({'a': 1}, {'a': BooleanRaster(other, (1, 0, 0))}, grid())

    def test_bad_partition_or_weight_key_binding(self):
        g = grid(); rasters = {'a': BooleanRaster(g, (1, 0, 0))}
        for parts in ([], [('a', 'a')], [('b',)]):
            with self.subTest(parts=parts), self.assertRaises(ValueError):
                weighted_sum({'a': 1}, rasters, g, parts)
        with self.assertRaises(ValueError):
            weighted_sum({'b': 1}, rasters, g)

    def test_missing_envelope_includes_failed_and_pending(self):
        reg = Registry(('a', 'b', 'c'), 'run-1', 'config-1', grid())
        validate(reg)
        reg.record(event('bad-b', 'b', 'stage', stage='viewshed', exit_code=2))
        env = missing_envelope(reg, {'a': 5, 'b': 7, 'c': 11})
        self.assertEqual(env, {'lower': (5, 0, None), 'upper': (23, 18, None), 'unvalidated_ids': ('b', 'c'), 'unvalidated_weight': 18})

    def test_exhaustive_completion_envelope_and_sharp_endpoints(self):
        g = grid((True, True, True))
        reg = Registry(('a', 'b', 'c'), 'run-1', 'config-1', g)
        validate(reg, cells=(1, 0, 1))
        weights = {'a': 2**32 + 1, 'b': 7, 'c': 13}
        env = missing_envelope(reg, weights)
        actual = []
        for bits in product((0, 1), repeat=6):
            rasters = {'a': BooleanRaster(g, (1, 0, 1)), 'b': BooleanRaster(g, bits[:3]), 'c': BooleanRaster(g, bits[3:])}
            values = weighted_sum(weights, rasters, g)
            actual.append(values)
            self.assertTrue(all(low <= value <= high for low, value, high in zip(env['lower'], values, env['upper'])))
        self.assertEqual(tuple(min(row[i] for row in actual) for i in range(3)), env['lower'])
        self.assertEqual(tuple(max(row[i] for row in actual) for i in range(3)), env['upper'])

    def test_threshold_ties_and_rational_thresholds(self):
        env = {'lower': (5, 0, None), 'upper': (5, 18, None)}
        self.assertEqual(threshold_decisions(env, 5), ('YES', 'UNKNOWN', 'MASKED'))
        self.assertEqual(threshold_decisions(env, 5, strict=True), ('NO', 'UNKNOWN', 'MASKED'))
        self.assertEqual(threshold_decisions(env, 18), ('NO', 'UNKNOWN', 'MASKED'))
        self.assertEqual(threshold_decisions(env, 18, strict=True), ('NO', 'NO', 'MASKED'))
        self.assertEqual(threshold_decisions(env, Fraction(11, 2)), ('NO', 'UNKNOWN', 'MASKED'))
        with self.assertRaises(ValueError):
            threshold_decisions(env, 5.0)

    def test_threshold_decisions_sound_over_all_completions(self):
        env = {'lower': (2, 7), 'upper': (5, 11)}
        for strict, threshold in product((False, True), (1, 2, 3, 5, 7, 11, 12)):
            decisions = threshold_decisions(env, threshold, strict)
            for i, decision in enumerate(decisions):
                outcomes = {value > threshold if strict else value >= threshold for value in range(env['lower'][i], env['upper'][i] + 1)}
                self.assertEqual(decision, 'YES' if outcomes == {True} else 'NO' if outcomes == {False} else 'UNKNOWN')

    def test_malformed_envelope_rejected(self):
        cases = [((1,), ()), ((None,), (1,)), ((1,), (None,)), ((5,), (4,)),
                 ((-1,), (0,)), ((0.0,), (1,)), ((True,), (1,))]
        for low, high in cases:
            with self.subTest(low=low, high=high), self.assertRaises(ValueError):
                threshold_decisions({'lower': low, 'upper': high}, 1)

    def test_zero_weights_and_no_validated_rows(self):
        reg = Registry(('a', 'b'), 'run-1', 'config-1', grid())
        env = missing_envelope(reg, {'a': 0, 'b': 0})
        self.assertEqual(env['lower'], (0, 0, None))
        self.assertEqual(env['upper'], (0, 0, None))
        self.assertFalse(reg.snapshot()['all_expected_validated'])

if __name__ == '__main__':
    unittest.main(verbosity=2)
