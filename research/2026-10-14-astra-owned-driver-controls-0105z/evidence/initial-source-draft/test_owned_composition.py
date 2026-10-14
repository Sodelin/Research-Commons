#!/usr/bin/env python3
"""Synthetic owned-driver controls; no builder, process or object authentication."""
import argparse
import base64
from contextlib import contextmanager
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import unittest
from unittest.mock import patch

from synthetic_fixtures import Owned, external_fixture, sha, write

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DRIVER_ROOT = ROOT / 'research/2026-10-14-astra-detached-owned-batch-0025z'
SUPPORT = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z'
PINNED = {
    DRIVER_ROOT / 'one_owned_batch.py': '157991882a6773c580fb8dcc226296b34d552bca39f09605a947fc55d3c727d7',
    DRIVER_ROOT / 'SOURCE-PINS.json': '0b1c54a9e69ae368dc25fbfcd5687bf31f228c9cd70de20b6dce7a61c1e225ff',
    ROOT / 'research/2026-10-13-astra-bounded-detached-guard-2320z/detached_transport.py':
        '4c396546825b108f48fe9633a0df576f78fb8af77830233c77751db1e9e56db1',
    SUPPORT / 'capture_batch.py': 'c748a27508cec46ee243ebc77ab256f515f87fbbb0e5c8c2b28d654d22febad4',
    SUPPORT / 'run_provider_namespace_batches.py': 'b58e7862e1d81f0667098f14f22475d282a096cd005620636b2db6bd6126ad2f',
}
OUTPUT = None
driver = transport = capture = helper = None
external = support = None
ATTEMPTED_EFFECTS = []


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def forbidden(*args, **kwargs):
    ATTEMPTED_EFFECTS.append(repr(args))
    raise AssertionError('Synthetic controls must never create or signal a process')


class Controls(unittest.TestCase):
    def setUp(self):
        self.root = OUTPUT / self._testMethodName
        self.root.mkdir()
        self.proc = self.root / 'synthetic-proc'; self.proc.mkdir()
        real_path = Path
        def controlled_path(*args):
            return self.proc if args == ('/proc',) else real_path(*args)
        self.enterContext(patch.object(driver, 'Path', controlled_path))
        self.enterContext(patch.object(driver, 'check_pins', return_value={'synthetic_fixture': True}))
        self.enterContext(patch.multiple(driver, HERE=self.root, SUPPORT=support, EXTERNAL=external,
                                        STATE=self.root / 'absent-owned-state'))
        # Reuse the already tested process transport. Only identity observations
        # are injected; actual read_receipt/hash/status interpretation is exercised.
        self.enterContext(patch.object(transport, '_load', return_value={'synthetic_identity': True}))
        self.enterContext(patch.object(transport, 'alive', return_value=False))
        self.journal = []

    def tearDown(self):
        write(self.root / 'CONTROL-SCOPE.json', dict(synthetic_only=True, journal=self.journal,
            actual_guard_executed=False, actual_compiler_executed=False,
            production_source_objects_authenticated=False))

    def child_root(self, name):
        root = self.root / name; root.mkdir()
        return root

    def preliminary(self, profile=None, output=None):
        return driver.preliminary(profile or dict(batch_id=1, expected_start_index=0),
            output or self.root / 'absent-guard-output', capture, helper)

    @contextmanager
    def changed_external(self, path, replacement=None, missing=False):
        original = path.read_bytes()
        withheld = path.with_name(path.name + '.synthetic-withheld')
        self.journal.append(dict(path=str(path.relative_to(external.parent)),
            original_utf8=original.decode(), replacement_utf8=None if missing else replacement.decode(),
            missing=missing, original_sha256=sha(original)))
        if missing:
            path.rename(withheld)
        else:
            path.write_bytes(replacement)
        try:
            yield
        finally:
            if missing:
                withheld.rename(path)
            else:
                path.write_bytes(original)

    def finish(self, fixture):
        with patch.object(driver, 'STATE', fixture.state):
            result = driver.finish(transport, capture, helper, fixture.profile,
                                   fixture.output, fixture.directory)
        self.assertIsNone(result['guard_process_exit_code'])
        for name in ['new_adapter_compilation_requested', 'actual_final_lake_target_run',
                     'final_axiom_audit_completed', 'full1613_aggregate_compiled',
                     'physical_representative_claimed', 'compiler_objects_independently_reaudited']:
            self.assertIs(result[name], False)
        self.assertTrue(result['no_automatic_next_batch'])
        self.assertTrue((fixture.directory / 'OWNED-STATE-DELTA.json').is_file())
        self.journal.append(dict(case=fixture.root.name, status=result['status'],
            synthetic_result_only=True, provider_batch_verified=result['provider_batch_verified']))
        return result

    def test_complete_metadata_is_only_a_preliminary_gate(self):
        result = self.preliminary()
        self.assertEqual(result['status'], 'PRELIMINARY_METADATA_REFUSAL_GATE_ONLY')
        self.assertFalse(result['external_objects_authenticated'])
        self.assertFalse(driver.STATE.exists())
        self.assertFalse((self.root / 'absent-guard-output').exists())

    def test_external_missing_failed_or_orphan_metadata_refuses(self):
        for suffix in ['json', 'stderr']:
            with self.subTest(missing=suffix), self.changed_external(external / ('0000.' + suffix), missing=True):
                with self.assertRaisesRegex(ValueError, 'incomplete or orphaned'):
                    self.preliminary()
        path = external / '0000.json'; row = json.loads(path.read_text()); row['exit_code'] = 1
        with self.changed_external(path, json.dumps(row).encode()):
            with self.assertRaisesRegex(ValueError, 'successful set'):
                self.preliminary()
        orphan = external / '9999.json'; orphan.write_bytes(b'{"synthetic_orphan":true}')
        try:
            with self.assertRaisesRegex(ValueError, 'incomplete or orphaned'):
                self.preliminary()
        finally:
            orphan.rename(self.root / 'PRESERVED-SYNTHETIC-ORPHAN.json')
        with self.changed_external(external / 'PLAN.json', b'{"wrong_synthetic_plan":true}'):
            with self.assertRaisesRegex(ValueError, 'selected plan differs'):
                self.preliminary()
        self.assertFalse(driver.STATE.exists())

    def test_small_scheduler_occupies_lane(self):
        process = self.proc / '999999001'; process.mkdir()
        (process / 'stat').write_text('999999001 (synthetic) S 0 0 0\n')
        (process / 'cmdline').write_bytes(b'python3\0one_batch_small.py\0launch\0')
        with self.assertRaisesRegex(ValueError, 'lane occupied'):
            self.preliminary()
        self.assertFalse(driver.STATE.exists())

    def test_changed_prior_checkpoint_refuses(self):
        for target in ['receipt', 'log', 'source', 'plan', 'namespace', 'delta']:
            with self.subTest(target=target):
                fixture = Owned(self.child_root(target), driver)
                prior = fixture.previous_finish(capture, helper)
                paths = dict(receipt=fixture.state / '0000.json', log=fixture.state / '0000.stderr',
                    source=fixture.source_path(0), plan=fixture.state / 'PLAN.json',
                    namespace=fixture.state / 'NAMESPACE-RESOLUTION.json', delta=prior / 'OWNED-STATE-DELTA.json')
                path = paths[target]; original = path.read_bytes()
                path.write_bytes(original + b'\nCHANGED_SYNTHETIC_BYTES')
                with patch.multiple(driver, HERE=fixture.root, STATE=fixture.state):
                    with self.assertRaisesRegex(ValueError, 'changed'):
                        self.preliminary(fixture.profile, fixture.root / 'absent-output')
                self.assertEqual(path.read_bytes(), original + b'\nCHANGED_SYNTHETIC_BYTES')

    def test_unchanged_prior_checkpoint_can_pass_preliminary_only(self):
        fixture = Owned(self.child_root('unchanged'), driver)
        fixture.previous_finish(capture, helper)
        with patch.multiple(driver, HERE=fixture.root, STATE=fixture.state):
            result = self.preliminary(fixture.profile, fixture.root / 'absent-output')
        self.assertFalse(result['external_objects_authenticated'])

    def test_fresh_clone_resumed_accounting(self):
        fixture = Owned(self.child_root('mixed'), driver); fixture.successful(capture, helper)
        result = self.finish(fixture)
        self.assertTrue(result['provider_batch_verified'])
        self.assertFalse(result['provider_preparation_complete'])
        self.assertEqual((result['fresh_invocation_count'], result['newly_authenticated_clone_count'],
                          result['resumed_receipts'], result['next_owned_receipt_index']), (1, 1, 1, 3))
        self.assertEqual(result['fresh_invocations'][0]['index'], 2)
        self.assertEqual(result['newly_authenticated_clones'][0]['index'], 1)

    def test_reuse_summary_cannot_conflate_new_clone_and_resumed(self):
        fixture = Owned(self.child_root('bad-reuse'), driver); fixture.successful(capture, helper)
        fixture.terminal([(2, 0)], [1], reuse_summary=1)
        result = self.finish(fixture)
        self.assertFalse(result['provider_batch_verified'])
        self.assertIn('conflates', result['error']['message'])

    def test_failed_and_resource_stopped_batches_preserve_eventless_bytes(self):
        for name, exit_code, stop in [('failed', 1, None), ('wall-stop', 0, 'wall_limit')]:
            with self.subTest(name=name):
                fixture = Owned(self.child_root(name), driver); fixture.checkpoint(capture, helper)
                fixture.row(1, code=1 if exit_code else 0)
                eventless = b'EVENTLESS SYNTHETIC STDERR; NO COMPILER CLAIM\n'
                (fixture.state / '0002.stderr').write_bytes(eventless)
                fixture.source_path(2).parent.mkdir(parents=True, exist_ok=True)
                fixture.source_path(2).write_bytes(fixture.sources[2])
                fixture.terminal([(1, 1 if exit_code else 0)], [], exit_code=exit_code, stop=stop)
                result = self.finish(fixture)
                self.assertFalse(result['provider_batch_verified'])
                self.assertFalse(result['provider_preparation_complete'])
                unverified = result['interrupted_unverified_invocations']
                self.assertEqual(unverified[0]['index'], 2)
                self.assertEqual(base64.b64decode(unverified[0]['outputs']['stderr']['exact_bytes_base64']), eventless)
                delta = json.loads((fixture.directory / 'OWNED-STATE-DELTA.json').read_text())
                self.assertEqual(delta['selected_plan']['sha256'], sha((fixture.state / 'PLAN.json').read_bytes()))
                self.assertEqual(delta['namespace_resolution']['sha256'], sha((fixture.state / 'NAMESPACE-RESOLUTION.json').read_bytes()))
                self.assertEqual(base64.b64decode(delta['changed_files']['0002.stderr']['exact_bytes_base64']), eventless)
                source_key = str(fixture.source_path(2).relative_to(fixture.state))
                self.assertEqual(base64.b64decode(delta['changed_files'][source_key]['exact_bytes_base64']), fixture.sources[2])

    def test_requested_stop_and_guard_error_never_promote_child_zero(self):
        for name in ['requested-stop', 'guard-error']:
            with self.subTest(name=name):
                fixture = Owned(self.child_root(name), driver); fixture.successful(capture, helper)
                if name == 'requested-stop':
                    write(fixture.directory / 'STOP-REQUEST.json', dict(synthetic_only=True))
                else:
                    fixture.terminal([(2, 0)], [1], error={'type':'SyntheticGuardError'})
                with patch.object(capture, 'capture', side_effect=AssertionError('success capture must be bypassed')):
                    result = self.finish(fixture)
                self.assertFalse(result['provider_batch_verified'])
                self.assertEqual(result['builder_exit_code'], 0)
                self.assertFalse((fixture.output / 'MODULE-RECEIPTS.json').exists())
                delta = json.loads((fixture.directory / 'OWNED-STATE-DELTA.json').read_text())
                self.assertIn('0001.json', delta['changed_files'])
                self.assertIn('0002.stderr', delta['changed_files'])

    def test_missing_malformed_receipt_or_capture_mismatch_preserves_delta(self):
        for name in ['missing-receipt', 'malformed-receipt', 'capture-mismatch']:
            with self.subTest(name=name):
                fixture = Owned(self.child_root(name), driver); fixture.successful(capture, helper)
                if name == 'missing-receipt':
                    (fixture.output / 'RECEIPT.json').rename(fixture.root / 'WITHHELD-SYNTHETIC-RECEIPT.json')
                elif name == 'malformed-receipt':
                    (fixture.output / 'RECEIPT.json').write_bytes(b'{not-json')
                else:
                    (fixture.state / '0002.stderr').write_bytes(b'changed synthetic stderr')
                result = self.finish(fixture)
                self.assertFalse(result['provider_batch_verified'])
                self.assertEqual(result['status'], 'UNVERIFIED_CAPTURE_OR_TERMINAL_ERROR')
                self.assertTrue((fixture.directory / 'FINISH.json').is_file())

    def test_short_incomplete_and_over_budget_refuse(self):
        for name in ['short-incomplete', 'over-budget']:
            with self.subTest(name=name):
                fixture = Owned(self.child_root(name), driver); fixture.successful(capture, helper)
                if name == 'short-incomplete':
                    fixture.profile['fresh_budget'] = 2
                else:
                    fixture.row(3); fixture.terminal([(2, 0), (3, 0)], [1])
                result = self.finish(fixture)
                self.assertFalse(result['provider_batch_verified'])
                self.assertIn('short batch' if name == 'short-incomplete' else 'accounting', result['error']['message'])

    def test_completed_provider_may_stop_short_without_final_audit(self):
        fixture = Owned(self.child_root('complete-short'), driver, provider_count=3)
        fixture.successful(capture, helper); fixture.profile['fresh_budget'] = 2
        result = self.finish(fixture)
        self.assertTrue(result['provider_batch_verified'])
        self.assertTrue(result['provider_preparation_complete'])
        self.assertFalse(result['actual_final_lake_target_run'])
        self.assertFalse(result['final_axiom_audit_completed'])


def main():
    global OUTPUT, driver, transport, capture, helper, support, external
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    OUTPUT = args.output.absolute(); OUTPUT.mkdir(parents=True, exist_ok=False)
    initial = {str(path):sha(path.read_bytes()) for path in PINNED}
    if initial != {str(path):pin for path, pin in PINNED.items()}:
        raise ValueError('frozen production/control helper source identity changed')
    for name in ['build_support_namespace', 'build_support', 'build_external_serial', 'build_lean']:
        if name in sys.modules:
            raise ValueError('builder unexpectedly loaded before source-only controls')
    executed = dict(started_utc=datetime.now(timezone.utc).isoformat(), provider_pins=initial,
        test_sources={name:sha((HERE / name).read_bytes()) for name in ['test_owned_composition.py','synthetic_fixtures.py']},
        scope='SYNTHETIC DRIVER/CAPTURE COMPOSITION ONLY; no production authentication, processes or Lean objects.')
    write(OUTPUT / 'EXECUTED-SOURCES.json', executed)
    driver = load('synthetic_owned_driver_under_test', DRIVER_ROOT / 'one_owned_batch.py')
    capture = load('capture_batch', SUPPORT / 'capture_batch.py')
    helper = load('synthetic_owned_delta_helper', SUPPORT / 'run_provider_namespace_batches.py')
    transport = load('synthetic_owned_transport', ROOT / 'research/2026-10-13-astra-bounded-detached-guard-2320z/detached_transport.py')
    fixture_root = OUTPUT / 'shared-synthetic-external'; fixture_root.mkdir()
    support, external = external_fixture(fixture_root)
    with patch.object(subprocess, 'Popen', forbidden), patch.object(subprocess, 'run', forbidden), \
         patch.object(subprocess, 'check_output', forbidden), patch.object(os, 'kill', forbidden), \
         patch.object(os, 'killpg', forbidden), patch.object(signal, 'pidfd_send_signal', forbidden):
        result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Controls))
    unchanged = {str(path):sha(path.read_bytes()) for path in PINNED} == initial
    no_builders = not any(name in sys.modules for name in ['build_support_namespace','build_support','build_external_serial','build_lean'])
    passed = result.wasSuccessful() and unchanged and no_builders and not ATTEMPTED_EFFECTS
    write(OUTPUT / 'TEST-RESULT.json', dict(status='PASS_SYNTHETIC_ONLY' if passed else 'FAIL',
        groups=result.testsRun,
        failures=[dict(test=str(test), traceback=trace) for test, trace in result.failures],
        errors=[dict(test=str(test), traceback=trace) for test, trace in result.errors],
        production_pins_unchanged=unchanged, builders_not_imported=no_builders,
        attempted_process_or_signal_effects=ATTEMPTED_EFFECTS, guard_invocations_from_controls=0,
        outer_resource_guard_separate=True,
        actual_compilers=0, production_object_authentication=False,
        transport_namespace_corpora_repeated=False, finished_utc=datetime.now(timezone.utc).isoformat()))
    return 0 if passed else 1


if __name__ == '__main__':
    raise SystemExit(main())
