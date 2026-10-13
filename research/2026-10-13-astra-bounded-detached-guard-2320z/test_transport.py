"""Stdlib dummy jobs only. Never invokes Lean, Lake, Git or production launch.

Set ASTRA_DETACHED_TEST_EVIDENCE to a fresh directory to preserve all dummy
profiles, process records and actual frozen-guard receipts after the tests.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import unittest
from unittest import mock

import detached_transport as transport

HERE = Path(__file__).resolve().parent
GUARD = HERE.parent / '2026-10-13-astra-unified-solver-0645z/guard.py'
GUARD_SHA = 'f6c606646239ff1bc5dccac80c154a2095a6b2f7f60e8b557a5b195544fadcb3'


def wait_for(predicate, seconds=8):
    end = time.monotonic() + seconds
    while time.monotonic() < end:
        if predicate():
            return
        time.sleep(0.025)
    raise AssertionError('bounded observation deadline expired')


def process_running(pid):
    try:
        return (Path('/proc') / str(pid) / 'stat').read_text().rsplit(') ', 1)[1].split()[0] not in ('Z', 'X')
    except FileNotFoundError:
        return False


class TransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if transport.digest(GUARD) != GUARD_SHA:
            raise RuntimeError('frozen guard source differs')
        cls.root = Path(os.environ['ASTRA_DETACHED_TEST_EVIDENCE']).resolve()
        cls.root.mkdir(parents=True, exist_ok=False)
        print(json.dumps(dict(executed_sources={name: transport.digest(HERE / name)
                         for name in ['detached_transport.py', 'one_guard.py', 'test_transport.py']},
                              frozen_guard_sha256=GUARD_SHA)), flush=True)

    def setUp(self):
        self.case = self.root / self._testMethodName
        self.case.mkdir()
        self.directory = self.case / 'launch'
        self.profile = None

    def tearDown(self):
        # Tests may fail, but their already-launched guard owns a 10s wall cap.
        # Identity checked SIGINT is the only early cleanup signal used here.
        if self.profile and (self.directory / 'LAUNCH.json').exists():
            record = transport._load(self.profile, self.directory)
            if transport.alive(record):
                if not (self.directory / 'STOP-REQUEST.json').exists():
                    try:
                        self.wait_ready()
                        transport.stop(self.profile, self.directory)
                    except (OSError, transport.Refused, AssertionError):
                        pass
                wait_for(lambda: not transport.alive(record), seconds=12)

    def start(self, body):
        script = self.case / 'dummy.py'
        script.write_text(body)
        output = self.case / 'guard-output'
        child = [sys.executable, '-B', str(script)]
        command = [sys.executable, str(GUARD), '--out', str(output), '--cwd', str(self.case),
                   '--wall', '10', '--cpu', '5', '--memory-mib', '128', '--file-mib', '4', '--'] + child
        self.profile = dict(name='DUMMY_TEST_ONLY', command=command, child_command=child,
                            batch_output=str(output), cwd=str(self.case),
                            python_exe=str(Path(sys.executable).resolve()), guard_sha256=GUARD_SHA,
                            environment={'PATH': '/usr/bin:/bin', 'LANG': 'C.UTF-8'},
                            limits=dict(cpu_seconds=5, wall_seconds=10, address_space_bytes=128 * 1024**2,
                                        file_bytes=4 * 1024**2, disk_floor=8 * 1024**3,
                                        ram_floor=1024**3, cgroup_stop=4 * 1024**3))
        profile_path = self.case / 'profile.json'
        profile_path.write_text(json.dumps(self.profile))
        bootstrap = (
            'import json,sys;from pathlib import Path;'
            'import detached_transport as t;'
            'p=json.loads(Path(sys.argv[1]).read_text());'
            't.launch(p,Path(sys.argv[2]),{"dummy_preexisting": "recorded-before-Popen"})'
        )
        # Parent bootstrap actually exits while the independent guard remains.
        boot = subprocess.run([sys.executable, '-B', '-c', bootstrap, str(profile_path), str(self.directory)],
                              cwd=HERE, capture_output=True, timeout=3)
        (self.case / 'bootstrap.stdout').write_bytes(boot.stdout)
        (self.case / 'bootstrap.stderr').write_bytes(boot.stderr)
        transport.write_new(self.case / 'bootstrap.json', dict(exit_code=boot.returncode))
        self.assertEqual(boot.returncode, 0, boot.stderr.decode())
        return output

    def closed(self, output):
        record = transport._load(self.profile, self.directory)
        wait_for(lambda: not transport.alive(record) and (output / 'RECEIPT.json').exists())
        return transport.read_receipt(self.profile, self.directory)

    def wait_ready(self):
        pid = transport._load(self.profile, self.directory)['identity']['pid']
        wait_for(lambda: (Path('/proc') / str(pid) / 'wchan').read_text().strip() == 'hrtimer_nanosleep')

    def test_bootstrap_exit_persists_without_success_promotion(self):
        output = self.start('import time\nfrom pathlib import Path\ntime.sleep(0.4)\nPath("done").write_text("done")\n')
        state = transport.status(self.profile, self.directory)
        self.assertEqual(state['status'], 'RUNNING')
        self.assertFalse(state['completion_verified'])
        self.assertFalse((output / 'RECEIPT.json').exists())
        result = self.closed(output)
        self.assertEqual(result['status'], 'GUARD_RECEIPT_SUCCESS')
        self.assertIsNone(result['guard_process_exit_code'])
        self.assertTrue((self.case / 'done').exists())

    def test_pidfd_stop_cleans_owned_stopped_descendant(self):
        output = self.start('import subprocess,sys,os,signal,time,json\nfrom pathlib import Path\n'
                            'p=subprocess.Popen([sys.executable,"-c","import time;time.sleep(20)"])\n'
                            'os.kill(p.pid,signal.SIGSTOP)\n'
                            'Path("descendant.json").write_text(json.dumps({"pid":p.pid}))\n'
                            'time.sleep(20)\n')
        path = self.case / 'descendant.json'
        wait_for(path.exists)
        pid = json.loads(path.read_text())['pid']
        self.assertTrue(process_running(pid))
        self.wait_ready()
        self.assertEqual(transport.stop(self.profile, self.directory)['status'], 'SIGINT_SENT_COMPLETION_UNKNOWN')
        result = self.closed(output)
        self.assertEqual(result['status'], 'GUARD_RECEIPT_NOT_SUCCESS')
        receipt = json.loads((output / 'RECEIPT.json').read_text())
        self.assertEqual(receipt['error']['type'], 'KeyboardInterrupt')
        self.assertTrue(result['requested_stop'])
        wait_for(lambda: not process_running(pid))

    def test_stale_starttime_refuses_signal(self):
        output = self.start('import time\ntime.sleep(2)\n')
        wait_for(lambda: (output / 'stderr').exists())
        path = self.directory / 'LAUNCH.json'
        original = path.read_bytes()
        altered = json.loads(original)
        altered['identity']['starttime_ticks'] += 1
        path.write_text(json.dumps(altered))
        try:
            with self.assertRaises(transport.Refused):
                transport.stop(self.profile, self.directory)
            self.assertFalse((self.directory / 'STOP-REQUEST.json').exists())
        finally:
            path.write_bytes(original)
        self.assertEqual(transport.status(self.profile, self.directory)['status'], 'RUNNING')
        self.wait_ready()
        transport.stop(self.profile, self.directory)
        self.assertEqual(self.closed(output)['status'], 'GUARD_RECEIPT_NOT_SUCCESS')

    def test_pre_monitor_readiness_refuses_signal(self):
        output = self.start('import time\ntime.sleep(2)\n')
        wait_for(lambda: (output / 'stderr').exists())
        # Controlled negative observation models the Popen-before-assignment
        # window. It is not misreported as an actual kernel wait-channel trace.
        with mock.patch.object(transport, 'monitor_sleep',
                               side_effect=transport.Refused('test-only pre-monitor state')):
            with mock.patch.object(transport.signal, 'pidfd_send_signal') as sent:
                with self.assertRaises(transport.Refused):
                    transport.stop(self.profile, self.directory)
                sent.assert_not_called()
        self.assertFalse((self.directory / 'STOP-REQUEST.json').exists())
        self.assertEqual(transport.status(self.profile, self.directory)['status'], 'RUNNING')
        # Now observe the real kernel wait channel before a real pidfd stop.
        self.wait_ready()
        transport.stop(self.profile, self.directory)
        self.assertEqual(self.closed(output)['status'], 'GUARD_RECEIPT_NOT_SUCCESS')

    def test_builder_failure_is_not_success(self):
        output = self.start('import time\ntime.sleep(0.2)\nraise SystemExit(3)\n')
        result = self.closed(output)
        self.assertEqual(result['builder_exit_code'], 3)
        self.assertEqual(result['status'], 'GUARD_RECEIPT_NOT_SUCCESS')

    def test_requested_stop_never_promotes_child_zero(self):
        output = self.start('import time\ntime.sleep(0.2)\n')
        self.assertEqual(self.closed(output)['status'], 'GUARD_RECEIPT_SUCCESS')
        # Deterministic model of a stop-request/child-exit race. No changed guard
        # receipt is presented as execution: this additive test marker is labelled.
        transport.write_new(self.directory / 'STOP-REQUEST.json', dict(test_only=True,
                            reason='model pending stop at child-zero boundary'))
        self.assertEqual(transport.read_receipt(self.profile, self.directory)['status'],
                         'GUARD_RECEIPT_NOT_SUCCESS')

    def test_missing_pidfd_is_refused_before_launch(self):
        with mock.patch.object(transport.os, 'pidfd_open', create=False):
            original = transport.os.pidfd_open
            del transport.os.pidfd_open
            try:
                with self.assertRaises(transport.Refused):
                    transport.launch({}, self.directory, {})
                self.assertFalse(self.directory.exists())
            finally:
                transport.os.pidfd_open = original


if __name__ == '__main__':
    unittest.main()
