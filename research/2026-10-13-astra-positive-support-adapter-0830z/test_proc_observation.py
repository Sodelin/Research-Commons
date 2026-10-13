#!/usr/bin/env python3
"""Bounded monitor regression using an owned Python child; never invokes Lean."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

import diagnose_thread_failure as diagnostic


child = subprocess.Popen([sys.executable, '-c', "print('READY', flush=True); input()"],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
try:
    assert child.stdout.readline() == 'READY\n'
    found = list(diagnostic.matching_children(os.getpid(), sys.executable))
    assert [int(path.name) for path in found] == [child.pid]
    assert not list(diagnostic.matching_children(os.getpid(), '/not/the/child/executable'))
    assert not list(diagnostic.matching_children(child.pid, sys.executable))
    for name in ['status', 'limits', 'maps', 'smaps_rollup']:
        assert (found[0] / name).read_text()
    child.communicate('\n', timeout=2)
    assert child.returncode == 0
    assert not list(diagnostic.matching_children(os.getpid(), sys.executable))
    print(json.dumps({'status': 'PASS', 'child_identity_and_proc_files': True,
                      'executable_and_parent_filters': True, 'reaped_child_absent': True,
                      'diagnostic_sha256': hashlib.sha256(Path(diagnostic.__file__).read_bytes()).hexdigest(),
                      'test_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}))
finally:
    if child.poll() is None:
        child.kill()
        child.wait()
