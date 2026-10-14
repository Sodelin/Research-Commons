"""Run only new namespace controls and successor final-evidence gates."""
import hashlib
import json
from pathlib import Path
import sys
import unittest

import test_namespace_resolution
import test_namespace_final_gates


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    names = ['namespace_resolution.py', 'build_support_namespace.py',
             'audit_support_namespace.py', 'capture_final_namespace.py',
             'lakefile.namespace.lean', 'run_provider_namespace_batches.py',
             'test_namespace_resolution.py', 'test_namespace_final_gates.py',
             'test_namespace_controls.py']
    print(json.dumps(dict(scope='synthetic namespace and final-evidence controls only',
        compiler_invocations=0, executed_source_pins={name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                                                    for name in names})), flush=True)
    suite = unittest.TestSuite(unittest.defaultTestLoader.loadTestsFromModule(module)
                               for module in [test_namespace_resolution, test_namespace_final_gates])
    outcome = unittest.TextTestRunner(verbosity=2).run(suite)
    sys.exit(0 if outcome.wasSuccessful() else 1)
