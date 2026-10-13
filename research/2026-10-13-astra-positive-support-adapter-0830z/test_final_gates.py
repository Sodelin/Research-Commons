"""Bounded fail-closed checks for final evidence gates; no Lean invocation."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

import audit_support_interface as interface
import capture_final as capture


class FinalGateTests(unittest.TestCase):
    def test_missing_completion_cannot_launch_interface_compiler(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            argv=['audit_support_interface.py']
            for name in ['source-root','external-state','state','mathlib-root','lean-bin']:
                argv.extend(['--'+name,str(root/name)])
            with patch.object(sys,'argv',argv),patch.object(interface.subprocess,'run') as launch:
                with self.assertRaisesRegex(ValueError,'complete provider/adapter receipt'):
                    interface.main()
                launch.assert_not_called()

    def refuse_capture(self,guard,message):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);state=root/'state';state.mkdir();lake=root/'lake';lake.mkdir()
            (state/'PLAN.json').write_text(json.dumps(dict(modules=[])))
            (state/'RESULT.json').write_text(json.dumps(dict(
                status='EXACT_ACCEPTED_PROVIDER_AND_SUPPORT_ADAPTER_VERIFIED',modules=[])))
            recorded=dict(runner_sha256=capture.support.PREVIOUS_PINS['guard.py'],
                          limits=capture.FINAL_LIMITS)
            recorded.update(guard)
            (lake/'RECEIPT.json').write_text(json.dumps(recorded))
            argv=['capture_final.py','--source-root',str(root/'source'),
                  '--state',str(state),'--external-state',str(root/'external'),
                  '--mathlib-root',str(root/'mathlib'),'--lean-bin',str(root/'bin'),
                  '--lake-output',str(lake),'--out',str(root/'export')]
            with patch.object(sys,'argv',argv),patch.object(capture.support,'verify',return_value={}):
                with self.assertRaisesRegex(ValueError,message):capture.main()
            self.assertFalse((root/'export').exists())

    def test_failed_guard_cannot_produce_final_export(self):
        self.refuse_capture(dict(exit_code=-15,stop='cgroup_pressure'),
                            'final Lake invocation did not pass')

    def test_other_successful_command_is_not_a_lake_target_receipt(self):
        self.refuse_capture(dict(exit_code=0,stop=None,command=['python3','-c','pass']),
                            'exact native Lake adapter invocation')

    def test_other_lake_adapter_directory_is_rejected(self):
        self.refuse_capture(dict(exit_code=0,stop=None,cwd='/unrelated',
                                 command=['/unrelated/lake','build','adapter']),
                            'exact native Lake adapter invocation')

    def test_unpinned_guard_is_rejected(self):
        self.refuse_capture(dict(exit_code=0,stop=None,runner_sha256='different'),
                            'pinned reviewed implementation')

    def test_weaker_physical_limit_is_rejected(self):
        limits=dict(capture.FINAL_LIMITS,cgroup_stop=8*1024**3)
        self.refuse_capture(dict(exit_code=0,stop=None,limits=limits),
                            'limits differ from the approved profile')

    def test_owned_ledger_binds_reuse_origin(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);path=root/'0000.json'
            path.write_text(json.dumps(dict(execution='AUTHENTICATED_REUSE',origin='original')))
            before=interface.ledger_digest(root,dict(modules=[{}]))
            path.write_text(json.dumps(dict(execution='AUTHENTICATED_REUSE',origin='changed')))
            self.assertNotEqual(before,interface.ledger_digest(root,dict(modules=[{}])))


if __name__=='__main__':
    root=Path(__file__).resolve().parent
    print(json.dumps(dict(executed_source_pins={name:hashlib.sha256((root/name).read_bytes()).hexdigest()
        for name in ['test_final_gates.py','capture_final.py','audit_support_interface.py','build_support.py']})),flush=True)
    unittest.main(verbosity=2)
