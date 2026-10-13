"""Bounded fail-closed checks for final evidence gates; no Lean invocation."""
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
            (lake/'RECEIPT.json').write_text(json.dumps(guard))
            argv=['capture_final.py','--source-root',str(root/'source'),
                  '--state',str(state),'--external-state',str(root/'external'),
                  '--lake-output',str(lake),'--out',str(root/'export')]
            with patch.object(sys,'argv',argv),patch.object(capture.support,'verify',return_value={}):
                with self.assertRaisesRegex(ValueError,message):capture.main()
            self.assertFalse((root/'export').exists())

    def test_failed_guard_cannot_produce_final_export(self):
        self.refuse_capture(dict(exit_code=-15,stop='cgroup_pressure'),
                            'final Lake invocation did not pass')

    def test_other_successful_command_is_not_a_lake_target_receipt(self):
        self.refuse_capture(dict(exit_code=0,stop=None,command=['python3','-c','pass']),
                            'actual native Lake adapter target')


if __name__=='__main__':unittest.main(verbosity=2)
