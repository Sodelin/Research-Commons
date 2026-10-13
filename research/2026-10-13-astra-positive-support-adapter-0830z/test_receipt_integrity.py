#!/usr/bin/env python3
"""Bounded malformed-evidence checks. No Lean compiler is invoked."""
import json
from pathlib import Path
import tempfile
import unittest

import build_support as support
import capture_batch as capture


class ReceiptIntegrity(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)
        self.state=self.root/'state';self.state.mkdir()
        self.batch=self.root/'batch';self.batch.mkdir()

    def guard(self,stdout,exit_code=0):
        (self.batch/'stdout').write_text(stdout)
        (self.batch/'stderr').write_text('')
        receipt=dict(exit_code=exit_code,stop='wall' if exit_code else None,
                     outputs={suffix:dict(bytes=(self.batch/suffix).stat().st_size,
                                          sha256=capture.sha((self.batch/suffix).read_bytes()))
                              for suffix in ['stdout','stderr']})
        (self.batch/'RECEIPT.json').write_text(json.dumps(receipt))

    def test_truncated_guard_output_rejected(self):
        self.guard(json.dumps(dict(status='BATCH_COMPLETE',freshly_compiled=0))+'\n')
        (self.batch/'stdout').write_text('')
        with self.assertRaisesRegex(ValueError,'guard output bytes differ'):
            capture.capture(self.state,self.batch)

    def test_missing_completion_event_rejected(self):
        self.guard(json.dumps(dict(status='BATCH_COMPLETE',freshly_compiled=1))+'\n')
        with self.assertRaisesRegex(ValueError,'summary differs'):
            capture.capture(self.state,self.batch)

    def test_eventless_partial_receipt_preserved(self):
        (self.state/'PLAN.json').write_text(json.dumps(dict(modules=[dict(module='Example')])) )
        (self.batch/'PRE-BATCH-STATE.json').write_text('{}')
        (self.state/'0000.json').write_bytes(b'{"partial":')
        (self.state/'0000.stdout').write_bytes(b'compiler output\xff')
        self.guard('',exit_code=-15)
        capture.capture(self.state,self.batch)
        result=json.loads((self.batch/'MODULE-RECEIPTS.json').read_text())
        orphan=result['interrupted_unverified_invocations'][0]
        self.assertEqual(orphan['status'],'EVENTLESS_UNVERIFIED_EVIDENCE')
        self.assertEqual(orphan['outputs']['json']['sha256'],capture.sha(b'{"partial":'))
        self.assertIn('exact_bytes_base64',orphan['outputs']['stdout'])

    def test_empty_object_set_rejected(self):
        with self.assertRaisesRegex(ValueError,'missing or changed module artifacts'):
            support.authenticate_artifacts({},self.state/'Missing.olean')

    def test_resumed_log_mutation_rejected(self):
        for suffix in ['stdout','stderr']:(self.state/('0000.'+suffix)).write_text('')
        receipt={suffix+'_sha256':capture.sha(b'') for suffix in ['stdout','stderr']}
        (self.state/'0000.stdout').write_text("'Fake' does not depend on any axioms\n")
        with self.assertRaisesRegex(ValueError,'compiler log differs'):
            support.read_audit_logs(self.state,0,receipt)

    def test_resumed_placeholder_rejected(self):
        (self.state/'0000.stdout').write_text("'Fake' depends on axioms: [sorryAx]\n")
        (self.state/'0000.stderr').write_text('')
        receipt={suffix+'_sha256':capture.sha((self.state/('0000.'+suffix)).read_bytes())
                 for suffix in ['stdout','stderr']}
        with self.assertRaisesRegex(ValueError,'placeholder axiom'):
            support.read_audit_logs(self.state,0,receipt)

    def test_artifact_extensions_remain_bound(self):
        mapped=support.copied_artifact_map({'/old/Test.olean':'one','/old/Test.ir':'two'},
                                          self.state/'Test.olean')
        self.assertEqual(mapped[str(self.state/'Test.olean')],'one')
        self.assertEqual(mapped[str(self.state/'Test.ir')],'two')


if __name__=='__main__':unittest.main()
