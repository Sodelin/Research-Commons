import copy
import json
import unittest
from proof_job_ingress import evaluate, digest, Bad

dump = lambda o: json.dumps(o, sort_keys=True, separators=(",", ":")).encode()
H = lambda char: char * 64

class IngressTest(unittest.TestCase):
    def setUp(self):
        self.source = b"source fixture"
        self.ident = dict(job="lemma.smoke", commit="1"*40, source_sha256=digest(self.source), statement_sha256=H("2"))
        self.config = [
            dict(stage=s, checker_sha256=H(str(i)), input_sha256=H(str(i+3)), accept=a)
            for i, (s,a) in enumerate([("exact","passed"),("smt","unsat"),("lean","passed")], 3)
        ]
        self.reg = dict(schema="proofbridge.job-registry.v1", jobs=[dict(self.ident, stages=self.config)])
        self.receipts = [
            dict(self.ident, stage=c["stage"], checker_sha256=c["checker_sha256"], input_sha256=c["input_sha256"],
                 result=c["accept"], output_sha256=H("f"))
            for c in self.config
        ]
        self.job = dict(self.ident, schema="proofbridge.proof-job.v1", receipt_refs=[])

    def verdict(self, refs=None, ledger=None, reg_pin=None, ledger_pin=None, rawjob=None, source=None):
        r = dump(self.reg)
        l = dump(dict(schema="proofbridge.evidence-ledger.v1", registry_sha256=digest(r),
                      receipts=self.receipts if ledger is None else ledger))
        j = dict(self.job, receipt_refs=[digest(dump(s)) for s in (self.receipts if refs is None else refs)])
        return evaluate(r, reg_pin or digest(r), l, ledger_pin or digest(l), rawjob or dump(j),
                        self.source if source is None else source)

    def test_full_fixture_trusted_receipt_not_fresh_execution(self):
        result = self.verdict()
        self.assertEqual(result["disposition"], "trusted_kernel_receipt_matched")
        self.assertFalse(result["fresh_checker_execution"])

    def test_indexed_source_not_certified(self):
        result = self.verdict(refs=[])
        self.assertEqual(result["disposition"], "not_certified")
        self.assertEqual(result["stages"]["exact"]["disposition"], "pending")
        self.assertEqual(result["stages"]["lean"]["disposition"], "blocked")

    def test_exact_and_smt_do_not_replace_lean(self):
        self.assertEqual(self.verdict(refs=self.receipts[:2])["disposition"], "not_certified")

    def test_unknown_smt_blocks_lean(self):
        self.receipts[1]["result"] = "unknown"
        self.assertEqual(self.verdict(refs=self.receipts[:2])["stages"]["smt"]["disposition"], "inconclusive")
        with self.assertRaisesRegex(Bad, "after unresolved"):
            self.verdict()

    def test_wrong_smt_polarity_is_not_accepted(self):
        self.receipts[1]["result"] = "sat"
        self.assertFalse(self.verdict(refs=self.receipts[:2])["stages"]["smt"]["accepted"])
        with self.assertRaisesRegex(Bad, "after unresolved"):
            self.verdict()

    def test_source_substitution(self):
        with self.assertRaisesRegex(Bad, "source bytes mismatch"):
            self.verdict(source=b"wrong")

    def test_stale_reuse(self):
        for key, value in (("commit","f"*40), ("statement_sha256",H("e")), ("source_sha256",H("d"))):
            with self.subTest(key=key):
                refs = copy.deepcopy(self.receipts)
                refs[2][key] = value
                with self.assertRaisesRegex(Bad, "receipt job/commit/source/statement mismatch"):
                    self.verdict(refs=refs, ledger=refs)

    def test_cross_checker_substitution(self):
        for key in ("checker_sha256","input_sha256"):
            with self.subTest(key=key):
                refs = copy.deepcopy(self.receipts)
                refs[2][key] = H("d")
                with self.assertRaisesRegex(Bad, "checker/input mismatch"):
                    self.verdict(refs=refs, ledger=refs)

    def test_no_job_supplied_authority_or_commands(self):
        for key in ("command", "lean_script", "smt_program", "registry_pin", "status"):
            with self.subTest(key=key), self.assertRaisesRegex(Bad, "unexpected"):
                self.verdict(rawjob=dump(dict(self.job, **{key:"ignored?"})))

    def test_untrusted_pin(self):
        with self.assertRaisesRegex(Bad, "untrusted ledger"):
            self.verdict(ledger_pin=H("4"))
        with self.assertRaisesRegex(Bad, "untrusted registry"):
            self.verdict(reg_pin=H("4"))

    def test_duplicate_json_keys(self):
        with self.assertRaisesRegex(Bad, "duplicate JSON"):
            self.verdict(rawjob=b'{"job":"a","job":"b"}')

    def test_missing_prerequisite(self):
        with self.assertRaisesRegex(Bad, "after unresolved"):
            self.verdict(refs=self.receipts[1:])

    def test_duplicate_stage(self):
        refs = copy.deepcopy(self.receipts)
        refs[2] = dict(refs[0], output_sha256=H("b"))
        with self.assertRaisesRegex(Bad, "duplicate stage"):
            self.verdict(refs=refs, ledger=refs)

    def test_other_job(self):
        self.job["job"] = "lemma.unregistered"
        with self.assertRaisesRegex(Bad, "not registered"):
            self.verdict()

    def test_receipt_cannot_come_from_job_directly(self):
        self.receipts[2]["output_sha256"] = H("b")
        with self.assertRaisesRegex(Bad, "missing or untrusted receipt"):
            self.verdict(ledger=self.receipts[:2])

if __name__ == "__main__":
    unittest.main()
