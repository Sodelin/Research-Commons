import concurrent.futures, tempfile, unittest
from pathlib import Path
from pickup import pick
from test_proof_job_ingress import IngressTest, digest, dump

class PickupTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.db = Path(self.tmp.name) / "state"
        f = IngressTest()
        f.setUp()
        self.id = tuple(f.ident.values())
        self.r = dump(f.reg)
        self.l = dump(dict(schema="proofbridge.evidence-ledger.v1", registry_sha256=digest(self.r),receipts=f.receipts))
        self.req = dump(dict(f.job,receipt_refs=[digest(dump(s)) for s in f.receipts]))
        self.src = f.source
        self.c = dict(schema="proofbridge.pickup-catalog.v1",entries=[dict(f.ident,
            lean_receipt_ref=digest(dump(f.receipts[-1])), lean_output_sha256=f.receipts[-1]["output_sha256"])])
        self.q = dict(schema="proofbridge.pickup-queue.v1",registry_sha256=digest(self.r),
            ledger_sha256=digest(self.l),entries=[dict(f.ident,request_sha256=digest(self.req))])

    def run_pick(self, tick=1, qpin=None, req=None, src=None, rpin=None, lpin=None):
        c=dump(self.c)
        q=dump(dict(self.q,catalog_sha256=digest(c)))
        return pick(self.db,tick,self.r,rpin or digest(self.r),self.l,lpin or digest(self.l),q,qpin or digest(q),
                    c,digest(c),{self.id:(req or self.req,src or self.src)})

    def test_concurrent_tick_and_same_binding_across_ticks(self):
        with concurrent.futures.ThreadPoolExecutor(3) as pool:
            out=list(pool.map(lambda _:self.run_pick(),range(3)))
        self.assertEqual(sorted(r["status"] for r in out),["already_picked","already_picked","picked_existing_receipt"])
        self.assertEqual(self.run_pick(tick=2)["status"],"no_work")
        self.assertEqual(len({dump(r["receipt"]) for r in out}),1)
        self.assertFalse(out[0]["receipt"]["fresh_checker_execution"])

    def test_untrusted_queue_and_source_bytes(self):
        with self.assertRaisesRegex(ValueError,"untrusted queue"): self.run_pick(qpin="b"*64)
        with self.assertRaisesRegex(ValueError,"source bytes mismatch"): self.run_pick(src=b"lookalike")
        self.assertEqual(self.run_pick()["status"],"picked_existing_receipt")

    def test_catalog_wrong_evidence(self):
        self.c["entries"][0]["lean_receipt_ref"]="d"*64
        with self.assertRaisesRegex(ValueError,"catalog references different evidence"): self.run_pick()

    def test_wrong_theorem_and_mixed_snapshot(self):
        self.c["entries"][0]["statement_sha256"]="e"*64
        with self.assertRaisesRegex(ValueError,"missing exact catalog"): self.run_pick()
        with self.assertRaisesRegex(ValueError,"mixed snapshot"): self.run_pick(lpin="c"*64)

if __name__ == "__main__": unittest.main()
