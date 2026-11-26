import unittest
from catalog import Catalog, VERSION, digest


def sample():
    provenance = {"kind":"primary","reference":"demo fixture, not proof evidence"}
    return {"schema":VERSION,"problems":[
      {"id":"problem.alexander.001","title":"Universal capped host","statement":"All eligible families satisfy P.",
       "closure":"open","provenance":provenance}],
      "theorems":[{"id":"theorem.host.minor","title":"Capped host grid minor bound",
        "statement":"All balanced indexed hosts satisfy Q.","proof_status":"hand_proof","assumptions":["vertices indexed in birth order"],
        "problems":[{"id":"problem.alexander.001","relation":"partial"}],
        "artifacts":["artifact.host.minor"],"provenance":provenance}],
      "artifacts":[{"id":"artifact.host.minor","repo":"Owner/Repo","commit":"a"*40,
        "path":"Lean/Minor.lean","declaration":"Research.NoMinor","sha256":None,
        "verification":{"kind":"source_only","reference":None,"lean_version":None,"statement_sha256":None},
        "provenance":provenance}]}


class CatalogTests(unittest.TestCase):
    def test_partial_keeps_problem_open(self):
        c=Catalog(sample())
        self.assertEqual(c.show("problem.alexander.001")["closure"],"open")
        self.assertEqual(c.show("theorem.host.minor")["artifact_evidence"],["source_only"])
        self.assertEqual(c.search("grid minor")[0]["id"],"theorem.host.minor")

    def test_closed_cannot_be_only_partial(self):
        x=sample()
        x["problems"][0]["closure"]="closed"
        with self.assertRaisesRegex(ValueError,"closed requires"):
            Catalog(x)

    def test_wrongly_promoting_exact_claim(self):
        x=sample()
        x["theorems"][0]["problems"][0]["relation"]="exact"
        with self.assertRaisesRegex(ValueError,"exact coverage"):
            Catalog(x)

    def test_closed_math_can_be_source_only_but_not_attested(self):
        x=sample()
        x["problems"][0]["statement"]=x["theorems"][0]["statement"]
        x["problems"][0]["closure"]="closed"
        x["theorems"][0]["problems"][0]["relation"]="exact"
        x["theorems"][0]["assumptions"]=[]
        p=Catalog(x).show("problem.alexander.001")
        self.assertEqual(p["closure"],"closed")
        self.assertFalse(p["has_exact_kernel_attestation"])

    def test_pinned_lock_resolution(self):
        c=Catalog(sample())
        lock=c.lock("problem.alexander.001")
        self.assertEqual(lock["artifacts"],c.lock("theorem.host.minor")["artifacts"])
        self.assertEqual(lock["artifacts"][0]["commit"],"a"*40)
        self.assertEqual(lock["artifacts"][0]["verification"]["kind"],"source_only")
        self.assertIsNone(lock["artifacts"][0]["sha256"])

    def test_floating_ref_and_path_traversal_rejected(self):
        x=sample()
        for bad in ("main","a12345",".","refs/heads/main"):
            x["artifacts"][0]["commit"]=bad
            with self.assertRaisesRegex(ValueError,"full Git commit"):
                Catalog(x)
        x["artifacts"][0]["commit"]="a"*40
        for p in ("../mine.lean","/Lean/a.lean","Lean//a.lean","Lean/./a.lean","."):
            x["artifacts"][0]["path"]=p
            with self.assertRaisesRegex(ValueError,"noncanonical path"):
                Catalog(x)

    def test_dangling_refs(self):
        x=sample()
        x["theorems"][0]["artifacts"]=["artifact.nonexistent"]
        with self.assertRaisesRegex(ValueError,"dangling"):
            Catalog(x)
        x=sample()
        x["theorems"][0]["problems"][0]["id"]="problem.nonexistent"
        with self.assertRaisesRegex(ValueError,"dangling"):
            Catalog(x)

    def test_real_remote_report_distinct_from_locally_checked_declaration(self):
        x=sample()
        v=x["artifacts"][0]["verification"]
        v.update(kind="remote_ci",reference="verified CI run reference",lean_version="Lean version",statement_sha256=None)
        self.assertEqual(Catalog(x).show("theorem.host.minor")["artifact_evidence"],["remote_ci"])
        self.assertFalse(Catalog(x).show("problem.alexander.001")["has_exact_kernel_attestation"])

    def test_kernel_attestation_needs_pins_and_matches_statement(self):
        x=sample()
        a=x["artifacts"][0]
        v=a["verification"]
        v.update(kind="kernel_checked",reference="receipt",lean_version="Lean 4",statement_sha256="a"*64)
        with self.assertRaisesRegex(ValueError,"requires source"):
            Catalog(x)
        a["sha256"]="b"*64
        with self.assertRaisesRegex(ValueError,"different statement"):
            Catalog(x)
        v["statement_sha256"]=digest(x["theorems"][0]["statement"])
        self.assertEqual(Catalog(x).show("theorem.host.minor")["artifact_evidence"],["kernel_checked"])
        self.assertFalse(Catalog(x).show("problem.alexander.001")["has_exact_kernel_attestation"])

    def test_source_only_cannot_carry_receipt(self):
        x=sample()
        x["artifacts"][0]["verification"]["reference"]="phantom receipt"
        with self.assertRaisesRegex(ValueError,"source-only"):
            Catalog(x)

    def test_dependency_and_reverse_lookup(self):
        x=sample()
        from copy import deepcopy
        t=deepcopy(x["theorems"][0]); t.update(id="theorem.other",problems=[],artifacts=[])
        t["uses"]=[{"id":"theorem.host.minor","relation":"uses"}]
        x["theorems"].append(t)
        c=Catalog(x)
        self.assertEqual(c.show("theorem.host.minor")["used_by"],[{"id":"theorem.other","relation":"uses"}])
        self.assertEqual(c.show("artifact.host.minor")["linked_theorem_ids"],["theorem.host.minor"])
        self.assertEqual(c.lock("theorem.other")["artifacts"],c.lock("theorem.host.minor")["artifacts"])
        t["uses"][0]["relation"]="may_use"
        self.assertEqual(Catalog(x).lock("theorem.other")["artifacts"],[])

    def test_no_kernel_theorem_from_source(self):
        x=sample()
        x["theorems"][0]["proof_status"]="kernel_checked"
        with self.assertRaisesRegex(ValueError,"theorem-level kernel"):
            Catalog(x)

if __name__=="__main__":
    unittest.main()
