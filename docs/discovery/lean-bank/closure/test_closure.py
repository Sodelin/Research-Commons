import tempfile, unittest
from pathlib import Path
from closure import git_blob, lean_header, plan, sha256

class Closure(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.store = self.root/"store"
        self.spec = {"repo":"Example/Lean","commit":"a"*40,"source_prefix":"lean",
                     "module_prefixes":["Example"],"blobs":{}}
        self.cfg = {"schema":"commons.lean-source-planner.v1","version":"review-v1",
                    "toolchain":"lean-v4.33.1","toolchain_module_prefixes":["Init","Lean","Std"],
                    "targets":["Example.Main"],"repositories":[self.spec]}

    def add(self, name, content, attest=True):
        path = self.store / "review-v1/Example/Lean" / self.spec["commit"] / "lean" / (name.replace(".","/")+".lean")
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_bytes(content)
        if attest:
            self.spec["blobs"][name] = git_blob(content)
        return path

    def run_plan(self):
        return plan(self.cfg,self.store,self.root)

    def test_lexing(self):
        self.assertEqual(lean_header(b"-- import Fake\n/- outer /- nested -/ -/\nmodule\nprelude\npublic meta import all Lean\nimport Example.A\n/-! docs import Fake -/\ndef x := \"/-\"\n"),["Lean","Example.A"])
        self.assertEqual(lean_header(b"import Std\nimport Std\ndef x := 0\n"),["Init","Std"])
        self.assertEqual(lean_header(b"import\n Std\n"),["Init","Std"])
        self.assertRaises(ValueError, lean_header, b"import Example.\xc2\xabName\xc2\xbb\n")
        self.assertRaises(ValueError, lean_header, b"/- never closes")
        self.assertRaises(UnicodeError, lean_header, b"import \xff")

    def test_pending_and_dependency_order(self):
        p=self.run_plan()
        self.assertEqual(p["fetch_requests"][0]["ref"],"a"*40)
        self.assertEqual(p["fetch_requests"][0]["path"],"lean/Example/Main.lean")
        self.assertEqual(p["package_source_closure"],"incomplete")
        self.add("Example.Main",b"import Example.Util\nimport Std\n")
        self.assertEqual(self.run_plan()["blocking_modules"],["Example.Util"])
        self.add("Example.Util",b"import Lean\n")
        p=self.run_plan()
        self.assertEqual(p["dependency_first_source_order"],["Example.Util","Example.Main"])
        self.assertEqual(p["package_source_closure"],"present")
        self.assertEqual(p["compilability"],"not_checked")
        self.assertEqual(p["entries"]["Lean"]["status"],"toolchain_dependency_unverified")

    def test_unmapped_never_fetched(self):
        self.add("Example.Main",b"import SecretPackage.Theorem\n")
        p=self.run_plan()
        self.assertEqual(p["entries"]["SecretPackage.Theorem"]["status"],"unmapped_import")
        self.assertEqual(p["fetch_requests"],[])

    def test_missing_attestation(self):
        self.add("Example.Main",b"import Std\n",attest=False)
        p=self.run_plan()
        self.assertEqual(p["entries"]["Example.Main"]["status"],"pending_blob_attestation")
        self.assertEqual(p["package_source_closure"],"incomplete")

    def test_integrity_mismatch(self):
        path=self.add("Example.Main",b"import Std\n")
        path.write_bytes(b"import Example.Poison\n")
        p=self.run_plan()
        self.assertEqual(p["entries"]["Example.Main"]["status"],"integrity_mismatch")
        self.assertFalse(p["fetch_requests"])

    def test_cycle(self):
        self.add("Example.Main",b"import Example.Util\n")
        self.add("Example.Util",b"import Example.Main\n")
        p=self.run_plan()
        self.assertEqual(p["cycles"],[["Example.Main","Example.Util","Example.Main"]])
        self.assertIsNone(p["dependency_first_source_order"])
        self.assertEqual(p["package_source_closure"],"incomplete")

    def test_local_exact_package(self):
        f=self.root/"Local.lean"
        f.write_bytes(b"import Example.Main\n")
        self.cfg["targets"]=["Local"]
        self.cfg["local_sources"]={"Local":{"path":"Local.lean","sha256":sha256(f.read_bytes())}}
        self.add("Example.Main",b"import Std\n")
        p=self.run_plan()
        self.assertEqual(p["entries"]["Local"]["status"],"local_source_present")
        self.assertEqual(p["dependency_first_source_order"],["Example.Main","Local"])

    def test_unsafe_parameters(self):
        self.cfg["version"]="../oops"
        self.assertRaises(ValueError,self.run_plan)
        self.cfg["version"]="review-v1"
        self.spec["commit"]="main"
        self.assertRaises(ValueError,self.run_plan)

    def test_resolved_symlink_escape(self):
        f=self.add("Example.Main",b"import Std\n")
        (self.root/"outside.lean").write_bytes(f.read_bytes())
        f.unlink()
        f.symlink_to(self.root/"outside.lean")
        self.assertRaises(ValueError,self.run_plan)

    def test_version_isolation(self):
        self.add("Example.Main",b"import Std\n")
        self.cfg["version"]="review-v2"
        p=self.run_plan()
        self.assertEqual(p["entries"]["Example.Main"]["status"],"pending_source")
        self.assertTrue(p["fetch_requests"][0]["staging_path"].startswith("review-v2/"))

if __name__=="__main__":
    unittest.main(verbosity=2)
