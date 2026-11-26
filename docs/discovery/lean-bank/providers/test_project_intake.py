import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import project_intake as p

ROOT = Path(__file__).resolve().parent
PROVIDER = "lean4_core_selected"

class IntakeTests(unittest.TestCase):
    def setUp(self):
        self.approval = p.load_json(ROOT/"reference/approved.json")
        self.capture = p.load_json(ROOT/"reference/lean4-core-capture.json")

    def reject(self, pattern):
        with self.assertRaisesRegex(ValueError, pattern):
            p.products(PROVIDER, self.approval, self.capture)

    def test_pinned_actual_material(self):
        rows, meta, receipt = p.products(PROVIDER, self.approval, self.capture)
        self.assertEqual(meta["count"], 4)
        self.assertEqual(meta["repo"], "leanprover/lean4")
        self.assertEqual(meta["evidence"], "source_path_only")
        self.assertEqual(meta["commit"], "819816b2e0a3bf405af45ae5c7af2491d8f5bee6")
        self.assertTrue(receipt["tree_object_hashes_recomputed"])
        self.assertFalse(receipt["source_bytes_verified"])
        self.assertFalse(receipt["lean_replay"])
        root = ROOT.parent/"external"
        self.assertEqual(rows, (root/"lean4-core-selected.jsonl").read_bytes())
        self.assertEqual(p.canonical({PROVIDER:meta}), (root/"providers.fragment.json").read_bytes())
        self.assertEqual(p.canonical(receipt), (root/"lean4-core-selected.receipt.json").read_bytes())

    def test_output_is_byte_stable_under_tree_order(self):
        expected, meta, _ = p.products(PROVIDER, self.approval, copy.deepcopy(self.capture))
        self.capture["trees"].reverse()
        for tree in self.capture["trees"]:
            tree["tree"].reverse()
        rows, new_meta, _ = p.products(PROVIDER, self.approval, self.capture)
        self.assertEqual(rows, expected)
        self.assertEqual(meta, new_meta)

    def test_unapproved_provider_is_not_discovered(self):
        with self.assertRaisesRegex(ValueError, "not approved"):
            p.products("unknown", self.approval, self.capture)

    def test_revision_not_branch(self):
        self.approval["providers"][PROVIDER]["commit"] = "main"
        self.reject("full lowercase")

    def test_wrong_commit_origin(self):
        self.capture["commit"]["url"] = self.capture["commit"]["url"].replace("leanprover", "someone")
        self.reject("commit does not match")

    def test_commit_string_cannot_substitute_root(self):
        self.capture["commit"]["tree"]["sha"] = "0"*40
        self.capture["commit"]["tree"]["url"] = "https://api.github.com/repos/leanprover/lean4/git/trees/"+"0"*40
        self.reject("root tree does not match")

    def test_wrong_tree_origin(self):
        self.capture["trees"][0]["url"] = "https://example.com/fake"
        self.reject("unexpected tree origin")

    def test_truncation(self):
        self.capture["trees"][0]["truncated"] = True
        self.reject("incomplete tree")

    def test_entry_mutation(self):
        self.capture["trees"][0]["tree"][0]["sha"] = "0"*40
        self.reject("Git tree hash mismatch")

    def test_detached_snapshot(self):
        self.capture["trees"].pop()
        self.reject("missing required tree")

    def test_duplicate_entry(self):
        entries = self.capture["trees"][0]["tree"]
        entries.append(entries[0])
        self.reject("duplicate tree name")

    def test_corroboration_conflict(self):
        self.capture["corroboration"][0]["sha"] = "0"*40
        self.reject("corroboration disagrees")

    def test_disallowed_file(self):
        self.approval["providers"][PROVIDER]["paths"][0] = "../Outside.lean"
        self.reject("noncanonical Git path segment")

    def test_promotion_rejected(self):
        self.approval["providers"][PROVIDER]["evidence"] = "kernel_checked"
        self.reject("evidence promotion")

    def test_hard_entry_budget(self):
        with patch.object(p, "MAX_ENTRIES", 3):
            self.reject("cap exceeded")

    def test_duplicate_input_keys(self):
        with tempfile.TemporaryDirectory() as td:
            f = Path(td)/"duplicate.json"
            f.write_text('{"dup":1,"dup":2}')
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                p.load_json(f)

    def test_git_mode_policy_rejects_even_hash_valid_symlink(self):
        repo, commit, file = "test/repo", "a"*40, "Shim.lean"
        e = {"path":file,"mode":"120000","type":"blob","sha":"b"*40}
        tid = p.git_tree_hash([e])
        api = f"https://api.github.com/repos/{repo}/git"
        app = {"schema":"proofbridge.github-allowlist.v1", "providers":{
            "test":{"repo":repo,"commit":commit,"tree":tid,"paths":[file],"max_files":1,
                    "evidence":"source_path_only"}}}
        cap = {"schema":"proofbridge.github-metadata.v1", "commit":{
            "sha":commit,"url":f"{api}/commits/{commit}","tree":{"sha":tid,"url":f"{api}/trees/{tid}"}},
            "trees":[{"sha":tid,"url":f"{api}/trees/{tid}","truncated":False,"tree":[e]}],
            "corroboration":[{"path":file,"sha":e["sha"],"url":f"https://github.com/{repo}/blob/{commit}/{file}"}]}
        with self.assertRaisesRegex(ValueError, "not a regular Lean Git source blob"):
            p.verify("test",app,cap)

if __name__ == "__main__":
    unittest.main()
