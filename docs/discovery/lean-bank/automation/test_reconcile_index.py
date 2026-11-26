import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from reconcile_index import Failure, reconcile

HERE = Path(__file__).resolve().parent
PRODUCER = HERE.parent/"pb-linked-bank"/"automation"/"index_sources.py"
if (HERE/"index_sources.py").is_file():
    PRODUCER = HERE/"index_sources.py"


class Tests(unittest.TestCase):
    def setUp(self):
        trial = tempfile.TemporaryDirectory(dir=HERE, prefix="trial-")
        self.addCleanup(trial.cleanup)
        self.repo = Path(trial.name)/"git"
        self.index = Path(trial.name)/"index"
        self.repo.mkdir()
        self.git("init","-q")
        self.git("-c","user.email=tests@invalid.example","-c","user.name=Tests",
                 "commit","-qm","base","--allow-empty")
        self.old = self.git("rev-parse","HEAD")
        for p in ("research/x/Ok.lean", "lean/Y.md", "packages/research/s/a-receipt.json",
                  "docs/discovery/lean-bank/tools/Z.md", "research/x/raw.txt",
                  "elsewhere/other.lean"):
            self.write(p,"invalid Lean deliberately not executed\n")
        link=self.repo/"research/x/skip.lean"
        link.symlink_to("Ok.lean")
        self.git("add",".")
        self.git("update-index","--add","--cacheinfo","160000,"+self.old+",research/ext.lean")
        self.git("-c","user.email=tests@invalid.example","-c","user.name=Tests","commit","-qm","inventory")
        self.sha = self.git("rev-parse","HEAD")
        self.write("research/x/Untracked.lean","ignored")
        self.command = [sys.executable, str(HERE/"reconcile_index.py"), "--root",str(self.repo),
                        "--index",str(self.index),"--commit",self.sha]
        self.generate()

    def git(self,*a):
        return subprocess.check_output(["git","-C",str(self.repo),*a],text=True).strip()

    def write(self,p,b):
        file=self.repo/p
        file.parent.mkdir(parents=True,exist_ok=True)
        file.write_text(b)

    def generate(self):
        subprocess.run([sys.executable,str(PRODUCER),"--root",str(self.repo),"--commit",self.sha,
                        "--dest",str(self.index)],check=True,stdout=subprocess.DEVNULL)

    def mutate(self, f):
        path = self.index/"receipt.json"
        receipt = json.loads(path.read_text())
        acc = hashlib.sha256()
        for e in receipt["shards"]:
            sp=self.index/e["path"]
            rows=[json.loads(l) for l in sp.read_text().splitlines()]
            new=f(e["path"],rows)
            body="".join(json.dumps(r,separators=(",",":"))+"\n" for r in new).encode()
            sp.write_bytes(body)
            e.update(rows=len(new),sha256=hashlib.sha256(body).hexdigest())
            acc.update(body)
        receipt.update(rows=sum(e["rows"] for e in receipt["shards"]), sha256=acc.hexdigest())
        if "scan" in receipt:
            receipt["scan"].update(reused_rows=0,source_bodies_read=receipt["rows"])
        path.write_text(json.dumps(receipt))

    def mismatch(self, code):
        with self.assertRaises(Failure) as ex:
            reconcile(self.repo,self.index,self.sha)
        self.assertEqual(ex.exception.code,code)
        return ex.exception.info

    def test_real_producer_and_exact_exclusions(self):
        r=reconcile(self.repo,self.index,self.sha)
        self.assertEqual(r["by_kind"],{"lean_source":1,"research_note":1,"receipt_locator":1})
        self.assertEqual(r["excluded_in_roots"],{"gitlink":1,"symlink":1,
            "tooling_documentation":1,"unsupported_extension_or_basename":1})
        self.assertEqual(r["evidence"],"inventory_only")
        self.assertEqual(r["tree_entries_in_roots"],7)

    def test_missing_despite_valid_rehashed_manifest(self):
        self.mutate(lambda _,rs:[r for r in rs if r["kind"] != "lean_source"])
        info=self.mismatch("git_index_coverage_mismatch")
        self.assertEqual(info["missing"],["research/x/Ok.lean"])

    def test_stale_blob_and_kind_despite_valid_rehashed_manifest(self):
        def change(_,rs):
            for r in rs:
                if r["kind"]=="lean_source":
                    r.update(git_blob="f"*40,kind="research_note")
            return rs
        self.mutate(change)
        detail=self.mismatch("git_index_coverage_mismatch")["changed"][0]
        self.assertEqual(detail["path"],"research/x/Ok.lean")
        self.assertEqual(detail["indexed_blob"],"f"*40)
        self.assertEqual(detail["expected_kind"],"lean_source")

    def test_duplicate(self):
        self.mutate(lambda _,rs:rs+rs)
        self.mismatch("duplicate_index_path")

    def test_forged_extra(self):
        forged="research/x/Untracked.lean"
        group=hashlib.sha256(forged.encode()).hexdigest()[:2]
        ghost={"path":forged,"kind":"lean_source","git_blob":"f"*40,"title":"Forged",
               "declaration_hints":[],"evidence":"indexed_only"}
        self.mutate(lambda s,rs:rs+[ghost] if s==f"shards/{group}.jsonl" else rs)
        self.assertEqual(self.mismatch("git_index_coverage_mismatch")["unexpected"],[forged])

    def test_incremental_manifest_with_exact_count(self):
        path=self.index/"receipt.json"
        r=json.loads(path.read_text())
        r.update(hint_version="line-hints.v1",scan={"prior_index":"previous-source",
                 "reused_rows":2,"source_bodies_read":1})
        path.write_text(json.dumps(r))
        self.assertEqual(reconcile(self.repo,self.index,self.sha)["indexed_rows"],3)
        r["scan"]["reused_rows"]=0
        path.write_text(json.dumps(r))
        self.mismatch("invalid_incremental_scan_counts")
        r.pop("scan")
        path.write_text(json.dumps(r))
        self.mismatch("invalid_json_fields")

    def test_bad_manifest_pin(self):
        with self.assertRaises(Failure) as ex:
            reconcile(self.repo,self.index,self.old)
        self.assertEqual(ex.exception.code,"manifest_commit_mismatch")

    def test_changed_payload_without_rehash(self):
        p=self.index/"shards/00.jsonl"
        p.write_bytes(p.read_bytes()+b"bogus\n")
        self.mismatch("shard_digest_mismatch")

    def test_extra_shard_file(self):
        (self.index/"shards/extra.jsonl").write_bytes(b"")
        self.mismatch("unexpected_shard_directory_contents")

    def test_hints_may_not_claim_proof(self):
        def overstate(_,rs):
            return [{**r,"evidence":"lean_verified"} for r in rs]
        self.mutate(overstate)
        self.mismatch("index_row_overstates_evidence")

    def test_cli_fails_closed_and_emits_machine_report(self):
        self.mutate(lambda _,rs:[])
        report=self.index/"coverage.json"
        proc=subprocess.run(self.command+["--report",str(report)],capture_output=True)
        self.assertEqual(proc.returncode,2)
        self.assertEqual(json.loads(report.read_text()),json.loads(proc.stdout))
        self.assertEqual(json.loads(proc.stdout)["status"],"failed")


if __name__=="__main__":
    unittest.main()
