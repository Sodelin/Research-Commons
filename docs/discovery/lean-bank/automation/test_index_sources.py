import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from index_sources import discover

class GitIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo=Path(self.temp.name)
        self.git("init","-q")
        self.git("config","user.email","test@example.test")
        self.git("config","user.name","Test")
        self.git("commit","-qm","initial","--allow-empty")
        self.first=self.git("rev-parse","HEAD")
    def git(self,*args):
        return subprocess.check_output(["git","-C",str(self.repo),*args],text=True).strip()
    def write(self,name,body):
        p=self.repo/name
        p.parent.mkdir(exist_ok=True,parents=True)
        p.write_text(body)
        return p
    def test_committed_only_and_exact_blob(self):
        p=self.write("research/example/NewZeroRun.lean","theorem newlyDiscovered : True := by trivial\n")
        self.write("research/example/README.md","# New zero-run\n")
        (p.parent/"ignored.lean").symlink_to(p.name)
        self.git("add","research")
        self.git("commit","-qm","proof lands")
        sha=self.git("rev-parse","HEAD")
        self.write("research/example/Untracked.lean","theorem notCommitted : True := by trivial\n")
        self.assertEqual(discover(self.repo,self.first),[])
        rows={x["path"]:x for x in discover(self.repo,sha)}
        self.assertEqual(set(rows),{"research/example/README.md","research/example/NewZeroRun.lean"})
        entry=rows["research/example/NewZeroRun.lean"]
        self.assertEqual(entry["git_blob"],self.git("rev-parse",sha+":research/example/NewZeroRun.lean"))
        self.assertEqual(entry["declaration_hints"],["newlyDiscovered"])
        self.assertEqual(entry["evidence"],"indexed_only")
    def test_ref_must_be_pinned(self):
        with self.assertRaises(ValueError):
            discover(self.repo,"HEAD")

if __name__=="__main__": unittest.main()
