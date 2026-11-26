from pathlib import Path
import subprocess
import sys
import unittest
from index_sources import discover, read_cache
import test_index_sources

class IncrementalTests(test_index_sources.GitIndexTests):
    def generate(self, sha, dest, old=None):
        source=Path(__file__).with_name("index_sources.py")
        cmd=[sys.executable,str(source),"--root",str(self.repo),"--commit",sha,"--dest",str(dest)]
        if old is not None: cmd += ["--reuse",str(old)]
        subprocess.check_call(cmd,stdout=subprocess.DEVNULL)
    def test_exact_reuse_and_tamper(self):
        self.write("research/ok/First.lean","theorem first : True := by trivial\n")
        self.write("research/ok/Second.lean","theorem second : True := by trivial\n")
        self.git("add","research")
        self.git("commit","-qm","two sources")
        sha=self.git("rev-parse","HEAD")
        old=self.repo/"old"
        self.generate(sha,old)
        cache,state=read_cache(old)
        self.assertEqual(state,"verified")
        self.write("research/ok/Second.lean","theorem secondChanged : True := by trivial\n")
        self.git("add","research");self.git("commit","-qm","just one change")
        new=self.git("rev-parse","HEAD")
        m={}
        self.assertEqual(discover(self.repo,new,cache,m),discover(self.repo,new))
        self.assertEqual(m,{"reused_rows":1,"source_bodies_read":1})
        p=sorted((old/"shards").glob("*.jsonl"))[0]
        p.write_bytes(p.read_bytes()+b"tampered")
        self.assertEqual(read_cache(old),({},"rejected_rebuild"))
