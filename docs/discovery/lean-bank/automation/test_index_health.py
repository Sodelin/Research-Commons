import json
import subprocess
import tempfile
import unittest
from pathlib import Path

import index_health as h

class Tests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo=Path(self.tmp.name)
        self.g("init","-q")
        self.put("research/a.lean", "theorem hello : True := .intro\n")
        self.src=self.commit()
        sha=h.sha(b"")
        self.m={"schema":"commons.discovery.git-source-index.v2","evidence":"indexed_only",
                "source_commit":self.src,"sha256":sha,"rows":0,
                "shards":[{"path":f"shards/{i:02x}.jsonl","rows":0,"sha256":sha} for i in range(256)]}
        self.c={"schema":"commons.discovery.check-battery.v1","source_commit":self.src,"index_sha256":sha,
                "checks":{"source_index":{"status":"passed"}, "lean":{"status":"not_run"}}}
        self.q={"schema":"commons.discovery.query-smoke.v1","source_commit":self.src,"index_sha256":sha,
                "checks":[{"path":"research/a.lean","git_blob":self.g("rev-parse",self.src+":research/a.lean")}]}
        item=self.q["checks"][0]
        item["decl_hint"]="hello"
        row=json.dumps({"path":item["path"], "git_blob":item["git_blob"],
                        "declaration_hints":["hello"],"evidence":"indexed_only"})+"\n"
        self.m["rows"]=1
        self.m["sha256"]=self.c["index_sha256"]=self.q["index_sha256"]=h.sha(row.encode())
        bucket=int(h.sha(item["path"].encode())[:2],16)
        self.m["shards"][bucket].update(rows=1,sha256=self.m["sha256"])
        self.sync()
        for i,s in enumerate(self.m["shards"]):
            self.put(h.BASE+s["path"],row if i==bucket else "")
        self.commit()

    def put(self,path,body):
        f=self.repo/path
        f.parent.mkdir(parents=True,exist_ok=True)
        f.write_text(body)

    def sync(self):
        for n,o in [("receipt.json",self.m),("checks.json",self.c),("query-smoke.json",self.q)]:
            self.put(h.BASE+n,json.dumps(o))

    def g(self,*args):
        return subprocess.check_output(["git","-C",self.tmp.name,*args],text=True).strip()

    def commit(self):
        self.g("add","-A")
        self.g("-c","user.email=a@example.test","-c","user.name=A","commit","-qm","test commit")
        return self.g("rev-parse","HEAD")

    def test_healthy_and_unwatched_commit(self):
        self.put("README.md","not tracked by index scope\n")
        self.commit()
        self.assertEqual(h.status(self.repo,"HEAD")["status"],"current_for_index_scope")
        self.assertEqual(h.status(self.repo,"HEAD")["check_status_counts"]["lean"],"not_run")

    def test_stale_after_missed_push(self):
        self.put("research/a.lean","theorem changed : True := .intro\n")
        self.commit()
        self.assertEqual(h.status(self.repo,"HEAD")["status"],"stale")

    def test_bad_smoke_pin(self):
        self.q["checks"][0]["git_blob"]="1"*40
        self.sync()
        self.commit()
        with self.assertRaisesRegex(ValueError,"query pin"):
            h.status(self.repo,"HEAD")

    def test_companion_drift(self):
        self.q["index_sha256"]="1"*64
        self.sync()
        self.commit()
        with self.assertRaisesRegex(ValueError,"mixed"):
            h.status(self.repo,"HEAD")

    def test_rejects_receipt_without_actual_search_hint(self):
        self.q["checks"][0]["decl_hint"]="not_in_index"
        self.sync()
        self.commit()
        with self.assertRaisesRegex(ValueError,"mismatched query row"):
            h.status(self.repo,"HEAD")

    def test_optional_full_shard_readback(self):
        self.assertEqual(h.status(self.repo,"HEAD",True)["shard_bodies_checked"],256)
        self.put(h.BASE+"shards/ff.jsonl","{}\n")
        self.commit()
        with self.assertRaisesRegex(ValueError,"shard body mismatch"):
            h.status(self.repo,"HEAD",True)

if __name__ == "__main__":
    unittest.main()
