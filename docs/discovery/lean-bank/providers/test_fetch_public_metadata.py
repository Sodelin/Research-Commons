import unittest
from pathlib import Path
from fetch_public_metadata import observe
from project_intake import load_json

class TestFetch(unittest.TestCase):
    def setUp(self):
        root=Path(__file__).resolve().parent/"reference"
        self.policy=load_json(root/"approved.json")
        self.ref=load_json(root/"lean4-core-capture.json")
    def fake(self,path):
        if "/commits/" in path: return self.ref["commit"]
        if "/trees/" in path: return next(t for t in self.ref["trees"] if t["sha"]==path.split("/")[-1])
        if "/contents/" in path:
            return [{"type":"file","path":e["path"],"sha":e["sha"],"html_url":e["url"]} for e in self.ref["corroboration"]]
        raise AssertionError(path)
    def test_live_shapes_without_network(self):
        result=observe("lean4_core_selected",self.policy,self.fake)
        self.assertEqual(result["status"],"passed")
        self.assertEqual(result["receipt"]["count"],4)
        self.assertFalse(result["receipt"]["source_bytes_verified"])
    def test_corroboration_must_agree(self):
        def forged(path):
            r=self.fake(path)
            if "/contents/" in path: return [{**x,"sha":"0"*40} for x in r]
            return r
        with self.assertRaises(ValueError):
            observe("lean4_core_selected",self.policy,forged)

if __name__=="__main__": unittest.main()
