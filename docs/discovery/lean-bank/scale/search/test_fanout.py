import contextlib
import json
from pathlib import Path
import random
import runpy
import subprocess
import tempfile
import unittest
from fanout import build, load_generated, matching_ids, open_db, search, tokens

HERE=Path(__file__).resolve().parent
MANIFEST=HERE.parent/"pb-next-e2e-Ms9J/docs/discovery/generated-source-index"
BASE=HERE.parent/"pb-next-integrate/tools/search-bank.py"
legacy=runpy.run_path(str(BASE))
legacy_terms=legacy["terms"]

class Tests(unittest.TestCase):
    def setUp(self):
        tmp=tempfile.TemporaryDirectory(dir=HERE,prefix="test-")
        self.addCleanup(tmp.cleanup)
        self.db=Path(tmp.name)/"result.sqlite"
    def test_existing_index_and_legacy_owner(self):
        rows,meta=load_generated(MANIFEST)
        legacy_rows=list(legacy["generated_rows"](MANIFEST,json.loads((MANIFEST/"receipt.json").read_text())))
        self.assertEqual(rows,legacy_rows)
        build(rows,meta,self.db)
        with contextlib.closing(open_db(self.db)[0]) as con:
            for q in ("TriangleRun","triangle","theorem","source_commit","receipt","indexed_only","nothingknown",
                      *[t for row in legacy_rows for t in sorted(legacy_terms(json.dumps(row,ensure_ascii=False)))]):
                expected=[j for j,r in enumerate(legacy_rows)
                          if legacy_terms(q)<=legacy_terms(json.dumps(r,ensure_ascii=False))]
                self.assertEqual(matching_ids(con,q),expected,q)
    def test_limits_do_not_change_match_count(self):
        build([{"path":f"one/item_{i}","evidence":"indexed_only"} for i in range(40)],{},self.db)
        with contextlib.closing(open_db(self.db)[0]) as con:
            r=search(con,"item",2)
            self.assertEqual(r["matches"],40)
            self.assertEqual([x["path"] for x in r["results"]],["one/item_0","one/item_1"])
    def test_randomized_oracle(self):
        randomizer=random.Random(481)
        atoms=["triangle","balance","root","LEAF","arc","abc","青","café","alphaBeta","one_one"]
        rows=[{"path":"/".join(randomizer.choices(atoms,k=4))+f"/{j}.lean",
               "declaration_hints":randomizer.choices(atoms,k=3)}
              for j in range(310)]
        build(rows,{},self.db)
        with contextlib.closing(open_db(self.db)[0]) as con:
            for q in (" ".join(randomizer.choices(atoms,k=randomizer.randrange(1,5))) for _ in range(140)):
                if not tokens(q):
                    continue
                self.assertEqual(matching_ids(con,q),
                    [j for j,r in enumerate(rows) if legacy_terms(q)<=legacy_terms(json.dumps(r,ensure_ascii=False))],q)
    def test_no_substring_match_and_no_silent_empty_query(self):
        build([{"path":"longroot/Triangulation.lean"},{"path":"line/TriangleRun.lean"}],{},self.db)
        with contextlib.closing(open_db(self.db)[0]) as con:
            self.assertEqual(matching_ids(con,"triangle"),[1])
            self.assertEqual(matching_ids(con,"root"),[])
            with self.assertRaises(ValueError): matching_ids(con,"青")
    def test_stale_pin_rejected(self):
        rows,meta=load_generated(MANIFEST)
        build(rows,meta,self.db)
        p=subprocess.run(["python",str(HERE/"fanout.py"),"query",str(self.db),"triangle",
                          "--expect-commit","a"*40],capture_output=True)
        self.assertEqual(p.returncode,2)
        self.assertIn(b"cache commit mismatch",p.stderr)
    def test_failed_build_preserves_existing_cache(self):
        build([{"path":"untouched/Here.lean"}],{},self.db)
        with self.assertRaises(TypeError): build([{"bad":object()}],{},self.db)
        with contextlib.closing(open_db(self.db)[0]) as con:
            self.assertEqual(matching_ids(con,"here"),[0])

if __name__=="__main__": unittest.main()
