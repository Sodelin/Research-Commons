import unittest
from graph_certificate import SCHEMA, request_hash, verify, read_strict
class Tests(unittest.TestCase):
    def run_case(self, obs, query, kind, **details):
        r = {"schema":SCHEMA,"domain":{"kind":"all_labeled_simple_undirected","n":3},
             "observations":obs,"query":query}
        return verify(r,{"request_sha256":request_hash(r),"kind":kind,**details})
    @property
    def count1(self): return [{"feature":{"kind":"edge_count"},"eq":1}]
    @property
    def edge(self): return {"kind":"identify","target":{"kind":"edge","uv":[0,1]}}
    def test_distinct_target_same_obs_is_not_infeasible(self):
        self.assertEqual(self.run_case(self.count1,self.edge,"ambiguity_pair",left=1,right=2)["values"], [1,0])
        with self.assertRaises(ValueError): self.run_case(self.count1,self.edge,"empty_replay")
    def test_counterexample_must_fit_observation(self):
        with self.assertRaises(ValueError): self.run_case(self.count1,self.edge,"ambiguity_pair",left=1,right=0)
    def test_counterexample_must_differ_on_target(self):
        with self.assertRaises(ValueError): self.run_case(self.count1,self.edge,"ambiguity_pair",left=2,right=4)
    def test_false_identified_rejected(self):
        with self.assertRaises(ValueError): self.run_case(self.count1,self.edge,"identified_replay",witness=1)
    def test_identified_nonempty(self):
        self.assertEqual(self.run_case(self.count1,{"kind":"identify","target":{"kind":"edge_count"}},
                                       "identified_replay",witness=1)["value"],1)
    def test_empty_does_not_identify_vacuously(self):
        obs=self.count1+[{"feature":{"kind":"degree","v":0},"eq":2}]
        self.assertEqual(self.run_case(obs,self.edge,"empty_replay")["states_replayed"],8)
        with self.assertRaises(ValueError): self.run_case(obs,self.edge,"identified_replay",witness=1)
    def test_unknown_is_not_attested(self):
        self.assertFalse(self.run_case([],self.edge,"unknown")["verified"])
    def test_check_binding(self):
        r = {"schema":SCHEMA,"domain":{"kind":"all_labeled_simple_undirected","n":3},
             "observations":self.count1,"query":self.edge}
        c = {"request_sha256":request_hash(r),"kind":"ambiguity_pair","left":1,"right":2}
        r["query"]={"kind":"identify","target":{"kind":"edge","uv":[0,2]}}
        with self.assertRaises(ValueError): verify(r,c)
    def test_non_integer_and_out_of_range_witness(self):
        for w in (True, 1.0, -1, 8):
            with self.assertRaises(ValueError): self.run_case(self.count1,{"kind":"feasible"},"feasible_witness",witness=w)
    def test_duplicate_json_key(self):
        with self.assertRaises(ValueError): read_strict('{"k": "x", "k": "y"}')
    def test_direct_feasible_witness(self):
        self.assertEqual(self.run_case(self.count1,{"kind":"feasible"},"feasible_witness",witness=1)["status"],"feasible")

if __name__ == "__main__": unittest.main()
