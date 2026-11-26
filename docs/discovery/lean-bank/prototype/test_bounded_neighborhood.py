import json
import unittest

from bounded_neighborhood import neighborhood

seed = "Finset.surjOn_of_injOn_of_card_le"
local = "AlexanderOmnibus.neighbor_lift_of_same_degree"
bridge = "AlexanderOmnibus.transport_of_retained_degrees"
loose = "Finset.map_eq_of_subset"

# Audited metadata fixture, not a live dependency graph. The cross-project
# relation records a manually audited analogy; it is not an import.
graph = {
    seed: [(local, "analogue", ("saturation",)), (loose, "same_module", ())],
    local: [(bridge, "used_by", ("edge_reflection", "walk_coverage")), (seed, "uses", ("saturation",))],
    bridge: [("actual_population_boundary", "same_module", ("concrete_boundary",))],
}


class Tests(unittest.TestCase):
    def test_follow_real_bridge_stop_before_concrete_boundary(self):
        goals = {"saturation", "edge_reflection", "walk_coverage", "concrete_boundary"}
        receipt = neighborhood(seed, goals, lambda node: iter(graph.get(node, ())))
        self.assertEqual([x["id"] for x in receipt["actions"]], [local, bridge])
        self.assertEqual(receipt["uncovered"], ["concrete_boundary"])
        self.assertEqual(receipt["edges_examined"], 4)
        self.assertEqual(receipt["stop"], "depth_budget")
        self.assertEqual(receipt["depth_frontier"], [bridge])
        self.assertIn((loose, "no_current_goal_gain"), receipt["declined"])
        print(json.dumps(receipt, sort_keys=True))

    def test_candidate_budget(self):
        reads = []
        def lines(node):
            reads.append(node)
            return iter(graph.get(node, ()))
        receipt = neighborhood(seed, {"saturation", "walk_coverage"}, lines, pulls=1)
        self.assertEqual(reads, [seed])
        self.assertEqual(receipt["stop"], "candidate_budget")

    def test_infinite_irrelevant_feed_stops(self):
        def lines(_):
            while True:
                yield "irrelevant", "same_module", ()
        receipt = neighborhood(seed, {"saturation"}, lines, fanout=3)
        self.assertEqual(receipt["edges_examined"], 3)
        self.assertEqual(receipt["actions"], [])

    def test_duplicate_hints_do_not_expand_twice(self):
        rows = [(local, "used_by", ("saturation",)), (local, "same_module", ("saturation",))]
        receipt = neighborhood(seed, {"saturation", "walk_coverage"},
                               lambda node: iter(rows if node == seed else []))
        self.assertEqual(len(receipt["actions"]), 1)

    def test_failed_check_can_retry_with_alternative(self):
        rows = [("a", "used_by", ("goal",)), ("b", "used_by", ("goal",))]
        result = neighborhood(seed, {"goal"}, lambda _: iter(rows), excluded={"a"})
        self.assertEqual(result["actions"][0]["id"], "b")


if __name__ == "__main__":
    unittest.main()
