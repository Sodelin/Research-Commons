"""New deterministic interface tests; mocked replay tests are plumbing only."""
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

BASE = Path(__file__).resolve().parent
WORKBENCH = BASE.parent / "practical-scientific-source-public-20261007-0503z" / "package"
sys.path.insert(0, str(WORKBENCH))
from jc_history_adapter import FixedJCBridge, Prepared, DOMAIN, FEATURES, MODEL, MAP, QUANTITY, PHYSICAL
from genealogy_workbench.core import InputError

RUNTIME = BASE.parent / "practical-synthetic-continuation-20261007-0302z" / "runtime-layout"
CORE = BASE.parent / "practical-synthetic-continuation-20261007-0302z" / "providers" / "integration_core.py"


def block(name="new", lo="3/4", hi="7/8", alpha="1/20"):
    return {"id": name, "source_instance": "one-common-source", "observation_map": MAP,
            "quantity": QUANTITY, "evidence_kind": "conditional_constraints_not_admitted",
            "error_allowance": alpha, "shifted_mean_box": {k: [lo, hi] for k in FEATURES}}


def history(blocks=None, mode="fresh_only", alpha="1/20"):
    return {"schema": "fixed-jc-constraint-history-v1", "model": MODEL,
            "observation_map": MAP, "quantity": QUANTITY, "source_instance": "one-common-source",
            "domain": deepcopy(DOMAIN), "mode": mode, "confidence_mode": "preallocated_fixed_blocks",
            "error_budget": alpha, "blocks": blocks if blocks is not None else [block()],
            "inverse_budget": {"scalar_steps": 0, "max_stages": 0, "max_splits": 0,
                "max_states": 1, "max_depth": 0, "wall_ms": 100,
                "recovery_wall_ms": 100, "recovery_max_stages": 0}}


class InterfaceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bridge = FixedJCBridge(RUNTIME, CORE)

    def parse(self, prepared, tmp, name="request.json"):
        p = Path(tmp) / name
        return self.bridge.write_request(prepared, p), p

    def test_actual_parser_and_initializer_shift_once_all_nine(self):
        prepared = self.bridge.prepare(history())
        self.assertEqual(prepared.request["quantity"], QUANTITY)
        self.assertEqual(prepared.request["features"], {k: ["3/4", "7/8"] for k in FEATURES})
        with tempfile.TemporaryDirectory() as tmp:
            parsed, _ = self.parse(prepared, tmp)
            state = self.bridge.engine.ops.initial(parsed["physical"], parsed["observed"])
            for k in FEATURES:
                self.assertEqual((state["moments"][k].lo, state["moments"][k].hi), (Q(1, 2), Q(3, 4)))
                self.assertNotEqual((state["moments"][k].lo, state["moments"][k].hi), (Q(0), Q(1, 2)))

    def test_cumulative_exact_intersection_and_three_over_twenty(self):
        p = self.bridge.prepare(history([block("old", "3/4", "7/8", "1/10"),
                                        block("new", "4/5", "9/10")], "cumulative", "3/20"))
        self.assertEqual(p.error_allowance, "3/20")
        self.assertEqual(p.selected_ids, ("old", "new"))
        self.assertEqual(p.request["features"], {k: ["4/5", "7/8"] for k in FEATURES})

    def test_fresh_only_does_not_retain_old_constraint_or_error(self):
        p = self.bridge.prepare(history([block("old", "1/2", "3/5", "1/10"), block("new")]))
        self.assertEqual(p.selected_ids, ("new",))
        self.assertEqual(p.error_allowance, "1/20")
        self.assertEqual(p.request["features"]["AA1"], ["3/4", "7/8"])

    def test_cumulative_insufficient_budget_rejected(self):
        with self.assertRaisesRegex(InputError, "insufficient error"):
            self.bridge.prepare(history([block("old", alpha="1/10"), block()], "cumulative", "1/10"))

    def test_empty_intersection_is_not_accuracy(self):
        p = self.bridge.prepare(history([block("old", "1/2", "3/5"), block()], "cumulative", "1/10"))
        self.assertEqual(p.status, "CONSTRAINT_INTERSECTION_EMPTY")
        self.assertIsNone(p.request)

    def test_nonempty_shifted_box_can_have_empty_model_range(self):
        p = self.bridge.prepare(history([block(lo="0", hi="1/4")]))
        self.assertEqual(p.status, "MODEL_RAW_RANGE_EMPTY")
        self.assertIsNone(p.request)

    def test_equal_endpoints_preserved(self):
        p = self.bridge.prepare(history([block(lo="3/4", hi="3/4")]))
        with tempfile.TemporaryDirectory() as tmp:
            parsed, _ = self.parse(p, tmp)
            v = self.bridge.engine.ops.initial(parsed["physical"], parsed["observed"])["moments"]["AA1"]
            self.assertEqual((v.lo, v.hi), (Q(1, 2), Q(1, 2)))

    def test_original_domain_guard(self):
        h = history(); h["domain"]["rA"] = ["1", "2"]
        with self.assertRaisesRegex(InputError, "original full domain"):
            self.bridge.prepare(h)

    def test_same_source_guard(self):
        h = history(); h["blocks"][0]["source_instance"] = "other-source"
        with self.assertRaisesRegex(InputError, "one source"):
            self.bridge.prepare(h)

    def test_changed_model_map_or_raw_unit_refused(self):
        for key, value in (("model", "different-source-family"), ("observation_map", "estimated-four-taxon-tree"), ("quantity", "raw_laplace_moment")):
            h = history(); h[key] = value
            with self.assertRaisesRegex(InputError, "fixed model|shifted observation map"):
                self.bridge.prepare(h)

    def test_exact_law_and_anytime_claim_refused(self):
        h = history(); h["blocks"][0]["evidence_kind"] = "exact_law"
        with self.assertRaisesRegex(InputError, "exact-law"):
            self.bridge.prepare(h)
        h = history(); h["confidence_mode"] = "anytime_prefix"
        with self.assertRaisesRegex(InputError, "fixed-block mode"):
            self.bridge.prepare(h)

    def test_missing_feature_and_nonexact_number_refused(self):
        h = history(); del h["blocks"][0]["shifted_mean_box"]["AA1"]
        with self.assertRaises(self.bridge.core.EvidenceInvalid):
            self.bridge.prepare(h)
        for v in (0.75, True):
            h = history(); h["blocks"][0]["shifted_mean_box"]["AA1"][0] = v
            with self.assertRaises(self.bridge.core.EvidenceInvalid):
                self.bridge.prepare(h)

    def test_duplicate_block_id_refused(self):
        with self.assertRaisesRegex(InputError, "unique constraint"):
            self.bridge.prepare(history([block(), block()], "cumulative", "1/10"))

    def test_actual_extractor_preserves_joint_counts_and_refuses_duplicate_loci(self):
        locus = {"id": "synthetic-panel", "columns": [1, 2],
                 "calls": {k: "AA" for k in ("A1", "A2", "B1", "B2", "C1", "C2")}}
        d = {"schema": "complete-six-copy-two-site-loci-v1", "loci": [locus]}
        selection = [{"id": locus["id"], "columns": locus["columns"]}]
        pin = self.bridge.core.sha(self.bridge.core.canonical(selection))
        result = self.bridge.extract(d, 1, pin)
        self.assertEqual(result["counts"], dict.fromkeys(FEATURES, 1))
        self.assertFalse(result["within_locus_feature_independence_assumed"])
        d["loci"].append(deepcopy(locus))
        with self.assertRaisesRegex(self.bridge.core.EvidenceInvalid, "duplicate locus"):
            self.bridge.extract(d, 2, pin)

    def test_actual_extractor_refuses_incomplete_panel(self):
        d = {"schema": "complete-six-copy-two-site-loci-v1", "loci": [
            {"id": "one", "columns": [1, 2], "calls": {"A1": "AA"}}]}
        with self.assertRaises(self.bridge.core.EvidenceInvalid):
            self.bridge.extract(d, 1, "0" * 64)

    def test_narrow_components_have_wide_union(self):
        p = self.bridge.prepare(history())
        with tempfile.TemporaryDirectory() as tmp:
            parsed, _ = self.parse(p, tmp)
            left = {k: [v[0], v[0]] for k, v in DOMAIN.items()}
            right = {k: [v[1], v[1]] for k, v in DOMAIN.items()}
            self.assertTrue(self.bridge.geometry_only(parsed, [left])["whole_union_width_target_met"])
            self.assertTrue(self.bridge.geometry_only(parsed, [right])["whole_union_width_target_met"])
            union = self.bridge.geometry_only(parsed, [left, right])
            self.assertFalse(union["whole_union_width_target_met"])
            self.assertEqual({v["normalized_ratio"] for v in union["widths"].values()}, {"1"})
            self.assertFalse(union["numeric_journal_validated"])
            self.assertFalse(union["data_confidence_certificate_issued"])

    def test_empty_geometry_never_meets_accuracy(self):
        with tempfile.TemporaryDirectory() as tmp:
            parsed, _ = self.parse(self.bridge.prepare(history()), tmp)
            out = self.bridge.geometry_only(parsed, [])
            self.assertFalse(out["nonempty"])
            self.assertFalse(out["whole_union_width_target_met"])

    def mock_checker(self, parsed):
        frontier = {"r": self.bridge.engine.initial_cell(parsed)}
        return self.bridge.checker.output(parsed, frontier, "normal_validated",
                                         {"complete_numeric_replay": True, "mocked_plumbing_only": True})

    def test_mocked_replay_plumbing_stays_unadmitted(self):
        p = self.bridge.prepare(history())
        with tempfile.TemporaryDirectory() as tmp:
            parsed, path = self.parse(p, tmp)
            with patch.object(self.bridge.checker, "recover", return_value=self.mock_checker(parsed)) as mocked:
                out = self.bridge.replay(p, path, Path(tmp) / "no-real-journal")
            mocked.assert_called_once()
            self.assertEqual(out["status"], "UNKNOWN_OUTER_COVER")
            self.assertFalse(out["scientific_admission_verified"])
            self.assertFalse(out["data_confidence_certificate_issued"])

    def test_mocked_empty_normal_vs_recovered_prefix(self):
        p = self.bridge.prepare(history())
        with tempfile.TemporaryDirectory() as tmp:
            parsed, path = self.parse(p, tmp)
            for mode, complete, expected in (
                ("normal_validated", True, "UNADMITTED_CONDITIONAL_CONFLICT"),
                ("recovered_same_process_validated_prefix", False, "UNKNOWN_OUTER_COVER")):
                mocked_result = self.bridge.checker.output(parsed, {}, mode,
                    {"complete_numeric_replay": complete, "resource_limited": not complete,
                     "mocked_plumbing_only": True})
                with patch.object(self.bridge.checker, "recover", return_value=mocked_result):
                    out = self.bridge.replay(p, path, Path(tmp) / "mocked-empty-journal")
                self.assertEqual(out["status"], expected)
                self.assertFalse(out["data_confidence_certificate_issued"])

    def test_post_use_authentication_failure_prevents_return(self):
        with patch.object(self.bridge.core, "extract", return_value={"mocked_plumbing_only": True}), \
             patch.object(self.bridge, "_authenticate", side_effect=[None, InputError("post-extractor change")]):
            with self.assertRaisesRegex(InputError, "post-extractor"):
                self.bridge.extract({}, 1, "0" * 64)
        p = self.bridge.prepare(history())
        with tempfile.TemporaryDirectory() as tmp:
            parsed, path = self.parse(p, tmp)
            result = self.mock_checker(parsed)
            with patch.object(self.bridge.checker, "recover", return_value=result), \
                 patch.object(self.bridge, "_authenticate", side_effect=[None, None, InputError("post-checker change")]):
                with self.assertRaisesRegex(InputError, "post-checker"):
                    self.bridge.replay(p, path, Path(tmp) / "mocked-journal")

    def test_mocked_stale_replay_preserves_old_identity(self):
        old = self.bridge.prepare(history([block("old", "1/2", "1", "1/10")], alpha="1/10"))
        new = self.bridge.prepare(history([block("old", "1/2", "1", "1/10"), block()], "cumulative", "3/20"))
        with tempfile.TemporaryDirectory() as tmp:
            parsed, path = self.parse(old, tmp)
            with patch.object(self.bridge.checker, "recover", return_value=self.mock_checker(parsed)):
                out = self.bridge.stale_replay(old, new, path, Path(tmp) / "mocked-journal")
            self.assertEqual(out["validated_request_sha256"], old.request_sha256)
            self.assertEqual(out["new_request_sha256"], new.request_sha256)
            self.assertEqual(out["conditional_error_allowance"], "3/20")
            self.assertFalse(out["old_journal_relabelled"])
            self.assertFalse(out["new_data_numerically_processed"])

    def test_fresh_only_stale_reuse_refused_before_checker(self):
        p = self.bridge.prepare(history())
        with patch.object(self.bridge.checker, "recover") as mocked:
            with self.assertRaisesRegex(InputError, "fresh-only nesting"):
                self.bridge.stale_replay(p, p, "unused", "unused")
            mocked.assert_not_called()

    def test_stale_noncontained_box_refused_before_checker(self):
        old = self.bridge.prepare(history([block("old", "4/5", "17/20")]))
        new = self.bridge.prepare(history([block()], "cumulative"))
        with patch.object(self.bridge.checker, "recover") as mocked:
            with self.assertRaisesRegex(InputError, "not contained"):
                self.bridge.stale_replay(old, new, "unused", "unused")
            mocked.assert_not_called()

    def test_geometry_outside_original_domain_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            parsed, _ = self.parse(self.bridge.prepare(history()), tmp)
            box = deepcopy(DOMAIN); box["rA"] = ["0", "1"]
            with self.assertRaisesRegex(InputError, "outside original domain"):
                self.bridge.geometry_only(parsed, [box])

    def test_prepared_mutation_and_request_overwrite_refused(self):
        p = self.bridge.prepare(history())
        bad = Prepared(p.history_json, b"{}", p.status, p.selected_ids, p.error_allowance)
        with self.assertRaisesRegex(InputError, "prepared record changed"):
            self.bridge.read_prepared(bad, "unused")
        with tempfile.TemporaryDirectory() as tmp:
            _, path = self.parse(p, tmp)
            with self.assertRaises(FileExistsError):
                self.bridge.write_request(p, path)


if __name__ == "__main__":
    unittest.main(verbosity=2)
