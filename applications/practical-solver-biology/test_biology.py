"""Consequential input/identity and offline-only contract controls."""
import copy
import hashlib
import json
import os
from pathlib import Path
import socket
import tempfile
import unittest
from unittest.mock import patch

import ingestion
import offline


class BiologicalInputTests(unittest.TestCase):
    def test_archived_obstruction_and_literal_counts(self):
        result = ingestion.audit_archived_panel()
        self.assertEqual(result["counts"], {"AA1": 704, "AB1": 660, "AB2": 594,
            "AC1": 623, "AC2": 550, "BB1": 730, "BC1": 661, "BC2": 578, "CC1": 794})
        self.assertEqual(result["normalized_rA_separation"], "3/55")
        self.assertTrue(result["fixed_band_all_nine_width_goal_impossible"])
        self.assertFalse(result["scientific_confidence_admitted"])

    def test_conversion_boundary_and_empty_projection(self):
        self.assertEqual(ingestion.shifted_to_raw(["3/4", "7/8"]), ["1/2", "3/4"])
        self.assertEqual(ingestion.shifted_to_raw(["1/4", "3/4"]), ["0", "1/2"])
        self.assertEqual(ingestion.shifted_to_raw(["1/2", "1/2"]), ["0", "0"])
        for bounds in (["0", "1/4"], ["3/4", "1/2"], ["-1/2", "1"]):
            with self.assertRaises(ValueError):
                ingestion.shifted_to_raw(bounds)

    def test_incomplete_unphased_duplicate_and_selected_columns_refuse(self):
        extractor = ingestion.authenticated_extractor()
        dataset = extractor.read(ingestion.SOURCE / "declared-model/DATASET.json",
                                 ingestion.PINS["declared-model/DATASET.json"])
        request = extractor.read(ingestion.SOURCE / "composition-attempt1/ANALYSIS-REQUEST.json",
                                 ingestion.PINS["composition-attempt1/ANALYSIS-REQUEST.json"])
        for mutation in ("missing_copy", "unphased_call", "duplicate_id", "changed_columns", "missing_locus"):
            changed = copy.deepcopy(dataset)
            if mutation == "missing_copy":
                del changed["loci"][0]["calls"]["A2"]
            elif mutation == "unphased_call":
                changed["loci"][0]["calls"]["A1"] = "GN"
            elif mutation == "duplicate_id":
                changed["loci"][1]["id"] = changed["loci"][0]["id"]
            elif mutation == "changed_columns":
                changed["loci"][0]["columns"] = [1, 3]
            else:
                changed["loci"].pop()
            with self.subTest(mutation=mutation), self.assertRaises(extractor.EvidenceInvalid):
                extractor.extract(changed, request["expected_loci"], request["selection_sha256"])
        with self.assertRaises(extractor.InputResource):
            extractor.extract(dataset, 100001, request["selection_sha256"])

    def test_literal_json_duplicate_nonfinite_and_tamper_refuse(self):
        extractor = ingestion.authenticated_extractor()
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "bad.json"
            for raw in (b'{"x":1,"x":2}', b'{"x":1.5}', b'{"x":NaN}'):
                path.write_bytes(raw)
                with self.assertRaises(extractor.EvidenceInvalid):
                    extractor.read(path, hashlib.sha256(raw).hexdigest())
            with self.assertRaises(extractor.EvidenceInvalid):
                extractor.read(path, "0" * 64)


class OfflineMolecularTests(unittest.TestCase):
    def test_offline_matched_context_no_network_no_secret_disclosure(self):
        sentinel = "TEST_ONLY_SECRET_NOT_A_REAL_KEY"
        with patch.dict(os.environ, {"ALPHAGENOME_API_KEY": sentinel}), \
             patch.object(socket.socket, "connect", side_effect=AssertionError("network forbidden")), \
             patch.object(socket, "getaddrinfo", side_effect=AssertionError("DNS forbidden")):
            result, request = offline.compute_offline()
        self.assertEqual(result["status"], "SUCCESS")
        self.assertEqual(set(request["sequence_scenarios"]), {"REF", "A", "B", "AB"})
        self.assertEqual(len({len(s) for s in request["sequence_scenarios"].values()}), 1)
        self.assertEqual(len(set(result["input_sequence_sha256"].values())), 4)
        self.assertEqual(result["live_api_calls"], 0)
        self.assertFalse(result["credentials_accessed"])
        self.assertNotIn(sentinel, json.dumps(result))
        self.assertFalse(result["biological_conclusion_established"])
        self.assertFalse(result["ancestry_observation_admitted"])
        self.assertEqual({e["family"] for e in result["endpoints"].values()},
                         {"expression", "splice_usage", "polyadenylation"})
        for key, endpoint in result["endpoints"].items():
            values = endpoint["values_by_scenario"]
            self.assertAlmostEqual(result["interactions"][key]["value"],
                                   values["AB"] - values["A"] - values["B"] + values["REF"])
        self.assertEqual(result["endpoints"]["pas-proxy"]["method"], "two_annotated_window_coverage_ratio_v1")

    def test_mismatched_alternative_and_reference_refuse(self):
        for mutation in ("short_a", "wrong_ref", "missing_ab"):
            request = offline.matched_request()
            if mutation == "short_a":
                request["sequence_scenarios"]["A"] = request["sequence_scenarios"]["A"][:-1]
            elif mutation == "wrong_ref":
                request["sequence_scenarios"]["REF"] = request["sequence_scenarios"]["A"]
            else:
                del request["sequence_scenarios"]["AB"]
            with self.subTest(mutation=mutation), self.assertRaises(Exception):
                offline.compute_offline(request)

    def test_tampered_inherited_source_refuses_before_execution(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for relative in offline.PINS:
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes((offline.INHERITED / relative).read_bytes())
            path = root / "molecular_apps/providers.py"
            path.write_bytes(path.read_bytes() + b"\nraise AssertionError('should never execute')\n")
            with patch.object(offline, "INHERITED", root), self.assertRaisesRegex(ValueError, "identity changed"):
                offline.compute_offline()

    def test_existing_export_preserved_before_computation(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder) / "existing"
            output.mkdir()
            sentinel = output / "old.json"
            sentinel.write_text("preserve me")
            with patch.object(offline, "compute_offline", side_effect=AssertionError("must not compute")):
                with self.assertRaises(FileExistsError):
                    offline.run_offline(output)
            self.assertEqual(sentinel.read_text(), "preserve me")


if __name__ == "__main__":
    unittest.main()
