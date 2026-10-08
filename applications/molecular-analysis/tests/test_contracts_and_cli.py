"""Boundary and deterministic mocked integration tests; no biological claims."""
import copy
from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
from unittest import mock

from molecular_apps.cli import execute
from molecular_apps.contracts import (MolecularError, context_from_dict,
                                      endpoint_from_dict, parse_json,
                                      sequence_sha256, validate_prediction)
from molecular_apps.providers import AlphaGenomeProvider, SyntheticProvider

ROOT = Path(__file__).resolve().parents[1]


def fixture():
    sequence = "ACGT" * 16
    context = {"window": {"assembly": "hg38", "chromosome": "chr1", "start0": 100,
                            "sequence": sequence, "guard_sequence": "ACGTACGT",
                            "source": "synthetic software fixture, not genomic evidence",
                            "sha256": sequence_sha256(sequence + "ACGTACGT")},
               "transcript": {"gene_id": "SYNTHETIC_GENE", "transcript_id": "SYNTHETIC_TX",
                              "start0": 104, "end0": 160, "strand": "+",
                              "source": "synthetic annotation", "version": "fixture-v1",
                              "exons": [[104, 120], [140, 160]]},
               "tissue": "UBERON:0002107", "model_version": "synthetic-v1",
               "output_types": ["RNA_SEQ", "SPLICE_SITES", "SPLICE_SITE_USAGE"],
               "preprocessing": "forward_reference_fixed_left_v1"}
    endpoints = [{"id": "expr", "family": "expression", "output_type": "RNA_SEQ",
                  "aggregation": "mean", "scale": "log", "start0": 104, "end0": 160},
                 {"id": "splice", "family": "splice_usage", "output_type": "SPLICE_SITE_USAGE",
                  "aggregation": "mean", "scale": "linear", "start0": 104, "end0": 160}]
    return {"context": context, "endpoints": endpoints,
            "variants": [{"id": "A", "chromosome": "chr1", "position": 109, "ref": "A", "alt": "G"},
                         {"id": "B", "chromosome": "chr1", "position": 145, "ref": "A", "alt": "T"}],
            "phase": {"kind": "hypothetical", "evidence": "synthetic scenario"}}


class ContractTests(unittest.TestCase):
    def assert_refused(self, callback, code=None):
        with self.assertRaises(MolecularError) as caught:
            callback()
        if code:
            self.assertEqual(caught.exception.code, code)
        return caught.exception

    def test_valid_context_and_endpoints(self):
        f = fixture(); c = context_from_dict(f["context"])
        for e in f["endpoints"]:
            endpoint_from_dict(e, c)

    def test_duplicate_json_key(self):
        self.assert_refused(lambda: parse_json('{"x":1,"x":2}'), "DUPLICATE_KEY")

    def test_nonfinite_json(self):
        for value in ("NaN", "Infinity", "-Infinity"):
            self.assert_refused(lambda: parse_json('{"x":' + value + '}'), "JSON")

    def test_overflowing_json_float(self):
        self.assert_refused(lambda: parse_json('{"nested":[1e999]}'), "JSON")

    def test_huge_integer_pseudocount_is_invalid_input(self):
        f = fixture(); f["endpoints"][0]["pseudocount"] = 10**400
        provider = mock.Mock()
        error = self.assert_refused(lambda: execute("haplotype", f, provider), "PSEUDOCOUNT")
        self.assertEqual(error.status, "INVALID_INPUT")
        provider.predict_sequence.assert_not_called()

    def test_unknown_context_field(self):
        c = fixture()["context"]; c["guess"] = 1
        self.assert_refused(lambda: context_from_dict(c), "SCHEMA")

    def test_reference_hash_includes_guard(self):
        c = fixture()["context"]; c["window"]["guard_sequence"] = "TTTT"
        self.assert_refused(lambda: context_from_dict(c), "REFERENCE_HASH")

    def test_wrong_assembly(self):
        c = fixture()["context"]; c["window"]["assembly"] = "hg19"
        self.assertEqual(self.assert_refused(lambda: context_from_dict(c)).status, "UNSUPPORTED")

    def test_boolean_coordinate(self):
        c = fixture()["context"]; c["window"]["start0"] = True
        self.assert_refused(lambda: context_from_dict(c), "COORDINATE")

    def test_negative_coordinate(self):
        c = fixture()["context"]; c["window"]["start0"] = -1
        self.assert_refused(lambda: context_from_dict(c), "COORDINATE")

    def test_strand_error(self):
        c = fixture()["context"]; c["transcript"]["strand"] = "."
        self.assert_refused(lambda: context_from_dict(c), "STRAND")

    def test_partial_transcript_refused(self):
        c = fixture()["context"]; c["transcript"]["end0"] = 200
        self.assert_refused(lambda: context_from_dict(c), "TRANSCRIPT_WINDOW")

    def test_overlapping_exons_refused(self):
        c = fixture()["context"]; c["transcript"]["exons"] = [[104, 145], [140, 160]]
        self.assert_refused(lambda: context_from_dict(c), "EXON")

    def test_unrequested_endpoint(self):
        f = fixture(); f["endpoints"][0]["output_type"] = "ATAC"
        self.assert_refused(lambda: endpoint_from_dict(f["endpoints"][0], context_from_dict(f["context"])), "ENDPOINT_OUTPUT")

    def test_percentile_scale_refused(self):
        f = fixture(); f["endpoints"][0]["scale"] = "AVI_percentile"
        self.assert_refused(lambda: endpoint_from_dict(f["endpoints"][0], context_from_dict(f["context"])), "SCALE")

    def test_nonpositive_pseudocount(self):
        f = fixture(); f["endpoints"][0]["pseudocount"] = 0
        self.assert_refused(lambda: endpoint_from_dict(f["endpoints"][0], context_from_dict(f["context"])), "PSEUDOCOUNT")

    def test_mock_reproducibility(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider()
        a = p.predict_sequence(c, "REF", c.window.sequence)
        self.assertEqual(a, p.predict_sequence(c, "REF", c.window.sequence))
        self.assertEqual(a.evidence, "MOCK_SYNTHETIC")

    def test_unsupported_tissue(self):
        c = replace(context_from_dict(fixture()["context"]), tissue="UBERON:9999999")
        self.assertEqual(self.assert_refused(lambda: SyntheticProvider().capabilities(c)).status, "UNSUPPORTED")

    def test_unsupported_output(self):
        c = replace(context_from_dict(fixture()["context"]), output_types=("SPLICE_JUNCTIONS",))
        self.assertEqual(self.assert_refused(lambda: SyntheticProvider().capabilities(c)).status, "UNSUPPORTED")

    def test_mismatched_settings(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        self.assert_refused(lambda: validate_prediction(c, replace(p, settings_sha256="wrong")), "MISMATCHED_SETTINGS")

    def test_mismatched_sequence(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        self.assert_refused(lambda: validate_prediction(c, p, expected_sequence_sha256="wrong"), "MISMATCHED_SEQUENCE")

    def test_mismatched_track_window(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        t = replace(p.tracks[0], interval_start0=101)
        self.assert_refused(lambda: validate_prediction(c, replace(p, tracks=(t,))), "MISMATCHED_WINDOW")

    def test_mismatched_track_strand(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        self.assert_refused(lambda: validate_prediction(c, replace(p, tracks=(replace(p.tracks[0], strand="-"),))), "STRAND")

    def test_direct_splice_sites_can_be_tissue_agnostic(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        t = replace(p.tracks[1], tissue="TISSUE_AGNOSTIC", metadata={"tissue_specific": False})
        validate_prediction(c, replace(p, tracks=(t,)))

    def test_tissue_agnostic_expression_refused(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        t = replace(p.tracks[0], tissue="TISSUE_AGNOSTIC", metadata={"tissue_specific": False})
        self.assert_refused(lambda: validate_prediction(c, replace(p, tracks=(t,))), "TISSUE")

    def test_nonfinite_track_refused(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        t = replace(p.tracks[0], values=(float("nan"),) * 64)
        self.assert_refused(lambda: validate_prediction(c, replace(p, tracks=(t,))), "TRACK_VALUES")

    def test_huge_integer_track_refused(self):
        c = context_from_dict(fixture()["context"]); p = SyntheticProvider().predict_sequence(c, "REF", c.window.sequence)
        t = replace(p.tracks[0], values=(10**400,) * 64)
        self.assert_refused(lambda: validate_prediction(c, replace(p, tracks=(t,))), "TRACK_VALUES")

    def test_live_access_has_exact_blockers_without_network(self):
        with mock.patch.dict(os.environ, {}, clear=True):
            blockers = AlphaGenomeProvider().blockers()
        self.assertTrue(any("terms" in b for b in blockers))
        self.assertTrue(any("API_KEY" in b for b in blockers))


class MockedIntegrationTests(unittest.TestCase):
    def test_malformed_phase_is_invalid_input_without_prediction(self):
        for kind in ([], {}, None, True):
            f = fixture(); f["phase"]["kind"] = kind
            provider = mock.Mock()
            result = execute("haplotype", f, provider)
            self.assertEqual(result["status"], "INVALID_INPUT")
            provider.predict_sequence.assert_not_called()

    def test_family_and_pas_order_preflight_without_prediction(self):
        for mutation in ("family", "overlap", "strand"):
            f = fixture()
            if mutation == "family":
                f["endpoints"][0]["family"] = "splice_sites"
            else:
                f["endpoints"] = [{"id": "pas", "family": "polyadenylation", "output_type": "RNA_SEQ", "aggregation": "site_ratio", "scale": "linear", "start0": 104, "end0": 160, "site_windows": [[108, 120], [112, 124]] if mutation == "overlap" else [[140, 150], [108, 120]], "site_annotation_source": "synthetic", "site_annotation_version": "test-v1"}]
            provider = mock.Mock()
            with self.assertRaises(MolecularError): execute("haplotype", f, provider)
            provider.predict_sequence.assert_not_called()

    def test_unsupported_endpoint_preflight_never_calls_provider(self):
        for mode in ("haplotype", "rna"):
            f = fixture(); f["endpoints"][0]["aggregation"] = "max"
            if mode == "rna":
                f = {"context": f["context"], "endpoints": f["endpoints"], "sequence_scenarios": {"REF": f["context"]["window"]["sequence"]}}
            provider = mock.Mock()
            with self.assertRaises(MolecularError) as error:
                execute(mode, f, provider)
            self.assertEqual(error.exception.code, "EXPRESSION_AGGREGATION")
            provider.capabilities.assert_not_called(); provider.predict_sequence.assert_not_called()

    def test_pas_preflight_never_calls_provider(self):
        f = fixture(); f["endpoints"] = [{"id": "pas", "family": "polyadenylation", "output_type": "RNA_SEQ", "aggregation": "site_ratio", "scale": "linear", "start0": 104, "end0": 160}]
        provider = mock.Mock()
        with self.assertRaises(MolecularError) as error:
            execute("haplotype", f, provider)
        self.assertEqual(error.exception.code, "PAS_WINDOWS_REQUIRED")
        provider.predict_sequence.assert_not_called()

    def test_haplotype_four_matched_scenarios(self):
        r = execute("haplotype", fixture(), SyntheticProvider())
        self.assertEqual(r["status"], "SUCCESS")
        self.assertFalse(r["biological_conclusion_established"])
        self.assertIn("MOCK_SYNTHETIC", json.dumps(r))
        self.assertIn("AB", json.dumps(r))

    def test_unknown_phase_does_not_become_cis(self):
        f = fixture(); f["phase"] = {"kind": "unknown", "evidence": ""}
        r = execute("haplotype", f, SyntheticProvider())
        self.assertEqual(r["status"], "UNKNOWN")
        self.assertFalse(r["biological_conclusion_established"])

    def test_rna_alternative_sequence_separate_from_haplotype(self):
        f = fixture(); seq = f["context"]["window"]["sequence"]
        r = execute("rna", {"context": f["context"], "endpoints": f["endpoints"],
                            "sequence_scenarios": {"REF": seq, "ALT": seq[:8]+"G"+seq[9:]}}, SyntheticProvider())
        self.assertEqual(r["status"], "SUCCESS")
        self.assertFalse(r["biological_conclusion_established"])
        self.assertEqual(set(r["input_sequence_sha256"]), {"REF", "ALT"})

    def test_invalid_ref_rna(self):
        f = fixture()
        self.assertRaises(MolecularError, execute, "rna", {"context": f["context"], "endpoints": f["endpoints"], "sequence_scenarios": {"REF": "A"*64}}, SyntheticProvider())

    def test_unknown_cli_field_refused(self):
        f = fixture(); f["guess_phase"] = True
        self.assertRaises(MolecularError, execute, "haplotype", f, SyntheticProvider())

    def test_cli_stdin_is_deterministic_and_synthetic(self):
        f = fixture(); data = json.dumps({"context": f["context"], "endpoints": f["endpoints"], "sequence_scenarios": {"REF": f["context"]["window"]["sequence"]}})
        command = [sys.executable, "-m", "molecular_apps", "rna", "-", "--provider", "mock"]
        a = subprocess.run(command, input=data, text=True, capture_output=True, cwd=ROOT, timeout=30)
        b = subprocess.run(command, input=data, text=True, capture_output=True, cwd=ROOT, timeout=30)
        self.assertEqual(a.returncode, 0, a.stderr); self.assertEqual(a.stdout, b.stdout)
        self.assertEqual(a.stderr, ""); self.assertIn("MOCK_SYNTHETIC", a.stdout)


if __name__ == "__main__":
    unittest.main()
