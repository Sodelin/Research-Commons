"""Offline synthetic RNA calculations and provider integration; no model call."""
from dataclasses import replace
import json
import math
import unittest

from molecular_apps.contracts import (Context, EndpointSpec, MolecularError,
                                     Prediction, PredictionTrack, ReferenceWindow,
                                     TranscriptAnnotation, sequence_sha256)
from molecular_apps.providers import SyntheticProvider
from molecular_apps.rna_processing import analyse_rna


def context(strand="+", outputs=("RNA_SEQ", "SPLICE_SITES", "SPLICE_SITE_USAGE")):
    sequence = "ACGTACGTACGT"
    return Context(ReferenceWindow("hg38", "chr1", 100, sequence, "ACGT",
                                   "synthetic software fixture", sequence_sha256(sequence + "ACGT")),
                   TranscriptAnnotation("SYNTHETIC_GENE", "SYNTHETIC_TX", 101, 111,
                                        strand, "synthetic annotation", "fixture-v1", ((101, 104), (108, 111))),
                   "UBERON:0002107", "synthetic-v1", outputs, "forward_reference_fixed_left_v1")


def endpoint(family="expression", output_type="RNA_SEQ", aggregation="mean", scale="linear", **kw):
    if family == "polyadenylation" and kw.get("site_windows"):
        kw.setdefault("site_annotation_source", "synthetic PAS-site annotation")
        kw.setdefault("site_annotation_version", "synthetic-sites-v1")
    return EndpointSpec(kw.pop("id", "e"), family, output_type, aggregation, scale,
                        kw.pop("start0", 101), kw.pop("end0", 111), **kw)


def prediction(c, scenario, values, output_type="RNA_SEQ", *, aligned=True, evidence="MOCK_SYNTHETIC"):
    metadata = {"synthetic": True, "name": f"synthetic-{output_type}"}
    if aligned:
        metadata["alignment"] = "reference_retained"
    track = PredictionTrack(output_type, tuple(values), c.window.start0, 1, c.transcript.strand,
                            c.tissue, c.transcript.gene_id, c.transcript.transcript_id, metadata)
    digest = sequence_sha256(c.window.sequence if scenario == "REF" else "T" * len(c.window.sequence))
    return Prediction(scenario, digest, c.settings_sha256, (track,), evidence)


class RnaEndpointTests(unittest.TestCase):
    def score(self, c, e, ref, alt, output_type="RNA_SEQ"):
        return analyse_rna(c, (e,), {"REF": prediction(c, "REF", ref, output_type),
                                    "ALT": prediction(c, "ALT", alt, output_type)})["endpoints"][e.id]

    def test_expression_exon_mask_excludes_introns(self):
        c = context()
        ref = [99, 1, 2, 3, 999, 999, 999, 999, 4, 5, 6, 99]
        alt = [99, 2, 4, 6, 0, 0, 0, 0, 8, 10, 12, 99]
        result = self.score(c, endpoint(), ref, alt)
        self.assertEqual(result["raw_values_by_scenario"], {"REF": 3.5, "ALT": 7.0})
        self.assertEqual(result["reference_mask_base_count"], 6)
        self.assertEqual(result["reference_mask_windows"], [[101, 104], [108, 111]])
        self.assertEqual(result["changes_vs_reference"]["ALT"], 3.5)
        self.assertEqual(result["direction_by_scenario"]["ALT"], "increase")

    def test_sum_and_log_declared_scale(self):
        c = context()
        result = self.score(c, endpoint(aggregation="sum", scale="log", pseudocount=1), [1]*12, [2]*12)
        self.assertEqual(result["raw_values_by_scenario"], {"REF": 6, "ALT": 12})
        self.assertAlmostEqual(result["changes_vs_reference"]["ALT"], math.log(13)-math.log(7))
        self.assertFalse(result["formula_matches_recommended_expression_transform"])

    def test_official_expression_mean_log_mask_condition(self):
        c = context()
        result = self.score(c, endpoint(scale="log"), [1]*12, [2]*12)
        self.assertTrue(result["formula_matches_recommended_expression_transform"])
        clipped = self.score(c, endpoint(scale="log", end0=109), [1]*12, [2]*12)
        self.assertTrue(clipped["formula_matches_recommended_expression_transform"])
        self.assertIn("proxy", clipped["limitations"][0])

    def test_log2_zero_and_fixed_reference_denominator(self):
        c = context()
        alt = [2]*12
        alt[101-c.window.start0] = 0  # A mapped deletion; original six-base mask stays fixed.
        result = self.score(c, endpoint(scale="log2", pseudocount=1), [2]*12, alt)
        self.assertEqual(result["raw_values_by_scenario"]["ALT"], 10/6)
        self.assertAlmostEqual(result["changes_vs_reference"]["ALT"], math.log2(10/6+1)-math.log2(3))
        zero = self.score(c, endpoint(scale="log2", pseudocount=0.5), [0]*12, [0]*12)
        self.assertEqual(zero["values_by_scenario"]["REF"], -1)
        self.assertEqual(zero["direction_by_scenario"]["ALT"], "unchanged")

    def test_splice_modalities_and_difference_of_maxima(self):
        c = context()
        ref, alt = [0]*12, [0]*12
        ref[1], ref[2], alt[1], alt[2] = 0.9, 0.1, 0.1, 0.9
        for family, output_type in (("splice_sites", "SPLICE_SITES"), ("splice_usage", "SPLICE_SITE_USAGE")):
            result = self.score(c, endpoint(family, output_type, "max"), ref, alt, output_type)
            self.assertEqual(result["semantics"], "derived")
            self.assertEqual(result["source_output_semantics"], "direct_model_prediction")
            self.assertEqual(result["output_type"], output_type)
            self.assertEqual(result["changes_vs_reference"]["ALT"], 0)
            self.assertEqual(result["max_absolute_positional_change_vs_reference"]["ALT"], 0.8)
            self.assertFalse(result["formula_matches_recommended_expression_transform"])

    def test_splice_probability_out_of_range_refused(self):
        c = context()
        with self.assertRaises(MolecularError) as caught:
            self.score(c, endpoint("splice_usage", "SPLICE_SITE_USAGE"), [0.5]*12, [2]*12, "SPLICE_SITE_USAGE")
        self.assertEqual(caught.exception.code, "PROBABILITY_RANGE")

    def test_tissue_agnostic_splice_sites_preserved(self):
        c = context()
        ref = prediction(c, "REF", [0.1]*12, "SPLICE_SITES")
        track = replace(ref.tracks[0], tissue="TISSUE_AGNOSTIC", metadata={**ref.tracks[0].metadata, "tissue_specific": False})
        result = analyse_rna(c, (endpoint("splice_sites", "SPLICE_SITES"),), {"REF": replace(ref, tracks=(track,))})
        self.assertEqual(result["status"], "SUCCESS")
        self.assertEqual(result["endpoints"]["e"]["track_metadata_by_scenario"]["REF"]["tissue"], "TISSUE_AGNOSTIC")

    def test_pas_proxy_strand_order_and_log_ratio(self):
        for strand, windows in (("+", ((101, 103), (109, 111))), ("-", ((109, 111), (101, 103)))):
            c = context(strand)
            ref, alt = [0]*12, [0]*12
            for start, end in windows[:1]:
                for pos in range(start, end):
                    ref[pos-100] = alt[pos-100] = 1
            for start, end in windows[1:]:
                for pos in range(start, end):
                    ref[pos-100], alt[pos-100] = 3, 7
            result = self.score(c, endpoint("polyadenylation", "RNA_SEQ", "site_ratio", "log", pseudocount=1, site_windows=windows), ref, alt)
            self.assertEqual(result["semantics"], "derived")
            self.assertAlmostEqual(result["raw_values_by_scenario"]["REF"], 2)
            self.assertAlmostEqual(result["raw_values_by_scenario"]["ALT"], 4)
            self.assertAlmostEqual(result["changes_vs_reference"]["ALT"], math.log(2))
            self.assertFalse(result["formula_matches_recommended_expression_transform"])
            self.assertEqual(result["site_annotation_version"], "synthetic-sites-v1")
            self.assertEqual(result["window_values_by_scenario"]["ALT"], {"proximal_mean": 1, "distal_mean": 7})

    def test_pas_missing_and_overlapping_windows(self):
        c = context()
        result = self.score(c, endpoint("polyadenylation", "RNA_SEQ", "site_ratio"), [1]*12, [1]*12)
        self.assertEqual(result["status"], "UNSUPPORTED")
        self.assertEqual(result["code"], "PAS_WINDOWS_REQUIRED")
        with self.assertRaises(MolecularError) as caught:
            self.score(c, endpoint("polyadenylation", "RNA_SEQ", "site_ratio", site_windows=((101,105),(104,108))), [1]*12, [1]*12)
        self.assertEqual(caught.exception.code, "PAS_WINDOW_ORDER")

    def test_no_fabricated_junction_or_psi(self):
        c = context(outputs=("RNA_SEQ", "SPLICE_JUNCTIONS"))
        endpoints = (endpoint("splice_junctions", "SPLICE_JUNCTIONS", id="junction"),
                     endpoint("psi", "RNA_SEQ", id="psi"))
        result = analyse_rna(c, endpoints, {"REF": prediction(c, "REF", [1]*12)})
        self.assertEqual(result["status"], "UNSUPPORTED")
        self.assertEqual(result["endpoints"]["junction"]["code"], "JUNCTION_ADAPTER_UNAVAILABLE")
        self.assertEqual(result["endpoints"]["psi"]["code"], "PSI_METHOD_UNAVAILABLE")
        self.assertEqual(result["endpoints"]["psi"]["values_by_scenario"], {})

    def test_missing_modality_never_falls_back_to_rna(self):
        c = context()
        result = analyse_rna(c, (endpoint(id="expr"), endpoint("splice_usage", "SPLICE_SITE_USAGE", id="usage")),
                             {"REF": prediction(c, "REF", [1]*12)})
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(result["endpoints"]["usage"]["code"], "MISSING_OUTPUT")
        self.assertEqual(result["endpoints"]["expr"]["status"], "SUCCESS")

    def test_family_output_and_unsupported_aggregation(self):
        c = context()
        r = self.score(c, endpoint("splice_usage", "RNA_SEQ"), [1]*12, [1]*12)
        self.assertEqual(r["code"], "FAMILY_OUTPUT")
        r = self.score(c, endpoint(aggregation="max"), [1]*12, [1]*12)
        self.assertEqual(r["code"], "EXPRESSION_AGGREGATION")

    def test_unaligned_alt_is_unavailable_but_alt_digest_is_not_reference(self):
        c = context()
        ref = prediction(c, "REF", [1]*12)
        alt = prediction(c, "ALT", [2]*12, aligned=False)
        r = analyse_rna(c, (endpoint(),), {"REF": ref, "ALT": alt})
        self.assertEqual(r["endpoints"]["e"]["code"], "UNALIGNED_ALTERNATIVE")
        alt = replace(alt, tracks=(replace(alt.tracks[0], metadata={**alt.tracks[0].metadata, "alignment": "reference_retained"}),))
        r = analyse_rna(c, (endpoint(),), {"REF": ref, "ALT": alt})
        self.assertEqual(r["status"], "SUCCESS")
        self.assertNotEqual(r["input_sequence_sha256"]["REF"], r["input_sequence_sha256"]["ALT"])

    def test_binned_and_ambiguous_tracks_explicitly_unavailable(self):
        c = context()
        ref = prediction(c, "REF", [1]*12)
        binned = replace(ref, tracks=(replace(ref.tracks[0], values=(1,)*6, bin_size=2),))
        r = analyse_rna(c, (endpoint(),), {"REF": binned})
        self.assertEqual(r["endpoints"]["e"]["code"], "PER_BASE_REQUIRED")
        r = analyse_rna(c, (endpoint(),), {"REF": replace(ref, tracks=ref.tracks*2)})
        self.assertEqual(r["endpoints"]["e"]["code"], "AMBIGUOUS_TRACK")

    def test_named_tracks_must_match_across_scenarios(self):
        c = context()
        ref, alt = prediction(c, "REF", [1]*12), prediction(c, "ALT", [2]*12)
        unnamed = replace(ref, tracks=(replace(ref.tracks[0], metadata={}),))
        result = analyse_rna(c, (endpoint(),), {"REF": unnamed})
        self.assertEqual(result["endpoints"]["e"]["code"], "TRACK_ID")
        different = replace(alt, tracks=(replace(alt.tracks[0], metadata={**alt.tracks[0].metadata, "name": "different-experiment"}),))
        with self.assertRaises(MolecularError) as caught:
            analyse_rna(c, (endpoint(),), {"REF": ref, "ALT": different})
        self.assertEqual(caught.exception.code, "MISMATCHED_TRACKS")

    def test_pas_annotation_is_required_not_inferred_from_transcript(self):
        c = context()
        e = endpoint("polyadenylation", "RNA_SEQ", "site_ratio", site_windows=((101,103),(109,111)))
        e = replace(e, site_annotation_source="", site_annotation_version="")
        with self.assertRaises(MolecularError) as caught:
            analyse_rna(c, (e,), {"REF": prediction(c, "REF", [1]*12)})
        self.assertEqual(caught.exception.code, "TEXT")

    def test_zero_pas_windows_and_log2_method(self):
        c = context()
        e = endpoint("polyadenylation", "RNA_SEQ", "site_ratio", "log2", site_windows=((101,103),(109,111)))
        result = self.score(c, e, [0]*12, [0]*12)
        self.assertEqual(result["raw_values_by_scenario"], {"REF": 1, "ALT": 1})
        self.assertEqual(result["values_by_scenario"], {"REF": 0, "ALT": 0})

    def test_identity_mismatch_and_mixed_evidence_refused(self):
        c = context()
        ref = prediction(c, "REF", [1]*12)
        for bad, code in ((replace(ref, settings_sha256="wrong"), "MISMATCHED_SETTINGS"),
                          (replace(ref, sequence_sha256="a"*64), "MISMATCHED_SEQUENCE"),
                          (replace(ref, scenario="ALT"), "SCENARIO"),
                          (replace(ref, tracks=(replace(ref.tracks[0], strand="-"),)), "STRAND")):
            with self.subTest(code=code), self.assertRaises(MolecularError) as caught:
                analyse_rna(c, (endpoint(),), {"REF": bad})
            self.assertEqual(caught.exception.code, code)
        with self.assertRaises(MolecularError) as caught:
            analyse_rna(c, (endpoint(),), {"REF": ref, "ALT": prediction(c, "ALT", [1]*12, evidence="REAL_MODEL_PREDICTION")})
        self.assertEqual(caught.exception.code, "MIXED_EVIDENCE")

    def test_duplicate_endpoint_and_empty_mask(self):
        c = context()
        with self.assertRaises(MolecularError) as caught:
            analyse_rna(c, (endpoint(), endpoint()), {"REF": prediction(c, "REF", [1]*12)})
        self.assertEqual(caught.exception.code, "ENDPOINTS")
        r = self.score(c, endpoint(start0=104, end0=108), [1]*12, [2]*12)
        self.assertEqual(r["code"], "EMPTY_MASK")

    def test_large_finite_log_and_overflow_refusal(self):
        c = context()
        r = self.score(c, endpoint(scale="log", pseudocount=1e308), [0]*12, [1]*12)
        self.assertTrue(math.isfinite(r["values_by_scenario"]["ALT"]))
        r = self.score(c, endpoint(aggregation="sum"), [1e308]*12, [1e308]*12)
        self.assertEqual(r["status"], "UNKNOWN")
        self.assertEqual(r["code"], "NUMERICAL_RANGE")

    def test_json_ready_provenance_and_no_biological_claim(self):
        c = context()
        result = analyse_rna(c, (endpoint(),), {"REF": prediction(c, "REF", [1]*12)})
        json.dumps(result, allow_nan=False)
        self.assertFalse(result["biological_conclusion_established"])
        self.assertEqual(result["identity"]["annotation_version"], "fixture-v1")
        self.assertEqual(result["evidence"], "MOCK_SYNTHETIC")


class MockProviderIntegrationTests(unittest.TestCase):
    def test_provider_four_scenarios_and_declared_interaction_inputs(self):
        c = context()
        provider = SyntheticProvider()
        sequences = {"REF": c.window.sequence, "A": "G"+c.window.sequence[1:],
                     "B": c.window.sequence[:1]+"T"+c.window.sequence[2:],
                     "AB": "GT"+c.window.sequence[2:]}
        predictions = {}
        for scenario, sequence in sequences.items():
            p = provider.predict_sequence(c, scenario, sequence)
            predictions[scenario] = replace(p, tracks=tuple(replace(t, metadata={**t.metadata, "alignment": "reference_retained"}) for t in p.tracks))
        endpoints = (endpoint(id="expression"), endpoint("splice_sites", "SPLICE_SITES", id="sites"),
                     endpoint("splice_usage", "SPLICE_SITE_USAGE", id="usage"))
        result = analyse_rna(c, endpoints, predictions)
        self.assertEqual(result["status"], "SUCCESS")
        self.assertEqual(result["evidence"], "MOCK_SYNTHETIC")
        for entry in result["endpoints"].values():
            self.assertEqual(set(entry["values_by_scenario"]), {"REF", "A", "B", "AB"})
            values = entry["values_by_scenario"]
            self.assertTrue(math.isfinite(values["AB"]-values["A"]-values["B"]+values["REF"]))
        self.assertFalse(result["biological_conclusion_established"])

    def test_provider_single_reference_native_track(self):
        c = context()
        provider = SyntheticProvider()
        prediction_ref = provider.predict_sequence(c, "REF", c.window.sequence)
        r = analyse_rna(c, (endpoint(),), {"REF": prediction_ref})
        self.assertEqual(r["status"], "SUCCESS")
        self.assertEqual(r["endpoints"]["e"]["values_by_scenario"]["REF"], 15/6)


if __name__ == "__main__":
    unittest.main()
