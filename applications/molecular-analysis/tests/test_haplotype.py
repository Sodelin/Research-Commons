"""Synthetic offline haplotype tests, including the actual native stdin bridge."""
from dataclasses import replace
import json
import os
from pathlib import Path
import unittest

from molecular_apps.contracts import (Context, EndpointSpec, HaplotypeRequest,
    MolecularError, Phase, ReferenceWindow, TranscriptAnnotation, Variant,
    sequence_sha256)
from molecular_apps.haplotype import (ALIGNMENT_POLICY, _reference_align,
    analyse_haplotype, assemble_haplotypes)
from molecular_apps.providers import SyntheticProvider


def request(*, sequence="CCCCCCCC", phase=None, variants=None, endpoint=None, strand="+"):
    guard = "CCCC"
    window = ReferenceWindow("hg38", "chr1", 0, sequence, guard,
        "synthetic offline test reference", sequence_sha256(sequence+guard))
    transcript = TranscriptAnnotation("SYNTHETIC_GENE", "SYNTHETIC_TX", 0,
        len(sequence), strand, "synthetic test annotation", "test-v1", ((0,len(sequence)),))
    context = Context(window, transcript, "UBERON:0002107", "synthetic-v1",
        ("RNA_SEQ",), "forward_reference_fixed_left_v1")
    variants = variants or (Variant("A","chr1",3,"C","A"), Variant("B","chr1",4,"C","G"))
    endpoint = endpoint or EndpointSpec("expression","expression","RNA_SEQ","sum","linear",0,len(sequence))
    return HaplotypeRequest(context,tuple(variants),phase or Phase("hypothetical","synthetic scenario"),(endpoint,))


class CountingProvider(SyntheticProvider):
    def __init__(self): self.prediction_calls=[]
    def predict_sequence(self,context,scenario,sequence):
        self.prediction_calls.append((scenario,sequence))
        return super().predict_sequence(context,scenario,sequence)


class UnitSignalProvider(CountingProvider):
    def predict_sequence(self,context,scenario,sequence):
        result=super().predict_sequence(context,scenario,sequence)
        return replace(result,tracks=tuple(replace(t,values=(1.0,)*len(sequence)) for t in result.tracks))


class MutatingProvider(CountingProvider):
    def __init__(self,mutation): super().__init__();self.mutation=mutation
    def predict_sequence(self,context,scenario,sequence):
        result=super().predict_sequence(context,scenario,sequence)
        return self.mutation(result,scenario)


class HaplotypeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        candidate=os.environ.get("MOLECULAR_HAPLOTYPE_CORE")
        if not candidate or not Path(candidate).is_file():
            raise RuntimeError("set MOLECULAR_HAPLOTYPE_CORE to the already-built native core for these integration tests")
        cls.binary=Path(candidate)

    def run_analysis(self,r=None,p=None):
        return analyse_haplotype(r or request(),p or SyntheticProvider(),core_binary=self.binary)

    def test_known_mock_interaction_and_compact_provenance(self):
        r=request();result=self.run_analysis(r)
        self.assertEqual(result["status"],"SUCCESS",result)
        self.assertTrue(result["successful_computation"]);self.assertFalse(result["biological_conclusion_established"])
        self.assertEqual(result["evidence"],"MOCK_SYNTHETIC")
        row=result["interactions"][0]
        self.assertEqual(row["interaction"],2.0)
        self.assertEqual(row["interaction"],row["values"]["AB"]-row["values"]["A"]-row["values"]["B"]+row["values"]["REF"])
        self.assertEqual(set(result["scenarios"]),{"REF","A","B","AB"})
        self.assertNotIn("sequence",result["context"]["window"])
        self.assertNotIn("guard_sequence",result["context"]["window"])
        self.assertEqual(result["context"]["window"]["end0"],8)
        self.assertEqual(result["context"]["transcript"]["transcript_id"],"SYNTHETIC_TX")
        self.assertEqual(result["endpoint_alignment"],ALIGNMENT_POLICY)
        self.assertNotIn("sequence",result["scenarios"]["AB"])
        json.dumps(result,allow_nan=False)

    def test_additive_fixture_has_zero_interaction(self):
        result=self.run_analysis(p=UnitSignalProvider())
        self.assertEqual(result["interactions"][0]["interaction"],0.0)

    def test_declared_log_scale_is_preserved(self):
        e=replace(request().endpoints[0],scale="log",pseudocount=0.5)
        result=self.run_analysis(request(endpoint=e))
        self.assertEqual(result["status"],"SUCCESS",result)
        self.assertEqual(result["interactions"][0]["scale"],"log")
        self.assertEqual(result["interactions"][0]["endpoint"]["pseudocount"],0.5)

    def test_unknown_phase_computes_counterfactual_without_becoming_cis(self):
        result=self.run_analysis(request(phase=Phase("unknown","")))
        self.assertEqual(result["status"],"UNKNOWN")
        self.assertTrue(result["successful_computation"])
        self.assertTrue(result["scenarios"]["AB"]["counterfactual"])
        self.assertEqual(result["phase"]["kind"],"unknown")
        self.assertIsNone(result["diploid_aggregation"])

    def test_cis_and_trans_require_explicit_evidence(self):
        for kind in ("cis","trans"):
            p=CountingProvider();result=self.run_analysis(request(phase=Phase(kind,"")),p)
            self.assertEqual(result["status"],"INVALID_INPUT")
            self.assertEqual(p.prediction_calls,[])
        cis=self.run_analysis(request(phase=Phase("cis","synthetic phased-block evidence")))
        trans=self.run_analysis(request(phase=Phase("trans","synthetic trans-block evidence")))
        self.assertFalse(cis["scenarios"]["AB"]["counterfactual"])
        self.assertTrue(trans["scenarios"]["AB"]["counterfactual"])

    def test_reference_and_guard_hash_are_checked_before_provider(self):
        r=request();bad=replace(r.context.window,guard_sequence="TTTT")
        p=CountingProvider();result=self.run_analysis(replace(r,context=replace(r.context,window=bad)),p)
        self.assertEqual(result["code"],"REFERENCE_HASH");self.assertEqual(p.prediction_calls,[])

    def test_native_ref_mismatch_overlap_and_duplicate_ids_before_prediction(self):
        bads=[(Variant("A","chr1",3,"A","T"),Variant("B","chr1",4,"C","G")),
              (Variant("A","chr1",3,"CC","TT"),Variant("B","chr1",4,"C","G")),
              (Variant("A","chr1",3,"C","A"),Variant("A","chr1",4,"C","G"))]
        for vs,code in zip(bads,("REFERENCE_MISMATCH","OVERLAPPING_VARIANTS","VARIANT_ID")):
            p=CountingProvider();result=self.run_analysis(request(variants=vs),p)
            self.assertEqual(result["code"],code,result);self.assertEqual(p.prediction_calls,[])

    def test_crop_of_declared_roi_refused_before_provider(self):
        r=request(variants=(Variant("A","chr1",2,"C","CAA"),Variant("B","chr1",4,"C","G")))
        p=CountingProvider();result=self.run_analysis(r,p)
        self.assertEqual(result["code"],"ROI_CROPPED");self.assertEqual(p.prediction_calls,[])

    def test_complex_delins_refused(self):
        r=request(variants=(Variant("A","chr1",2,"CC","CAT"),Variant("B","chr1",5,"C","G")))
        self.assertEqual(self.run_analysis(r)["status"],"UNSUPPORTED")

    def test_deletion_zero_fill_uses_original_mean_denominator(self):
        e=EndpointSpec("mean","expression","RNA_SEQ","mean","linear",0,4)
        r=request(endpoint=e,variants=(Variant("A","chr1",2,"CC","C"),Variant("B","chr1",5,"C","A")))
        result=self.run_analysis(r,UnitSignalProvider());self.assertEqual(result["status"],"SUCCESS",result)
        values=result["interactions"][0]["values"]
        self.assertEqual(values["REF"],1.0);self.assertEqual(values["A"],0.75);self.assertEqual(values["AB"],0.75)
        self.assertEqual(result["scenarios"]["A"]["deleted_reference_ranges"],[{"start0":2,"end0":3}])

    def test_inserted_bases_excluded_from_reference_endpoint(self):
        e=EndpointSpec("mean","expression","RNA_SEQ","mean","linear",0,4)
        r=request(endpoint=e,variants=(Variant("A","chr1",2,"C","CGG"),Variant("B","chr1",5,"C","T")))
        result=self.run_analysis(r,UnitSignalProvider());self.assertEqual(result["status"],"SUCCESS",result)
        self.assertEqual(set(result["interactions"][0]["values"].values()),{1.0})
        self.assertTrue(any(m["reference_start0"] is None for m in result["scenarios"]["AB"]["coordinate_map"]))

    def test_per_base_alignment_tracks_deletion_and_preserves_alt_digest(self):
        e=EndpointSpec("mean","expression","RNA_SEQ","mean","linear",0,4)
        r=request(endpoint=e,variants=(Variant("A","chr1",2,"CC","C"),Variant("B","chr1",5,"C","A")))
        native=assemble_haplotypes(r,core_binary=self.binary)
        details=native["scenarios"]["A"];p=UnitSignalProvider().predict_sequence(r.context,"A",details["sequence"])
        aligned=_reference_align(r.context,p,details)
        self.assertEqual(aligned.sequence_sha256,sequence_sha256(details["sequence"]))
        self.assertEqual(aligned.tracks[0].values[:4],(1.0,1.0,0.0,1.0))
        self.assertEqual(aligned.tracks[0].metadata["alignment"],"reference_retained")

    def test_coarse_indel_predictions_are_unsupported(self):
        e=EndpointSpec("mean","expression","RNA_SEQ","mean","linear",0,4)
        r=request(endpoint=e,variants=(Variant("A","chr1",2,"C","CGG"),Variant("B","chr1",5,"C","T")))
        p=MutatingProvider(lambda pred,s:replace(pred,tracks=tuple(replace(t,values=t.values[::2],bin_size=2) for t in pred.tracks)))
        result=self.run_analysis(r,p);self.assertEqual(result["code"],"INDEL_RESOLUTION",result)

    def test_provider_identity_mismatches_refused(self):
        cases=[(lambda p,s:replace(p,scenario="other"),"MISMATCHED_SCENARIO"),
               (lambda p,s:replace(p,sequence_sha256="wrong"),"MISMATCHED_SEQUENCE"),
               (lambda p,s:replace(p,settings_sha256="wrong"),"MISMATCHED_SETTINGS"),
               (lambda p,s:replace(p,tracks=tuple(replace(t,strand="-") for t in p.tracks)),"STRAND")]
        for mutation,code in cases:
            result=self.run_analysis(p=MutatingProvider(mutation));self.assertEqual(result["code"],code,result)

    def test_track_and_evidence_cannot_change_between_conditions(self):
        def track(pred,s):
            return replace(pred,tracks=tuple(replace(t,metadata={**t.metadata,"name":"different"}) for t in pred.tracks)) if s=="B" else pred
        self.assertEqual(self.run_analysis(p=MutatingProvider(track))["code"],"MISMATCHED_TRACKS")
        p=MutatingProvider(lambda pred,s:replace(pred,evidence="REAL_MODEL_PREDICTION") if s=="B" else pred)
        self.assertEqual(self.run_analysis(p=p)["code"],"EVIDENCE")

    def test_nonfinite_track_missing_track_and_unknown_coordinate_space(self):
        changes=[(lambda p,s:replace(p,tracks=()),"TRACK"),
                 (lambda p,s:replace(p,tracks=tuple(replace(t,values=(float("nan"),)*8) for t in p.tracks)),"TRACK_VALUES"),
                 (lambda p,s:replace(p,tracks=tuple(replace(t,metadata={**t.metadata,"coordinate_space":"unknown"}) for t in p.tracks)),"COORDINATE_SPACE")]
        for change,code in changes:
            result=self.run_analysis(p=MutatingProvider(change));self.assertEqual(result["code"],code,result)

    def test_percentile_avi_scale_is_not_addable(self):
        r=request(endpoint=replace(request().endpoints[0],scale="AVI_quantile"));p=CountingProvider()
        result=self.run_analysis(r,p);self.assertEqual(result["code"],"SCALE");self.assertEqual(p.prediction_calls,[])

    def test_minus_strand_and_supported_assembly_alias(self):
        r=request(strand="-");r=replace(r,context=replace(r.context,window=replace(r.context.window,assembly="GRCh38")))
        result=self.run_analysis(r);self.assertEqual(result["status"],"SUCCESS",result)
        self.assertEqual(result["context"]["transcript"]["strand"],"-")
        self.assertEqual(result["context"]["window"]["assembly"],"GRCh38")

    def test_provider_failure_is_structured_without_raw_exception(self):
        class Broken(SyntheticProvider):
            def predict_sequence(self,*args):raise RuntimeError("sensitive exception detail")
        result=self.run_analysis(p=Broken());self.assertEqual(result["status"],"EXECUTION_FAILURE")
        self.assertNotIn("sensitive",json.dumps(result))

    def test_missing_native_binary_is_explicit(self):
        result=analyse_haplotype(request(),SyntheticProvider(),core_binary="/definitely/not/a/native/binary")
        self.assertEqual(result["code"],"CORE_UNAVAILABLE");self.assertEqual(result["status"],"UNSUPPORTED")


if __name__ == "__main__": unittest.main()
