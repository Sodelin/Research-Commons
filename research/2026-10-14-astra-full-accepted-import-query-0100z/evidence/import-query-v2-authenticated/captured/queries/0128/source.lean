import G2HistoryResidualAttachment

/-!
The actual retained clock vector at a deterministic cut is an unnormalized
source-endpoint mixture of the original destination clock products.
Contributor: dot (OpenAI), 6 October 2026. This is derived by forgetting the
past from the already proved joint attachment, not assumed as a reset law.
-/
namespace GProgram.G2.CutResidualSourceMixture
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonKernel
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralEpochLaw
open GProgram.G2.LiteralCutResidual GProgram.G2.HistoryResidualAttachment
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

lemma actual_history_terminal_fibre_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ≥0) :
    actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)
      {h | decodedEndpoint N (Fintype.card Copy) s h = some d} =
      sourceTimeKernel N r t s d := by
  have h := actual_endpoint_mass_eq_source_kernel N r (Fintype.card Copy) s d t
    (Finset.card_le_univ s.val.live)
  rw [actualEndpointLaw,Measure.map_apply (decoded_endpoint_measurable N _ s)
    (show MeasurableSet ({some d} : Set (Option (Code N sample))) by trivial)] at h
  exact h

theorem actual_cut_residual_source_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    (currentPairClockMeasure N r s).map (literalCutResidual N (Fintype.card Copy) t s) =
      ∑ d : Code N sample, sourceTimeKernel N r t s d •
        ((currentPairClockMeasure N r d).map (encodeResidual N d)) := by
  letI := actual_marked_trace_probability N r (Fintype.card Copy) s t
  have h := congrArg (fun μ : Measure ((Bool × ClockTrace N sample (Fintype.card Copy)) ×
      CutResidual N sample) => μ.map Prod.snd)
    (actual_full_past_terminal_fibres N r (Fintype.card Copy) s t (Finset.card_le_univ s.val.live))
  rw [actualCutJointLaw,Measure.map_map measurable_snd
    ((marked_trace_measurable N _ s t).prodMk (literal_cut_measurable N _ s t)),
    Measure.map_finset_sum' measurable_snd.aemeasurable] at h
  have he (d : Code N sample) :
      (((((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {z | decodedEndpoint N (Fintype.card Copy) s z = some d}).prod
          (currentPairClockMeasure N r d)).map
            (fun z => (z.1,encodeResidual N d z.2))).map Prod.snd) =
        sourceTimeKernel N r t s d •
          ((currentPairClockMeasure N r d).map (encodeResidual N d)) := by
    letI := GProgram.G2.HistoryResidualAttachment.current_clock_probability N r d
    have hm : Measurable (fun z : (Bool × ClockTrace N sample (Fintype.card Copy)) ×
        (Choice N d → ℝ) => (z.1,encodeResidual N d z.2)) :=
      measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd)
    rw [Measure.map_map measurable_snd hm]
    change ((((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
      {z | decodedEndpoint N (Fintype.card Copy) s z = some d}).prod
        (currentPairClockMeasure N r d)).map ((encodeResidual N d) ∘ Prod.snd)) = _
    rw [← Measure.map_map (encode_residual_measurable N d) measurable_snd,
      Measure.map_snd_prod,Measure.map_smul,Measure.restrict_apply MeasurableSet.univ,
      univ_inter,actual_history_terminal_fibre_mass]
  simp_rw [he] at h
  exact h

/-- Every measurable retained-clock readout has the derived source mixture.
The following finite-history application supplies an actual suffix reader. -/
theorem actual_cut_readout_source_law {A : Type*} [MeasurableSpace A]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0)
    (F : CutResidual N sample → A) (hF : Measurable F) :
    (currentPairClockMeasure N r s).map (fun c => F (literalCutResidual N (Fintype.card Copy) t s c)) =
      ∑ d : Code N sample, sourceTimeKernel N r t s d •
        ((currentPairClockMeasure N r d).map (fun c => F (encodeResidual N d c))) := by
  change (currentPairClockMeasure N r s).map
    (F ∘ literalCutResidual N (Fintype.card Copy) t s) = _
  rw [← Measure.map_map hF (literal_cut_measurable N (Fintype.card Copy) s t),actual_cut_residual_source_law,
    Measure.map_finset_sum' hF.aemeasurable]
  apply Finset.sum_congr rfl
  intro d _
  rw [Measure.map_smul,Measure.map_map hF (encode_residual_measurable N d)]
  rfl

#print axioms actual_history_terminal_fibre_mass
#print axioms actual_cut_residual_source_law
#print axioms actual_cut_readout_source_law
end GProgram.G2.CutResidualSourceMixture
