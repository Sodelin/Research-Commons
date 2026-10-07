import ActualCutTagRefinement
import ActualTailBinRow
import G2SameClockPastFutureLaw

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate renewal-law derivative. Original deterministic cut and
principal calendar sources remain unchanged. Actual full-past terminal-fibre
renewal is consumed as a proved source result, not a desired output premise.
No compiler ran in this lane. Literal whole-calendar attachment is separate.
-/

namespace CloudG3.ActualCutJointLaw
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralCutResidual
open GProgram.G2.FiniteAncestralTrace GProgram.G2.HistoryResidualAttachment
open GProgram.G2.SameClockPastFutureLaw
open UnifiedLean.G6.BinFold
open CloudG3.ActualCutTagRefinement CloudG3.ActualTailBinRow
open scoped Classical NNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.HistoryResidualAttachment.current_clock_probability

abbrev TaggedEndpoint (N : RootedBinary V E X) (sample : Copy → X) :=
  Code N sample × (Copy → Copy → Tag)

noncomputable def tailTraceReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (s : Code N sample) (offset : ℝ) (B : Copy → Copy → Tag)
    (z : Bool × ClockTrace N sample (Fintype.card Copy)) : TaggedEndpoint N sample :=
  (traceEndpoint N (Fintype.card Copy) s z.2,
    foldTags N bin (Fintype.card Copy) s offset B z.2)

theorem tail_trace_readout_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (hbin : Measurable bin) (s : Code N sample) (offset : ℝ)
    (B : Copy → Copy → Tag) : Measurable (tailTraceReadout N bin s offset B) :=
  (raw_tail_endpoint_measurable N s).prodMk
    ((fold_tags_joint_measurable N bin hbin (Fintype.card Copy) offset).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_snd)))

noncomputable def cutCompleteReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (s : Code N sample) (offset : ℝ) :
    (Copy → Copy → Tag) × CutResidual N sample → TaggedEndpoint N sample :=
  fun z => match z.2 with
    | .inl _ => (s, z.1)
    | .inr q => tailTraceReadout N bin q.1 offset z.1 (completeAncestralTrace N q.1 q.2)

/-- The finite carried matrix can be fixed before using each original
measurable Sigma clock fibre. The failure value has no new leaf or Code. -/
theorem cut_complete_readout_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (offset : ℝ) :
    Measurable (cutCompleteReadout N bin s offset) := by
  apply measurable_from_prod_countable_right
  intro B
  have hm : Measurable (fun q : (Σ d : Code N sample, Choice N d → ℝ) =>
      tailTraceReadout N bin q.1 offset B (completeAncestralTrace N q.1 q.2)) := by
    intro A hA
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro d
    exact ((tail_trace_readout_measurable N bin hbin d offset B).comp
      (complete_ancestral_trace_measurable N d)) hA
  exact measurable_const.sumElim hm

noncomputable def prefixTailReadout (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (s d : Code N sample) (offset t : ℝ) (B : Copy → Copy → Tag)
    (z : (Bool × ClockTrace N sample (Fintype.card Copy)) ×
      (Bool × ClockTrace N sample (Fintype.card Copy))) : TaggedEndpoint N sample :=
  tailTraceReadout N bin d (offset + t)
    (foldTags N bin (Fintype.card Copy) s offset B z.1.2) z.2

theorem prefix_tail_readout_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (bin : ℝ → Tag) (hbin : Measurable bin)
    (s d : Code N sample) (offset t : ℝ) (B : Copy → Copy → Tag) :
    Measurable (prefixTailReadout N bin s d offset t B) := by
  have hB : Measurable (fun z :
      (Bool × ClockTrace N sample (Fintype.card Copy)) ×
        (Bool × ClockTrace N sample (Fintype.card Copy)) =>
      foldTags N bin (Fintype.card Copy) s offset B z.1.2) :=
    (fold_tags_joint_measurable N bin hbin (Fintype.card Copy) offset).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_fst.snd))
  exact ((raw_tail_endpoint_measurable N d).comp measurable_snd).prodMk
    ((fold_tags_joint_measurable N bin hbin (Fintype.card Copy) (offset + t)).comp
      (measurable_const.prodMk (hB.prodMk measurable_snd.snd)))

/-- Eq(10): the SAME complete endpoint/tag law is derived from the actual
unnormalized marked-prefix fibres and their actual complete residual clocks.
Ancestral support, tail-bin constancy and desired row laws are not premises. -/
theorem complete_cut_fibre_joint_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (bin : ℝ → Tag) (hbin : Measurable bin) (offset : ℝ) (t : ℝ≥0)
    (B : Copy → Copy → Tag) :
    (completeAncestralTraceLaw N r s).map (tailTraceReadout N bin s offset B) =
      ∑ d : Code N sample,
        ((((actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
          {h | decodedEndpoint N (Fintype.card Copy) s h = some d}).prod
          (completeAncestralTraceLaw N r d)).map
            (prefixTailReadout N bin s d offset (t : ℝ) B)) := by
  let F : (Bool × ClockTrace N sample (Fintype.card Copy)) × CutResidual N sample →
      TaggedEndpoint N sample := fun z => cutCompleteReadout N bin s (offset + (t : ℝ))
        (foldTags N bin (Fintype.card Copy) s offset B z.1.2, z.2)
  have hF : Measurable F := (cut_complete_readout_measurable N bin hbin s _).comp
    (((fold_tags_joint_measurable N bin hbin (Fintype.card Copy) offset).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_fst.snd))).prodMk
        measurable_snd)
  have hJ := (marked_trace_measurable N (Fintype.card Copy) s (t : ℝ)).prodMk
    (literal_cut_measurable N (Fintype.card Copy) s (t : ℝ))
  calc
    _ = (actualCutJointLaw N r (Fintype.card Copy) s (t : ℝ)).map F := by
      rw [completeAncestralTraceLaw,
        Measure.map_map (tail_trace_readout_measurable N bin hbin s offset B)
          (complete_ancestral_trace_measurable N s),
        actualCutJointLaw, Measure.map_map hF hJ]
      apply Measure.map_congr
      filter_upwards [actual_current_clock_regular_ae N r s] with c hc
      obtain ⟨d, k, hcut⟩ := actual_cut_residual_success N (Fintype.card Copy)
        (t : ℝ) s c hc (Finset.card_le_univ s.val.live)
      dsimp only [Function.comp_def, F]
      rw [hcut]
      exact same_clock_complete_joint_readout_cut_refinement N bin (t : ℝ) offset
        s d c k B hc t.coe_nonneg hcut
    _ = _ := by
      rw [actual_full_past_terminal_fibres N r (Fintype.card Copy) s t
        (Finset.card_le_univ s.val.live), Measure.map_finset_sum' hF.aemeasurable]
      apply Finset.sum_congr rfl
      intro d _
      let P := (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {h | decodedEndpoint N (Fintype.card Copy) s h = some d}
      letI := actual_marked_trace_probability N r (Fintype.card Copy) s t
      have he : Measurable (fun z : (Bool × ClockTrace N sample (Fintype.card Copy)) ×
          (Choice N d → ℝ) => (z.1, encodeResidual N d z.2)) :=
        measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd)
      have hg := prefix_tail_readout_measurable N bin hbin s d offset (t : ℝ) B
      have hprod : P.prod ((currentPairClockMeasure N r d).map
          (completeAncestralTrace N d)) =
          (P.prod (currentPairClockMeasure N r d)).map
            (Prod.map id (completeAncestralTrace N d)) := by
        simpa only [Measure.map_id] using
          Measure.map_prod_map P (currentPairClockMeasure N r d) measurable_id
            (complete_ancestral_trace_measurable N d)
      rw [Measure.map_map hF he, completeAncestralTraceLaw, hprod,
        Measure.map_map hg
          (measurable_id.prodMap (complete_ancestral_trace_measurable N d))]
      rfl

/-- At full cap the Option endpoint fibre and raw endpoint fibre agree as
unnormalized measures. A success flag is proved AE, never conditioned on. -/
theorem decoded_raw_endpoint_restrict (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s d : Code N sample) (t : ℝ≥0) :
    (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {h | decodedEndpoint N (Fintype.card Copy) s h = some d} =
      (actualMarkedTraceLaw N r (Fintype.card Copy) s (t : ℝ)).restrict
        {h | traceEndpoint N (Fintype.card Copy) s h.2 = d} := by
  apply Measure.restrict_congr_set
  filter_upwards [actual_marked_trace_success_ae N r (Fintype.card Copy) s t
    (Finset.card_le_univ s.val.live)] with h hh
  simp only [Set.mem_setOf_eq, decodedEndpoint, hh, if_true, Option.some.injEq]

#print axioms tail_trace_readout_measurable
#print axioms cut_complete_readout_measurable
#print axioms prefix_tail_readout_measurable
#print axioms complete_cut_fibre_joint_source_law
#print axioms decoded_raw_endpoint_restrict

end CloudG3.ActualCutJointLaw
