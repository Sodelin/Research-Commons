import LiteralSameBinTrace
import G2AncestralTraceSourceLaw

/-!
Contributor: Codex, delegated G3/source bridge, 2026-10-07.
UNCHECKED separate source-law derivative; no compiler has run on this file.
The actual original-clock event, SAME random-cover record and original raw
completion endpoint law derive the joint tail row. No desired row law is
supplied as a premise. The original ten-helper author source is unchanged.
-/

namespace CloudG3.ActualTailBinRow

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.CompleteDecoration
open GProgram.G2.FiniteAncestralTrace GProgram.G2.AncestralTraceSourceLaw
open GProgram.G2.ClockBoundaryNull
open UnifiedLean.G6.BinHistory UnifiedLean.G6.BinFold
open CloudG3.LiteralSameBinTrace
open scoped Classical NNReal

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

set_option backward.isDefEq.respectTransparency false in
/-- Old tags and destination Codes are finite. Only the actual age bin uses
a real measurable coordinate; flags and inactive padding are unchanged. -/
theorem fold_tags_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (hbin : Measurable bin) (n : ℕ) (offset : ℝ) :
    Measurable (fun z : Code N sample ×
        ((Copy → Copy → Tag) × ClockTrace N sample n) =>
      foldTags N bin n z.1 offset z.2.1 z.2.2) := by
  induction n with
  | zero => exact measurable_snd.fst
  | succ n ih =>
      have hh : Measurable (fun z : Code N sample ×
          ((Copy → Copy → Tag) × ClockTrace N sample (n + 1)) => z.2.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd.snd
      have ht : Measurable (fun z : Code N sample ×
          ((Copy → Copy → Tag) × ClockTrace N sample (n + 1)) =>
          fun i : Fin n => z.2.2 i.succ) := by
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i.succ).comp measurable_snd.snd
      have hu0 : Measurable (fun z : Code N sample ×
          (Code N sample × (Tag × (Copy → Copy → Tag))) =>
          tagUpdate N z.1 z.2.1 z.2.2.1 z.2.2.2) :=
        measurable_of_countable _
      have hu : Measurable (fun z : Code N sample ×
          ((Copy → Copy → Tag) × ClockTrace N sample (n + 1)) =>
          tagUpdate N z.1 (z.2.2 0).2.2
            (bin (offset + (z.2.2 0).2.1)) z.2.1) :=
        hu0.comp (measurable_fst.prodMk (hh.snd.snd.prodMk
          ((hbin.comp (measurable_const.add hh.snd.fst)).prodMk measurable_snd.fst)))
      have ha := ih.comp (hh.snd.snd.prodMk (hu.prodMk ht))
      have hi := ih.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk ht))
      exact Measurable.ite (measurableSet_eq_fun hh.fst measurable_const) ha hi

theorem raw_tail_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) :
    Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      traceEndpoint N (Fintype.card Copy) s z.2) :=
  (trace_end_joint_measurable N (Fintype.card Copy)).comp
    (measurable_const.prodMk measurable_snd)

/-- One original positive-coordinate event works for EVERY horizon and budget.
The horizon is free after fixing the vector, including its SAME clockCover. -/
theorem actual_tail_bin_fold_all_horizons (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (bin : ℝ → Tag) (tag : Tag) (cut offset : ℝ) (hoff : cut ≤ offset)
    (htail : ∀ a : ℝ, cut < a → bin a = tag) :
    ∀ᵐ c ∂currentPairClockMeasure N r s,
      ∀ (n : ℕ) (H : ℝ) (B : Copy → Copy → Tag),
        foldTags N bin n s offset B (literalMarkedTrace N n H s c).2 =
          tagUpdate N s (traceEndpoint N n s (literalMarkedTrace N n H s c).2) tag B := by
  filter_upwards [actual_clock_strictly_positive N r s] with c hc
  intro n H B
  have hb : ∀ i : Fin n, ((literalMarkedTrace N n H s c).2 i).1 = true →
      bin (offset + ((literalMarkedTrace N n H s c).2 i).2.1) = tag := by
    intro i hi
    obtain ⟨p, hp⟩ := literal_active_time_is_coordinate N n H s c i hi
    rw [hp]
    apply htail
    exact lt_of_le_of_lt hoff (lt_add_of_pos_right offset (hc p))
  exact (bin_constant_active_fold N bin tag n s offset B _ hb).trans
    (literal_same_bin_endpoint_fold N tag n s H offset c B)

/-- The proved original-clock identity is pushed to the ACTUAL complete record
law, simultaneously for every finite old matrix and without conditioning. -/
theorem actual_complete_tail_bin_fold (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (bin : ℝ → Tag) (hbin : Measurable bin) (tag : Tag) (cut offset : ℝ)
    (hoff : cut ≤ offset) (htail : ∀ a : ℝ, cut < a → bin a = tag) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      ∀ B : Copy → Copy → Tag,
        foldTags N bin (Fintype.card Copy) s offset B z.2 =
          tagUpdate N s (traceEndpoint N (Fintype.card Copy) s z.2) tag B := by
  have hp : Measurable (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
      ∀ B : Copy → Copy → Tag,
        foldTags N bin (Fintype.card Copy) s offset B z.2 =
          tagUpdate N s (traceEndpoint N (Fintype.card Copy) s z.2) tag B) := by
    apply Measurable.forall
    intro B
    have hprep : Measurable
        (fun z : Bool × ClockTrace N sample (Fintype.card Copy) =>
          (s, (B, z.2))) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_snd)
    have hf := (fold_tags_joint_measurable N bin hbin (Fintype.card Copy) offset).comp
      hprep
    have hu : Measurable (fun e : Code N sample => tagUpdate N s e tag B) :=
      measurable_of_countable _
    exact (measurableSet_eq_fun hf (hu.comp (raw_tail_endpoint_measurable N s))).mem
  rw [completeAncestralTraceLaw]
  apply (ae_map_iff (complete_ancestral_trace_measurable N s).aemeasurable hp.setOf).mpr
  filter_upwards [actual_tail_bin_fold_all_horizons N r s bin tag cut offset hoff htail] with c hc
  intro B
  simpa only [completeAncestralTrace] using hc (Fintype.card Copy) (clockCover N s c : ℝ) B

/-- A source-connected joint kernel row. The raw actual completion endpoint
law and the actual tail fold derive it; a desired row is not an input. -/
theorem actual_tail_joint_source_law (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) (bin : ℝ → Tag) (hbin : Measurable bin)
    (tag : Tag) (cut offset : ℝ) (hoff : cut ≤ offset)
    (htail : ∀ a : ℝ, cut < a → bin a = tag) (B : Copy → Copy → Tag) :
    (completeAncestralTraceLaw N r s).map
        (fun z => (traceEndpoint N (Fintype.card Copy) s z.2,
          foldTags N bin (Fintype.card Copy) s offset B z.2)) =
      (completionKernel N r s).toMeasure.map
        (fun e => (e, tagUpdate N s e tag B)) := by
  have hu : Measurable (fun e : Code N sample => (e, tagUpdate N s e tag B)) :=
    measurable_of_countable _
  calc
    _ = (completeAncestralTraceLaw N r s).map
        ((fun e => (e, tagUpdate N s e tag B)) ∘
          (fun z => traceEndpoint N (Fintype.card Copy) s z.2)) := by
      apply Measure.map_congr
      filter_upwards [actual_complete_tail_bin_fold N r s bin hbin tag cut offset hoff htail] with z hz
      exact Prod.ext rfl (hz B)
    _ = ((completeAncestralTraceLaw N r s).map
        (fun z => traceEndpoint N (Fintype.card Copy) s z.2)).map
        (fun e => (e, tagUpdate N s e tag B)) :=
      (Measure.map_map hu (raw_tail_endpoint_measurable N s)).symm
    _ = _ := by rw [complete_ancestral_state_source_law N r s hs]

#print axioms fold_tags_joint_measurable
#print axioms raw_tail_endpoint_measurable
#print axioms actual_tail_bin_fold_all_horizons
#print axioms actual_complete_tail_bin_fold
#print axioms actual_tail_joint_source_law

end CloudG3.ActualTailBinRow
