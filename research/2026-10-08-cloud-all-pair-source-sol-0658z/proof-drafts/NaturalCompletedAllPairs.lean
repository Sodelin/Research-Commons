import NaturalPanelPhysicalAges
import UnifiedLean.Source.SourceCompletedUnrankedTree
import UnifiedLean.Source.SourceNaturalCompletedLimit
import G2AncestralTraceSourceLaw
import Mathlib.Data.Fintype.Card
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.MeasurableSpace.Basic

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
Authored SOURCE/HAND candidate. All new bodies compiler UNCHECKED/outside179.
Actual initialized full calendar derives root support. Original completion
absorption + SAME clock-cover tail derive one full-Copy tree, then actual
pairAge bins for ALL selected distinct pairs. No desired one-tree, old matrix,
independence or law/decoder equality is an admission field. Hidden IDs/register
are internal proof coordinates, never part of the observable carrier.
-/
namespace CloudG6.NaturalCompletedAllPairs

open MeasureTheory ProbabilityTheory Filter Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.FiniteAncestralTrace
open GProgram.G2.AncestralTraceSourceLaw GProgram.G2.ActualCalendarTrace
open GProgram.G2.CompleteCalendarAttachment GProgram.G2.CompleteDecoration
open GProgram.G2.FaithfulPairAgeDecoration
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext CloudG3.CompleteCalendarBinReadout
open CloudG6.NaturalCalendarPastAdmission CloudG6.NaturalPastCompleteObservation
open CloudG6.SourceIndependentForestAlphabet CloudG6.ActualFiniteObservableRecord
open CloudG6.ActualPanelForestReadout CloudG6.NaturalPanelPhysicalAges
open CloudG6.ActualSourceCorruptionClasses CloudG6.ActualObservationCorruption
open scoped Classical

universe u v w x y
variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

theorem completion_kernel_terminal_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    {d : Code N sample} (hd : d ∈ (completionKernel N r s).support) :
    AncestralRoot N d ∧ liveCard d ≤ 1 := by
  exact ancestral_completion_terminal_support N r (Fintype.card Copy) s hs
    (Finset.card_le_univ s.val.live) hd

/-- No conditioning or replacement tail law: the actual random-cover trace's
RAW endpoint has the actual completion law on the proved full-success event. -/
theorem actual_ancestral_raw_terminal_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    ∀ᵐ z ∂completeAncestralTraceLaw N r s,
      AncestralRoot N (traceEndpoint N (Fintype.card Copy) s z.2) ∧
        liveCard (traceEndpoint N (Fintype.card Copy) s z.2) ≤ 1 := by
  have hp : ∀ᵐ d ∂(completionKernel N r s).toMeasure, AncestralRoot N d ∧ liveCard d ≤ 1 := by
    apply ae_iff_of_countable.mpr
    intro d hd
    have hd' : d ∈ (completionKernel N r s).support := by
      apply (PMF.mem_support_iff _ _).mpr
      rwa [PMF.toMeasure_apply_singleton _ d (by trivial)] at hd
    exact completion_kernel_terminal_support N r s hs hd'
  rw [← complete_ancestral_state_source_law N r s hs] at hp
  exact ae_of_ae_map
    ((trace_end_joint_measurable N (Fintype.card Copy)).comp
      (measurable_const.prodMk measurable_snd)).aemeasurable hp

/-- Source physical clock-cover semantics gives pathwise eventual stability;
the regular-clock premise is derived almost surely by the original provider.
No externally supplied terminal tree or finite horizon bound is a field. -/
theorem ancestral_clock_cover_one_tree [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (c : Choice N s → ℝ)
    (hs : AncestralRoot N s) (hc : ClockRegular c) :
    ∃ q : UnrankedTree Copy, treeWellLabelled q ∧ treeLeaves q = Finset.univ ∧
      ∀ t : ℝ, (clockCover N s c : ℝ) ≤ t →
        sourceUnrankedForest
          (state (traceEndpoint N (Fintype.card Copy) s (literalMarkedTrace N (Fintype.card Copy) t s c).2))
          Finset.univ = {q} := by
  obtain ⟨e, he, _, hcard⟩ := complete_ancestral_trace_terminal N s c hs hc
  have hraw : traceEndpoint N (Fintype.card Copy) s (completeAncestralTrace N s c).2 = e := by
    cases hz : (completeAncestralTrace N s c).1 <;> simp [decodedEndpoint, hz] at he
    exact he
  have hcardone : liveCard e = 1 := by
    have hpos := admitted_live_card_positive N e
    omega
  obtain ⟨q, hF, hW, hL⟩ := one_live_unranked_forest (state e) e.property.forest hcardone
  refine ⟨q, hW, hL, ?_⟩
  intro t ht
  rw [complete_ancestral_trace_stable N s c t ht, hraw]
  exact hF

/-- The whole actual original sorted calendar supplies root support. No
BoundaryReady, AncestralRoot or desired endpoint law is a FINAL input. -/
theorem original_initialized_calendar_root_ae (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      AncestralRoot N (calendarEnd N (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register) past) := by
  have hp : ∀ᵐ d ∂(sourceProgram N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).toMeasure, AncestralRoot N d := by
    apply ae_iff_of_countable.mpr
    intro d hd
    apply initialized_original_calendar_ancestral_support N C sample register H gamma common r
    apply (PMF.mem_support_iff _ _).mpr
    rwa [PMF.toMeasure_apply_singleton _ d (by trivial)] at hd
  rw [← actual_calendar_endpoint_law N r (compiledCalendarProgram N C H gamma common)
    (initialCode N sample register)] at hp
  exact ae_of_ae_map (calendar_end_measurable N _ _).aemeasurable hp

/-- Complete original fibres retain their actual masses, including null
fibres. Root support and tail absorption are derived on those same fibres. -/
theorem initialized_complete_terminal_ae (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      AncestralRoot N (completeEnd N (compiledCalendarProgram N C H gamma common) z) ∧
        liveCard (completeEnd N (compiledCalendarProgram N C H gamma common) z) ≤ 1 := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  have hp := original_initialized_calendar_root_ae N C sample register H gamma common r
  rw [completeCalendarTraceLaw, ae_finsetSum_measure_iff]
  intro d _
  letI := actual_calendar_trace_probability N r ops s
  letI := complete_ancestral_trace_probability N r d
  have hi : Measurable (fun z : (Fin ops.length → SegmentRecord N sample) ×
      (Bool × ClockTrace N sample (Fintype.card Copy)) => (d, z)) :=
    measurable_const.prodMk measurable_id
  have ht : MeasurableSet {e : Code N sample | AncestralRoot N e ∧ liveCard e ≤ 1} := by trivial
  have hm := ht.preimage (complete_end_measurable N (sample := sample) ops)
  apply (ae_map_iff hi.aemeasurable hm).mpr
  apply (Measure.ae_prod_iff_ae_ae (hm.preimage hi)).mpr
  filter_upwards [ae_restrict_of_ae hp,
    ae_restrict_mem (measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const)]
      with past hroot he
  have hd : AncestralRoot N d := by simpa only [he] using hroot
  exact actual_ancestral_raw_terminal_ae N r d hd

theorem initialized_complete_live_card_one_ae [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      liveCard (completeEnd N (compiledCalendarProgram N C H gamma common) z) = 1 := by
  filter_upwards [initialized_complete_terminal_ae N C sample register H gamma common r] with z hz
  have hpos := admitted_live_card_positive N (completeEnd N (compiledCalendarProgram N C H gamma common) z)
  omega

theorem initialized_complete_one_full_tree_ae [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      ∃ q : UnrankedTree Copy,
        sourceUnrankedForest (state (completeEnd N (compiledCalendarProgram N C H gamma common) z))
          Finset.univ = {q} ∧ treeWellLabelled q ∧ treeLeaves q = Finset.univ := by
  filter_upwards [initialized_complete_live_card_one_ae N C sample register H gamma common r] with z hz
  exact one_live_unranked_forest (state (completeEnd N (compiledCalendarProgram N C H gamma common) z))
    (completeEnd N (compiledCalendarProgram N C H gamma common) z).property.forest hz

/-- Empty Copy observes an empty forest; no nonempty tree/default leaf is
fabricated. Distinct-pair assertions are vacuous on empty/singleton carriers. -/
theorem source_forest_empty [IsEmpty Copy] (s : State V E Copy) (keep : Finset Copy) :
    sourceUnrankedForest s keep = ∅ := by
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro q hq
  obtain ⟨x, _, _, _, _⟩ := (mem_sourceUnrankedForest s keep q).mp hq
  exact isEmptyElim x

theorem singleton_no_offdiagonal [Subsingleton Copy] (a b : Copy) (hab : a ≠ b) : False :=
  hab (Subsingleton.elim a b)

/-- A graph-independent PROPERTY of the actual observable fields. The real
Decoration is an existential proof witness, not observed hidden coordinates
or a recovery of real ages from bins. Every original leaf/graft is retained. -/
def WholePairBinWitness (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (a : RawObservedRecord Copy Tag) : Prop :=
  ∃ t : Genealogy Copy, ∃ d : Decoration t,
    t.WellLabelled ∧ t.leaves = Finset.univ ∧ a.1 = {toUnranked t} ∧
      ∀ x y : Copy, x ≠ y → a.2 x y = bin (pairAge leafAge t d x y)

/-- ALL distinct pairs now lie in the SAME genuine terminal component. The
same physical decoder and derived original singleton initialization supply
their age bins; one-tree/matrix correctness is not a supplied premise. -/
theorem initialized_complete_all_pairs_ae [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register),
      WholePairBinWitness (fun x => C.age (N.leaf (sample x))) bin
        (sourceUnrankedForest (state (completeEnd N (compiledCalendarProgram N C H gamma common) z))
          Finset.univ,
        completeTags N bin (compiledCalendarProgram N C H gamma common) (initialCode N sample register)
          (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b)) z) := by
  let ops := compiledCalendarProgram N C H gamma common
  filter_upwards [initialized_complete_live_card_one_ae N C sample register H gamma common r,
    actual_complete_tag_decoder N r bin (fun x => C.age (N.leaf (sample x))) ops
      (initialCode N sample register) (firstOriginalDate N C) (leafAgeMatrix N C sample)
      (actual_leaf_initialCode_decorates N C sample register)] with z hz hdec
  let e := completeEnd N ops z
  obtain ⟨l, hl, hanc⟩ := one_live_ancestor (state e) e.property.forest hz
  obtain ⟨d, hd, _⟩ := hdec l hl
  have hL : ((state e).genealogy l).leaves = Finset.univ := by
    apply Finset.ext
    intro x
    rw [e.property.forest.leaf_fiber l hl x]
    simp [hanc x]
  obtain ⟨q, hF, _, _⟩ := one_live_unranked_forest (state e) e.property.forest hz
  obtain ⟨x⟩ := ‹Nonempty Copy›
  have hm : toUnranked ((state e).genealogy l) ∈ sourceUnrankedForest (state e) Finset.univ := by
    apply (mem_sourceUnrankedForest (state e) Finset.univ _).mpr
    exact ⟨x, Finset.mem_univ x, (state e).genealogy l, by rw [hanc x, genealogy_prune_univ], rfl⟩
  have hq : toUnranked ((state e).genealogy l) = q := by
    rw [hF] at hm
    exact Finset.mem_singleton.mp hm
  have hFt : sourceUnrankedForest (state e) Finset.univ = {toUnranked ((state e).genealogy l)} := by
    rw [hq]
    exact hF
  refine ⟨(state e).genealogy l, d, e.property.forest.wellLabelled l hl, hL, hFt, ?_⟩
  intro a b _
  have htags := congrFun (congrFun
    (map_complete_matrix N bin ops (initialCode N sample register)
      (firstOriginalDate N C) (leafAgeMatrix N C sample) z).symm a) b
  exact htags.trans (congrArg bin (hd a (by rw [hL]; exact Finset.mem_univ a)
    b (by rw [hL]; exact Finset.mem_univ b)))

/-- Converts the proved physical complete-record event to every POSITIVE
actual initialized joint PMF atom, without a desired PMF or support field. -/
theorem initialized_completed_joint_all_pairs_support [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) {q : TaggedEndpoint (Tag := Tag) N sample}
    (hq : q ∈ (completedJoint N r bin hbin (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register) (firstOriginalDate N C)
      (fun a b => bin (leafAgeMatrix N C sample a b))).support) :
    WholePairBinWitness (fun x => C.age (N.leaf (sample x))) bin
      (sourceUnrankedForest (state q.1) Finset.univ, q.2) := by
  let ops := compiledCalendarProgram N C H gamma common
  let good := fun q : TaggedEndpoint (Tag := Tag) N sample =>
    WholePairBinWitness (fun x => C.age (N.leaf (sample x))) bin
      (sourceUnrankedForest (state q.1) Finset.univ, q.2)
  have hm : MeasurableSet {q : TaggedEndpoint (Tag := Tag) N sample | good q} :=
    (Set.to_countable _).measurableSet
  have hp : ∀ᵐ q ∂(completedJoint N r bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b))).toMeasure, good q := by
    rw [completed_joint_toMeasure]
    apply (ae_map_iff (complete_readout_measurable N bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (fun a b => bin (leafAgeMatrix N C sample a b))).aemeasurable hm).mpr
    exact initialized_complete_all_pairs_ae N C sample register H gamma common r bin
  apply (ae_iff_of_countable.mp hp) q
  rw [PMF.toMeasure_apply_singleton _ q (measurableSet_singleton q)]
  exact (PMF.mem_support_iff _ _).mp hq

/-- The SAME original once-drawn COMMON register mixture carries the event.
No independent tags, entering law or resampling are introduced. -/
theorem natural_completed_joint_all_pairs_support [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) {q : TaggedEndpoint (Tag := Tag) N sample}
    (hq : q ∈ (naturalCompletedJoint N C sample p r bin hbin
      (compiledCalendarProgram N C H (originalGamma p) common)).support) :
    WholePairBinWitness (fun x => C.age (N.leaf (sample x))) bin
      (sourceUnrankedForest (state q.1) Finset.univ, q.2) := by
  unfold naturalCompletedJoint at hq
  obtain ⟨register, _, hrow⟩ := (PMF.mem_support_bind_iff _ _ _).mp hq
  exact initialized_completed_joint_all_pairs_support N C sample register H (originalGamma p)
    common r bin hbin hrow

theorem original_copy_nonempty {sample : Copy → X}
    (s : OriginalParameters.{u,v,w,x} Copy X sample) : Nonempty Copy := by
  have hX : 0 < Fintype.card X := by have h := s.four_taxa; omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hX
  obtain ⟨a, _⟩ := s.all_taxa_sampled x
  exact ⟨a⟩

/-- Actual source-family observation now has one full labelled tree and ALL
offdiagonal physical pair bins. Nonempty Copy and zero leaf ages are DERIVED
from the original sampled/contemporaneous fields, not new support premises. -/
theorem native_finite_all_pairs_support {sample : Copy → X} (mode : Bool)
    (bin : ℝ → Tag) (hbin : Measurable bin) (s : OriginalParameters.{u,v,w,x} Copy X sample)
    {a : FiniteObservedRecord Copy Tag} (ha : a ∈ (nativeFiniteLaw mode bin hbin s).support) :
    WholePairBinWitness (fun _ => 0) bin (forgetFiniteRecord a) := by
  letI := original_copy_nonempty s
  unfold nativeFiniteLaw actualCompiledObservation at ha
  obtain ⟨q, hq, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  have hgood := natural_completed_joint_all_pairs_support s.original.network s.original.calendar
    sample s.registry s.inheritance (fun _ => mode) s.rates bin hbin hq
  have hleaf : (fun x : Copy => s.original.calendar.age (s.original.network.leaf (sample x))) =
      (fun _ => 0) := by
    funext x
    exact s.contemporaneous (sample x)
  rw [hleaf] at hgood
  have hf : forgetFiniteRecord a = observedRecord s q := by
    rw [← he]
    exact boundedObservedRecord_forget s q
  rw [hf]
  exact hgood

/-- Every configured selected distinct pair retains that SAME physical bin.
The earlier actual-pruning theorem determines its topology separately. -/
theorem whole_pair_bin_witness_panel (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (a : RawObservedRecord Copy Tag) (h : WholePairBinWitness leafAge bin a) (keep : Finset Copy) :
    ∃ t : Genealogy Copy, ∃ d : Decoration t,
      t.WellLabelled ∧ t.leaves = Finset.univ ∧ a.1 = {toUnranked t} ∧
        ∀ x y : PanelCopy keep, x ≠ y →
          (panelReadout keep a).2 x y = bin (pairAge leafAge t d x.val y.val) := by
  obtain ⟨t, d, hW, hL, hF, hB⟩ := h
  refine ⟨t, d, hW, hL, hF, ?_⟩
  intro x y hxy
  exact hB x.val y.val (fun he => hxy (Subtype.ext he))

end CloudG6.NaturalCompletedAllPairs
