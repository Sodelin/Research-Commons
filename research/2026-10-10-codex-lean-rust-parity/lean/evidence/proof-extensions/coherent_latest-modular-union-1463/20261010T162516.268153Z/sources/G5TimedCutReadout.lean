import G2FaithfulTimedOutput
import G5TriplePartitionReadout

/-!
# G5 cut survival read directly from completed timed observations
Contributor: dot, 2026-10-09. Candidate pending compiler/source review.
The strict age inequalities correspond to the original inclusive-merger cut:
a merger exactly at the cut has already joined its pair. The absolute offset
is firstOriginalDate; no source time is silently translated or redrawn.
-/
namespace GProgram.G5.TimedCutReadout
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.PairBirthFold GProgram.G2.PairBirthThreshold
open GProgram.G2.WholeMatrixAges GProgram.G2.AncestralAgeCertificate
open GProgram.G2.CalendarDecoration GProgram.G2.CompleteDecoration
open GProgram.G2.ActualPairCoalescence GProgram.G2.CalendarFirstAge
open GProgram.G2.SourcePairMatrixReadout GProgram.G2.FaithfulTimedOutput
open GProgram.G2.JointTimedObservation GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CompletedPathProjection GProgram.G2.CompleteEpochPath
open GProgram.G5.SelectedDiscreteSurvival GProgram.G5.TriplePartitionReadout
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CalendarHistoryBinding.joinedMeasurable

/-- A measurable event on the authorized completed observation only. -/
def TimedNoMerger (keep : Finset Copy) (a : ℝ) (z : TimedObservation Copy) : Prop :=
  ∀ x ∈ keep, ∀ y ∈ keep, x ≠ y → (z.2 x y).1 = true ∧ a < (z.2 x y).2

lemma timed_no_merger_measurable (keep : Finset Copy) (a : ℝ) :
    MeasurableSet {z : TimedObservation Copy | TimedNoMerger keep a z} := by
  simp only [TimedNoMerger, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro x
  apply MeasurableSet.iInter
  intro hx
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro hy
  apply MeasurableSet.iInter
  intro hxy
  have hm : Measurable (fun z : TimedObservation Copy => z.2 x y) :=
    (measurable_pi_apply y).comp ((measurable_pi_apply x).comp measurable_snd)
  exact (measurableSet_eq_fun hm.fst measurable_const).inter
    (measurableSet_lt measurable_const hm.snd)

/-- Restore the inclusive threshold already proved inside the inherited
first-age reader, keeping its actual complete-record certificate. -/
theorem complete_matrix_cut_threshold (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (z : CompleteCalendarRecord N sample ops) (x y : Copy)
    (hz : CompleteAgeCertificate N
      (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops s z)
    (hs : ¬ sameBlock (selectedView (state s) Finset.univ) x y) (t : ℝ≥0) :
    (state (GProgram.G2.CalendarFirstAge.recordPath N ops s z.2.1 z.2.2.2 t)).ancestor x =
        (state (GProgram.G2.CalendarFirstAge.recordPath N ops s z.2.1 z.2.2.2 t)).ancestor y ↔
      completeMatrix N ops s offset M z x y ≤ offset + (t : ℝ) := by
  rcases hz with ⟨hst,hpair,hcal,hn,ho,hend⟩
  have hc := hpair x y
  have hs' : (state s).ancestor x ≠ (state s).ancestor y := by
    intro h
    exact hs ((selected_same_block (state s) s.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y)).mpr h)
  have he : (state (completeEnd N ops z)).ancestor x = (state (completeEnd N ops z)).ancestor y :=
    (selected_same_block (state (completeEnd N ops z)) (completeEnd N ops z).property.forest
      Finset.univ (Finset.mem_univ x) (Finset.mem_univ y)).mp hend
  obtain ⟨a,hbirth⟩ := (complete_first_birth_exists_iff_endpoint N ops s 0 z x y hc hs').mpr he
  have hrbirth : recordFirstPairBirth N ops s 0 z.2.1 z.2.2.2 x y = some a := by
    rw [record_birth_as_complete N ops s 0 z x y hst]
    exact hbirth
  have ht : PairTraceMonotone N (Fintype.card Copy) (calendarEnd N ops s z.2.1) z.2.2.2 x y := by
    rw [←hst]
    exact hc.2.2.1
  obtain ⟨_,hth⟩ := record_birth_threshold N ops s z.2.1 z.2.2.2 x y a
    hc.1 ht hcal hn ho hs' hrbirth
  have hboff : completeFirstPairBirth N ops s offset z x y = some (offset+a) := by
    rw [←record_birth_as_complete N ops s offset z x y hst]
    simpa only [add_zero,hrbirth,Option.map_some] using
      record_birth_translate N ops s offset 0 z.2.1 z.2.2.2 x y
  have hm : completeMatrix N ops s offset M z x y = offset+a := by
    rw [complete_matrix_entry_eq_first_birth N ops s offset M z x y hc,hboff]
    rfl
  rw [hm, add_le_add_iff_left]
  exact hth t

/-- The original completed timed observation identifies the actual selected
ancestry cut, on one full-mass set for ALL cuts at once. No posterior or path
law equality is provided as a hypothesis. -/
theorem actual_timed_survival_is_cut_discreteness (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register),
      ∀ t : ℝ≥0,
      TimedNoMerger keep (firstOriginalDate N C + (t : ℝ))
        (timedObservation N C sample keep (chronologicalPath N (compiledCalendarProgram N C H gamma common)
          (observeCompleted N (fun d => joinedProjection N keep (.inl d))
            (compiledCalendarProgram N C H gamma common) (initialCode N sample register) z))) ↔
      DiscreteView keep (selectedView (state (GProgram.G2.CalendarFirstAge.recordPath N
        (compiledCalendarProgram N C H gamma common) (initialCode N sample register)
        z.2.1 z.2.2.2 t)) keep) := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  have hroot : ∀ d, sourceProgram N r ops s d ≠ 0 → AncestralRoot N d := by
    intro d hd
    exact initialized_original_calendar_ancestral_support N C sample register H gamma common r
      ((PMF.mem_support_iff _ _).mpr hd)
  have hcert : ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, ∀ x y : Copy,
      CompleteAgeCertificate N (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops s z := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    exact actual_complete_pair_certificate N Finset.univ (Finset.mem_univ x) (Finset.mem_univ y) r ops s hroot
  filter_upwards [hcert, actual_original_faithful_output N C sample register H gamma common r keep] with z hz hout
  intro t
  rw [hout, actual_discrete_view_iff_injOn]
  constructor
  · intro h x hx y hy he
    by_contra hxy
    have hage := (h x hx y hy hxy).2
    have hinit : ¬ sameBlock (selectedView (state s) Finset.univ) x y := by
      intro h
      exact hxy ((initial_pair_iff N sample register Finset.univ (Finset.mem_univ x) (Finset.mem_univ y)).mp h)
    have hle := (complete_matrix_cut_threshold N ops s (firstOriginalDate N C)
      (fun x _ => C.age (N.leaf (sample x))) z x y (hz x y) hinit t).mp he
    have hread : (matrixObservation N keep (completeEnd N ops z)
      (completeMatrix N ops s (firstOriginalDate N C) (fun x _ => C.age (N.leaf (sample x))) z)).2 x y =
        (true, completeMatrix N ops s (firstOriginalDate N C) (fun x _ => C.age (N.leaf (sample x))) z x y) := by
      have hkeep : x ∈ keep ∧ y ∈ keep := ⟨hx, hy⟩
      simp only [matrixObservation, if_pos hkeep]
    rw [hread] at hage
    exact (not_lt_of_ge hle) hage
  · intro hi x hx y hy hxy
    have hinit : ¬ sameBlock (selectedView (state s) Finset.univ) x y := by
      intro h
      exact hxy ((initial_pair_iff N sample register Finset.univ (Finset.mem_univ x) (Finset.mem_univ y)).mp h)
    have hn : ¬ completeMatrix N ops s (firstOriginalDate N C)
        (fun x _ => C.age (N.leaf (sample x))) z x y ≤ firstOriginalDate N C + (t : ℝ) := by
      intro hle
      exact hxy (hi hx hy ((complete_matrix_cut_threshold N ops s (firstOriginalDate N C)
        (fun x _ => C.age (N.leaf (sample x))) z x y (hz x y) hinit t).mpr hle))
    simpa [matrixObservation, hx, hy] using And.intro (rfl : true = true) (lt_of_not_ge hn)

/-- Five-partition cut decoder on the completed timed observation. The copy
indexing is a readout only; original labels and source registers are retained. -/
noncomputable def timedPartitionAt (e : Fin 3 → Copy) (a : ℝ)
    (z : TimedObservation Copy) : Fin 5 :=
  if (z.2 (e 0) (e 1)).2 ≤ a then
    (if (z.2 (e 0) (e 2)).2 ≤ a then 4 else 1)
  else if (z.2 (e 0) (e 2)).2 ≤ a then 2
  else if (z.2 (e 1) (e 2)).2 ≤ a then 3 else 0

lemma timed_partition_at_measurable (e : Fin 3 → Copy) (a : ℝ) :
    Measurable (timedPartitionAt e a) := by
  have hm (i j : Fin 3) : Measurable (fun z : TimedObservation Copy => (z.2 (e i) (e j)).2) :=
    ((measurable_pi_apply (e j)).comp ((measurable_pi_apply (e i)).comp measurable_snd)).snd
  exact Measurable.ite (measurableSet_le (hm 0 1) measurable_const)
    (Measurable.ite (measurableSet_le (hm 0 2) measurable_const) measurable_const measurable_const)
    (Measurable.ite (measurableSet_le (hm 0 2) measurable_const) measurable_const
      (Measurable.ite (measurableSet_le (hm 1 2) measurable_const) measurable_const measurable_const))

/-- All cut partitions, including later mergers, are functions of the same
completed timed output. This is a simultaneous source-bound statement. -/
theorem actual_timed_partition_is_cut_partition (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy)
    (e : Fin 3 → Copy) (he : Function.Injective e) (hk : ∀ i, e i ∈ keep) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register),
      ∀ t : ℝ≥0,
      timedPartitionAt e (firstOriginalDate N C + (t : ℝ))
        (timedObservation N C sample keep (chronologicalPath N (compiledCalendarProgram N C H gamma common)
          (observeCompleted N (fun d => joinedProjection N keep (.inl d))
            (compiledCalendarProgram N C H gamma common) (initialCode N sample register) z))) =
      ancestorPartition (fun i => (state (GProgram.G2.CalendarFirstAge.recordPath N
        (compiledCalendarProgram N C H gamma common) (initialCode N sample register)
        z.2.1 z.2.2.2 t)).ancestor (e i)) := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  have hroot : ∀ d, sourceProgram N r ops s d ≠ 0 → AncestralRoot N d := by
    intro d hd
    exact initialized_original_calendar_ancestral_support N C sample register H gamma common r
      ((PMF.mem_support_iff _ _).mpr hd)
  have hcert : ∀ᵐ z ∂completeCalendarTraceLaw N r ops s, ∀ x y : Copy,
      CompleteAgeCertificate N (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops s z := by
    exact ae_all_iff.mpr (fun x => ae_all_iff.mpr (fun y =>
      actual_complete_pair_certificate N Finset.univ (Finset.mem_univ x) (Finset.mem_univ y) r ops s hroot))
  filter_upwards [hcert, actual_original_faithful_output N C sample register H gamma common r keep] with z hz hout
  intro t
  have hp (i j : Fin 3) (hij : i ≠ j) :=
    complete_matrix_cut_threshold N ops s (firstOriginalDate N C)
      (fun x _ => C.age (N.leaf (sample x))) z (e i) (e j) (hz (e i) (e j))
      (by intro h
          exact he.ne hij ((initial_pair_iff N sample register Finset.univ
            (Finset.mem_univ (e i)) (Finset.mem_univ (e j))).mp h)) t
  rw [hout]
  have h01 := hp 0 1 (by decide)
  have h02 := hp 0 2 (by decide)
  have h12 := hp 1 2 (by decide)
  simp only [timedPartitionAt, matrixObservation, hk, and_self, if_true, ancestorPartition]
  dsimp only [ops, s] at h01 h02 h12
  simp only [h01, h02, h12]

#print axioms timed_no_merger_measurable
#print axioms complete_matrix_cut_threshold
#print axioms actual_timed_survival_is_cut_discreteness
#print axioms timed_partition_at_measurable
#print axioms actual_timed_partition_is_cut_partition
end GProgram.G5.TimedCutReadout
