import G2ActualEpochHistoryLaw
import G2SourceFiniteHistory
import G2CompleteAncestralPath
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Data.Finset.Max

/-!
Cross-carrier projection of the actual all-time constant-epoch path law.
Contributor: dot (OpenAI), 6 October 2026.

Ordered histories come from the literal original clock vector. Their common
source law is derived from the original full/small source rows. Arbitrary
finite time sets are then covered by cumulative nonnegative increments, and
Mathlib's finite-measure product-cylinder uniqueness theorem (Rémy Degenne and
Peter Pfaffelhuber) identifies the measures on the product path space.
No projectivity or finite-dimensional equality is assumed. The final corollary
transports the finite random-cover trace readout, without a time truncation.
Physical calendar assembly and stronger path topologies are outside this result.
-/
namespace GProgram.G2.EpochPathProjection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.CompleteAncestralPath
open GProgram.G2.FiniteAncestralTrace GProgram.G2.SourceFiniteHistory
open GProgram.G2.ActualEpochHistoryLaw
open scoped Classical NNReal

/-- Appending an increment retains every previous cumulative observation and
adds one at the new total duration. This includes empty grids and zero steps. -/
lemma cumulative_times_extend (ds : List ℝ≥0) (t : ℝ≥0) :
    (∀ i : Fin ds.length, ∃ j : Fin (ds ++ [t]).length,
      cumulativeTimes (ds ++ [t]) j = cumulativeTimes ds i) ∧
    ∃ j : Fin (ds ++ [t]).length, cumulativeTimes (ds ++ [t]) j = ds.sum + t := by
  induction ds with
  | nil =>
      constructor
      · intro i
        exact Fin.elim0 i
      · exact ⟨⟨0, by simp⟩, by simp [cumulativeTimes]⟩
  | cons a ds ih =>
      constructor
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · exact ⟨⟨0, by simp⟩, rfl⟩
        · obtain ⟨j,hj⟩ := ih.1 k
          refine ⟨j.succ, ?_⟩
          simpa only [List.cons_append,cumulativeTimes,Fin.cons_succ] using
            congrArg (fun x : ℝ≥0 => a+x) hj
      · obtain ⟨j,hj⟩ := ih.2
        refine ⟨j.succ, ?_⟩
        simpa [cumulativeTimes,List.sum_cons,add_assoc] using
          congrArg (fun x : ℝ≥0 => a+x) hj

/-- Every finite observation set, including time zero, is represented by a
finite ordered grid of nonnegative increments. No bounded horizon is fixed. -/
lemma finite_times_cumulative_cover (I : Finset ℝ≥0) :
    ∃ ds : List ℝ≥0, ds.sum = I.sup id ∧
      ∀ t ∈ I, ∃ i : Fin ds.length, cumulativeTimes ds i = t := by
  induction I using Finset.induction_on_max with
  | empty => exact ⟨[], by simp, by simp⟩
  | @insert a I hmax ih =>
      obtain ⟨ds,hsum,hcover⟩ := ih
      have hle : ds.sum ≤ a := by
        rw [hsum]
        exact Finset.sup_le (fun b hb => le_of_lt (hmax b hb))
      refine ⟨ds ++ [a-ds.sum], ?_, ?_⟩
      · simp only [List.sum_append,List.sum_singleton,add_tsub_cancel_of_le hle]
        rw [Finset.sup_insert]
        exact (sup_eq_left.mpr (hsum ▸ hle)).symm
      · intro t ht
        rcases Finset.mem_insert.mp ht with hta | ht
        · obtain ⟨j,hj⟩ := (cumulative_times_extend ds (a-ds.sum)).2
          exact ⟨j,hj.trans ((add_tsub_cancel_of_le hle).trans hta.symm)⟩
        · obtain ⟨i,hi⟩ := hcover t ht
          obtain ⟨j,hj⟩ := (cumulative_times_extend ds (a-ds.sum)).1 i
          exact ⟨j,hj.trans hi⟩

noncomputable def gridReadout {S : Type*} (ds : List ℝ≥0) (p : ℝ≥0 → S) : Fin ds.length → S :=
  fun i => p (cumulativeTimes ds i)

lemma grid_readout_measurable {S : Type*} [MeasurableSpace S] (ds : List ℝ≥0) :
    Measurable (gridReadout (S := S) ds) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (cumulativeTimes ds i))

def pathProjection {S Q : Type*} (f : S → Q) (p : ℝ≥0 → S) : ℝ≥0 → Q :=
  fun t => f (p t)

lemma path_projection_measurable {S Q : Type*} [MeasurableSpace S] [MeasurableSpace Q]
    {f : S → Q} (hf : Measurable f) : Measurable (pathProjection f) :=
  measurable_pi_lambda _ (fun t => hf.comp (measurable_pi_apply t))

lemma history_projection_measurable {S Q : Type*} [MeasurableSpace S] [MeasurableSpace Q]
    {f : S → Q} (hf : Measurable f) (n : Nat) :
    Measurable (historyProjection (n := n) f) :=
  measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))

/-- Ordered-grid laws determine all finite marginals by a measurable coordinate
reindexing. The source sample spaces need not be the same. -/
lemma finite_marginals_of_grid_laws {S : Type*} [MeasurableSpace S]
    (μ ν : Measure (ℝ≥0 → S))
    (hgrid : ∀ ds, μ.map (gridReadout ds) = ν.map (gridReadout ds))
    (I : Finset ℝ≥0) : μ.map I.restrict = ν.map I.restrict := by
  obtain ⟨ds,_,hcover⟩ := finite_times_cumulative_cover I
  choose j hj using (fun t : I => hcover t.val t.property)
  let reindex : (Fin ds.length → S) → I → S := fun z t => z (j t)
  have hm : Measurable reindex :=
    measurable_pi_lambda _ (fun t => measurable_pi_apply (j t))
  have he : reindex ∘ gridReadout ds = I.restrict := by
    funext p t
    change p (cumulativeTimes ds (j t)) = p t.val
    rw [hj t]
  have h := congrArg (fun η : Measure (Fin ds.length → S) => η.map reindex) (hgrid ds)
  rw [Measure.map_map hm (grid_readout_measurable ds),
    Measure.map_map hm (grid_readout_measurable ds),he] at h
  exact h

/-- Product-measure uniqueness uses a finite marginal family obtained from μ
itself; no source projectivity equation is an assumption. -/
lemma path_measure_eq_of_grid_laws {S : Type*} [MeasurableSpace S]
    (μ ν : Measure (ℝ≥0 → S)) [IsFiniteMeasure μ]
    (hgrid : ∀ ds, μ.map (gridReadout ds) = ν.map (gridReadout ds)) : μ = ν := by
  let P : (I : Finset ℝ≥0) → Measure (I → S) := fun I => μ.map I.restrict
  have hμ : IsProjectiveLimit μ P := fun _ => rfl
  have hν : IsProjectiveLimit ν P :=
    fun I => (finite_marginals_of_grid_laws μ ν hgrid I).symm
  exact hμ.unique hν

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Only the finite coordinate carrier is discrete; time-indexed paths use the
ordinary product measurable space. -/
local instance joinedIndexMeasurable (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) :
    MeasurableSpace (JoinedIndex N sample keep) := ⊤

noncomputable def fullObservedEpochPath (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) (c : Choice N s → ℝ) :
    ℝ≥0 → JoinedIndex N sample keep :=
  pathProjection (fun d => joinedProjection N keep (.inl d)) (literalEpochPath N s c)

noncomputable def smallObservedEpochPath (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (d : Code N (selectedSample sample keep)) (c : Choice N d → ℝ) :
    ℝ≥0 → JoinedIndex N sample keep :=
  pathProjection (fun z => joinedProjection N keep (.inr z)) (literalEpochPath N d c)

lemma full_observed_epoch_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : Measurable (fullObservedEpochPath N keep s) :=
  (path_projection_measurable measurable_from_top).comp (literal_epoch_path_measurable N s)

lemma small_observed_epoch_path_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (d : Code N (selectedSample sample keep)) :
    Measurable (smallObservedEpochPath N keep d) :=
  (path_projection_measurable measurable_from_top).comp (literal_epoch_path_measurable N d)

/-- Actual ordered original-clock histories retain their proved source law
after any measurable coordinate observation. -/
theorem actual_observed_grid_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ds : List ℝ≥0) (s : Code N sample)
    {Q : Type*} [MeasurableSpace Q] (f : Code N sample → Q) (hf : Measurable f) :
    ((currentPairClockMeasure N r s).map
      (fun c => pathProjection f (literalEpochPath N s c))).map (gridReadout ds) =
      ((epochSourceHistoryLaw N r ds s).map (historyProjection f)).toMeasure := by
  change ((currentPairClockMeasure N r s).map
    (pathProjection f ∘ literalEpochPath N s)).map (gridReadout ds) = _
  rw [Measure.map_map (grid_readout_measurable ds)
    ((path_projection_measurable hf).comp (literal_epoch_path_measurable N s))]
  change (currentPairClockMeasure N r s).map
    (historyProjection f ∘ actualEpochHistory N ds s) = _
  rw [← Measure.map_map (history_projection_measurable hf ds.length)
    (actual_epoch_history_measurable N ds s),actual_epoch_history_source_law,
    PMF.toMeasure_map _ _ (history_projection_measurable hf ds.length)]

/-- The actual full and small ordered histories have one common PMF. The
original source interval rows discharge every one-step transport premise. -/
theorem cross_carrier_epoch_source_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ds : List ℝ≥0)
    (s : Code N sample) (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (epochSourceHistoryLaw N r ds s).map
      (historyProjection (fun z => joinedProjection N keep (.inl z))) =
    (epochSourceHistoryLaw N r ds d).map
      (historyProjection (fun z => joinedProjection N keep (.inr z))) := by
  have hf := history_projection
    (fun (t : ℝ≥0) (z : Code N sample) => sourceTimeKernel N r t z)
    (fun t q => commonProgramStep N r keep (.interval t) q)
    (fun z => joinedProjection N keep (.inl z))
    (fun t z => full_source_step_common N r keep (.interval t) z) ds s
  have hd := history_projection
    (fun (t : ℝ≥0) (z : Code N (selectedSample sample keep)) => sourceTimeKernel N r t z)
    (fun t q => commonProgramStep N r keep (.interval t) q)
    (fun z => joinedProjection N keep (.inr z))
    (fun t z => small_source_step_common N r keep (.interval t) z) ds d
  have he : joinedProjection N keep (.inl s) = joinedProjection N keep (.inr d) :=
    Subtype.ext hs
  rw [he] at hf
  exact hf.trans hd.symm

/-- The observed path measure on either actual source carrier. Both branches
use their own original clock vectors and the same original rates. -/
noncomputable def joinedObservedEpochPathLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    JoinedCode N sample keep → Measure (ℝ≥0 → JoinedIndex N sample keep)
  | .inl s => (currentPairClockMeasure N r s).map (fullObservedEpochPath N keep s)
  | .inr d => (currentPairClockMeasure N r d).map (smallObservedEpochPath N keep d)

lemma joined_observed_epoch_path_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : JoinedCode N sample keep) :
    IsProbabilityMeasure (joinedObservedEpochPathLaw N r keep s) := by
  cases s with
  | inl s =>
      letI := GProgram.G2.HistoryResidualAttachment.current_clock_probability N r s
      exact Measure.isProbabilityMeasure_map (full_observed_epoch_path_measurable N keep s).aemeasurable
  | inr d =>
      letI := GProgram.G2.HistoryResidualAttachment.current_clock_probability N r d
      exact Measure.isProbabilityMeasure_map (small_observed_epoch_path_measurable N keep d).aemeasurable

/-- Both branches have the common original-source grid law, so this identity
also supplies same-carrier representation independence. -/
theorem joined_observed_epoch_grid_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ds : List ℝ≥0)
    (s : JoinedCode N sample keep) :
    (joinedObservedEpochPathLaw N r keep s).map (gridReadout ds) =
      (historyLaw (fun t q => commonProgramStep N r keep (.interval t) q) ds
        (joinedProjection N keep s)).toMeasure := by
  cases s with
  | inl s =>
      change ((currentPairClockMeasure N r s).map
        (fun c => pathProjection (fun q => joinedProjection N keep (.inl q))
          (literalEpochPath N s c))).map (gridReadout ds) = _
      rw [actual_observed_grid_law N r ds s _ measurable_from_top]
      congr 1
      exact history_projection
        (fun (t : ℝ≥0) (z : Code N sample) => sourceTimeKernel N r t z)
        (fun t q => commonProgramStep N r keep (.interval t) q)
        (fun z => joinedProjection N keep (.inl z))
        (fun t z => full_source_step_common N r keep (.interval t) z) ds s
  | inr d =>
      change ((currentPairClockMeasure N r d).map
        (fun c => pathProjection (fun q => joinedProjection N keep (.inr q))
          (literalEpochPath N d c))).map (gridReadout ds) = _
      rw [actual_observed_grid_law N r ds d _ measurable_from_top]
      congr 1
      exact history_projection
        (fun (t : ℝ≥0) (z : Code N (selectedSample sample keep)) => sourceTimeKernel N r t z)
        (fun t q => commonProgramStep N r keep (.interval t) q)
        (fun z => joinedProjection N keep (.inr z))
        (fun t z => small_source_step_common N r keep (.interval t) z) ds d

/-- Representation independence covers all four full/small carrier pairings.
Only equality of the original labelled selected views is required. -/
theorem joined_observed_epoch_path_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s d : JoinedCode N sample keep)
    (hs : joinedProjection N keep s = joinedProjection N keep d) :
    joinedObservedEpochPathLaw N r keep s = joinedObservedEpochPathLaw N r keep d := by
  letI := joined_observed_epoch_path_probability N r keep s
  apply path_measure_eq_of_grid_laws
  intro ds
  rw [joined_observed_epoch_grid_law,joined_observed_epoch_grid_law,hs]

/-- Equality on every measurable set of the entire nonnegative-time product
path space. Original rates and the selected-view compatibility are the only
source inputs, including for empty panels and carriers. -/
theorem actual_cross_carrier_epoch_path_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (currentPairClockMeasure N r s).map (fullObservedEpochPath N keep s) =
      (currentPairClockMeasure N r d).map (smallObservedEpochPath N keep d) := by
  exact joined_observed_epoch_path_eq N r keep (.inl s) (.inr d) (Subtype.ext hs)

/-- The complete finite random-cover records have the same projected all-time
readout law. This follows from literal-path equality, not from fixed-horizon
truncation or a postulated cross-carrier trace law. -/
theorem actual_cross_carrier_complete_path_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample)
    (d : Code N (selectedSample sample keep))
    (hs : selectedView (state s) keep = liftView keep (selectedView (state d) Finset.univ)) :
    (completeAncestralTraceLaw N r s).map
      (fun z => pathProjection (fun q => joinedProjection N keep (.inl q)) (completePath N s z)) =
    (completeAncestralTraceLaw N r d).map
      (fun z => pathProjection (fun q => joinedProjection N keep (.inr q)) (completePath N d z)) := by
  change (completeAncestralTraceLaw N r s).map
    (pathProjection (fun q => joinedProjection N keep (.inl q)) ∘ completePath N s) =
    (completeAncestralTraceLaw N r d).map
    (pathProjection (fun q => joinedProjection N keep (.inr q)) ∘ completePath N d)
  rw [← Measure.map_map (path_projection_measurable measurable_from_top)
    (complete_path_measurable N s),
    ← Measure.map_map (path_projection_measurable measurable_from_top)
    (complete_path_measurable N d),actual_complete_path_law,actual_complete_path_law,
    Measure.map_map (path_projection_measurable measurable_from_top)
    (literal_epoch_path_measurable N s),
    Measure.map_map (path_projection_measurable measurable_from_top)
    (literal_epoch_path_measurable N d)]
  exact actual_cross_carrier_epoch_path_law N r keep s d hs

#print axioms cumulative_times_extend
#print axioms finite_times_cumulative_cover
#print axioms grid_readout_measurable
#print axioms path_projection_measurable
#print axioms history_projection_measurable
#print axioms finite_marginals_of_grid_laws
#print axioms path_measure_eq_of_grid_laws
#print axioms full_observed_epoch_path_measurable
#print axioms small_observed_epoch_path_measurable
#print axioms actual_observed_grid_law
#print axioms cross_carrier_epoch_source_history
#print axioms joined_observed_epoch_path_probability
#print axioms joined_observed_epoch_grid_law
#print axioms joined_observed_epoch_path_eq
#print axioms actual_cross_carrier_epoch_path_law
#print axioms actual_cross_carrier_complete_path_law
end GProgram.G2.EpochPathProjection
