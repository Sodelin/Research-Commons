import G2CompleteTerminalReadout

/-!
Faithful same-trace joint topology and graft-age observation.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.FaithfulTimedOutput
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.NativeParentRouting
open GProgram.G2.JointTimedObservation GProgram.G2.CompleteDecoration
open GProgram.G2.CompleteTimedSupport GProgram.G2.ChronologicalDecoration
open GProgram.G2.ChronologicalPruning GProgram.G2.SourcePairMatrixReadout
open GProgram.G2.CompleteTerminalReadout GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompletedPathProjection GProgram.G2.ChronologicalPathReadout
open GProgram.G2.CalendarFirstAge GProgram.G2.AncestralAgeCertificate
open GProgram.G2.ActualPairCoalescence GProgram.G2.EventualPathReadout
open GProgram.G2.CompleteEpochPath
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.EventualPathReadout.terminalOptionMeasurable
  GProgram.G2.CompleteCalendarAttachment.unrankedForestMeasurable

lemma timed_matrix_diagonal (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) (hm : HasTimedBound leafAge M s) (x : Copy) :
    M x x = leafAge x := by
  obtain ⟨n,hn⟩ := hm
  obtain ⟨d,hd,_,_⟩ := hn (s.ancestor x) (hs.ancestor_live x)
  have hx : x ∈ (s.genealogy (s.ancestor x)).leaves :=
    (hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl
  exact (hd x hx x hx).trans (pair_age_self leafAge _ d x hx)

noncomputable def matrixObservation (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) (M : Copy → Copy → ℝ) : TimedObservation Copy :=
  (some (sourceUnrankedForest (state s) keep),fun x y =>
    if x ∈ keep ∧ y ∈ keep then (true,M x y) else (false,0))

/-- The complete measurable path observation is the matrix of the actual
chronological graft decoration, with exactly its own terminal topology. -/
theorem actual_timed_output_identity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (ops : List (ProgramStep N)) (keep : Finset Copy)
    (z : CompleteCalendarRecord N sample ops)
    (hcert : ∀ x y : Copy, CompleteAgeCertificate N
      (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops (initialCode N sample register) z)
    (ht : terminalPath (chronologicalPath N ops (observeCompleted N
      (fun d => joinedProjection N keep (.inl d)) ops (initialCode N sample register) z)) =
      some (joinedProjection N keep (.inl (completeEnd N ops z))))
    (hm : HasTimedBound (fun x => C.age (N.leaf (sample x)))
      (completeMatrix N ops (initialCode N sample register) (firstOriginalDate N C)
        (fun x _ => C.age (N.leaf (sample x))) z) (state (completeEnd N ops z))) :
    timedObservation N C sample keep (chronologicalPath N ops (observeCompleted N
      (fun d => joinedProjection N keep (.inl d)) ops (initialCode N sample register) z)) =
      matrixObservation N keep (completeEnd N ops z)
        (completeMatrix N ops (initialCode N sample register) (firstOriginalDate N C)
          (fun x _ => C.age (N.leaf (sample x))) z) := by
  apply Prod.ext
  · change (terminalPath _).map _ = _
    rw [ht]
    rfl
  · funext x y
    by_cases hk : x ∈ keep ∧ y ∈ keep
    · by_cases he : x = y
      · subst y
        change (if _ then if _ then _ else _ else _) = (if _ then _ else _)
        rw [if_pos hk,if_pos rfl,if_pos hk]
        congr 1
        exact (timed_matrix_diagonal _ _ _ (completeEnd N ops z).property.forest hm x).symm
      · have hc := hcert x y
        have hp : chronologicalPath N ops (observeCompleted N
            (fun d => joinedProjection N keep (.inl d)) ops (initialCode N sample register) z) =
            fun t => joinedProjection N keep (.inl
              (recordPath N ops (initialCode N sample register) z.2.1 z.2.2.2 t)) := by
          funext t
          have h := record_path_is_chronological N (fun d => joinedProjection N keep (.inl d))
            ops (initialCode N sample register) z.2.1 z.2.2.2 t
          simpa only [observeCompleted,completePath,hc.1] using h
        change (if _ then if _ then _ else _ else _) = (if _ then _ else _)
        rw [if_pos hk,if_neg he,if_pos hk,hp]
        exact actual_complete_matrix_selected_age N register ops (firstOriginalDate N C)
          (fun x _ => C.age (N.leaf (sample x))) z keep hk.1 hk.2 he hc
    · change (if _ then _ else _) = (if _ then _ else _)
      rw [if_neg hk,if_neg hk]

/-- Original physical calendar: the faithful output identity holds with full
mass under the actual source clock/routing law, with no extra path premise. -/
theorem actual_original_faithful_output (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy) :
    ∀ᵐ z ∂completeCalendarTraceLaw N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register),
      timedObservation N C sample keep (chronologicalPath N (compiledCalendarProgram N C H gamma common)
        (observeCompleted N (fun d => joinedProjection N keep (.inl d))
          (compiledCalendarProgram N C H gamma common) (initialCode N sample register) z)) =
        matrixObservation N keep (completeEnd N (compiledCalendarProgram N C H gamma common) z)
          (completeMatrix N (compiledCalendarProgram N C H gamma common) (initialCode N sample register)
            (firstOriginalDate N C) (fun x _ => C.age (N.leaf (sample x))) z) := by
  let ops := compiledCalendarProgram N C H gamma common
  let s := initialCode N sample register
  have hroot : ∀ d, sourceProgram N r ops s d ≠ 0 → UnifiedLean.Source.SourceAncestralCompletion.AncestralRoot N d := by
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
  filter_upwards [hcert,actual_terminal_readout N r ops s (fun d => joinedProjection N keep (.inl d)),
    actual_original_complete_timed_support N C sample register H gamma common r] with z hz ht hm
  exact actual_timed_output_identity N C sample register ops keep z hz ht hm

#print axioms actual_original_faithful_output
#print axioms actual_timed_output_identity
end GProgram.G2.FaithfulTimedOutput
