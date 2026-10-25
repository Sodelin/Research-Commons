import G2ChronologicalPruning

/-!
Initial singleton ancestry and the actual source matrix/selected-path age identity.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.SourcePairMatrixReadout
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G2.ActualPairCoalescence GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.WholeMatrixAges GProgram.G2.AncestralAgeCertificate
open GProgram.G2.CalendarFirstAge GProgram.G2.RationalAgeReadout
open GProgram.G2.JointTimedObservation GProgram.G2.CompleteDecoration
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.CalendarHistoryBinding.joinedMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

lemma initial_pair_iff (N : RootedBinary V E X) (sample : Copy → X)
    (reg : V → Bool) (keep : Finset Copy) {x y : Copy} (hx : x ∈ keep) (hy : y ∈ keep) :
    sameBlock (selectedView (state (initialCode N sample reg)) keep) x y ↔ x = y := by
  have h := decode_encode_selectedView N.root (initial N sample reg)
    (initial_valid N sample reg) keep
  change sameBlock (selectedView (decodeSnapshot N.root
    (encodeSnapshot (initial N sample reg) (initial_valid N sample reg))) keep) x y ↔ _
  rw [h,selected_same_block _ (initial_valid N sample reg) keep hx hy]
  rfl

lemma selected_pair_is_full (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) {x y : Copy} (hx : x ∈ keep) (hy : y ∈ keep) :
    sameBlock (joinedProjection N keep (.inl s)).val x y ↔
      sameBlock (selectedView (state s) Finset.univ) x y := by
  change sameBlock (selectedView (state s) keep) x y ↔ _
  exact (selected_same_block (state s) s.property.forest keep hx hy).trans
    (selected_same_block (state s) s.property.forest Finset.univ (Finset.mem_univ x) (Finset.mem_univ y)).symm

lemma rational_selected_pair (N : RootedBinary V E X) {sample : Copy → X}
    (path : ℝ≥0 → Code N sample) (keep : Finset Copy) {x y : Copy} (hx : x ∈ keep) (hy : y ∈ keep) :
    rationalAge (fun q : JoinedIndex N sample keep => sameBlock q.val x y)
      (fun t => joinedProjection N keep (.inl (path t))) =
    rationalAge (fun d => sameBlock (selectedView (state d) Finset.univ) x y) path := by
  unfold rationalAge
  congr 1
  funext q
  simp only [selected_pair_is_full N (path (Real.toNNReal (q : ℝ))) keep hx hy]

/-- Every retained off-diagonal entry of the actual complete graft matrix is
exactly the finite absolute age read from the same selected source path. -/
theorem actual_complete_matrix_selected_age (N : RootedBinary V E X)
    {sample : Copy → X} (reg : V → Bool) (ops : List (ProgramStep N))
    (offset : ℝ) (M : Copy → Copy → ℝ) (z : CompleteCalendarRecord N sample ops)
    (keep : Finset Copy) {x y : Copy} (hx : x ∈ keep) (hy : y ∈ keep) (hne : x ≠ y)
    (hz : CompleteAgeCertificate N
      (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops (initialCode N sample reg) z) :
    finiteAbsoluteAge offset
      (rationalAge (fun q : JoinedIndex N sample keep => sameBlock q.val x y)
        (fun t => joinedProjection N keep (.inl
          (recordPath N ops (initialCode N sample reg) z.2.1 z.2.2.2 t)))) =
      (true,completeMatrix N ops (initialCode N sample reg) offset M z x y) := by
  have hs : ¬ sameBlock (selectedView (state (initialCode N sample reg)) Finset.univ) x y :=
    fun h => hne ((initial_pair_iff N sample reg Finset.univ (Finset.mem_univ x) (Finset.mem_univ y)).mp h)
  obtain ⟨a,ha,hm,hr⟩ := complete_matrix_first_age N ops (initialCode N sample reg) offset M z x y hz hs
  rw [rational_selected_pair N _ keep hx hy,hr]
  simp only [finiteAbsoluteAge,ENNReal.ofReal_ne_top,if_false,ENNReal.toReal_ofReal ha,hm]

#print axioms initial_pair_iff
#print axioms actual_complete_matrix_selected_age
end GProgram.G2.SourcePairMatrixReadout
