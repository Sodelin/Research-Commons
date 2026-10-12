import G1OriginalActorUnrankedBoundaryFrames

/-! Concrete original source kernels on the common unranked actor carrier.
They are defined from ACTUAL source-valid quotient rows; only unreachable
non-source interface values use identity. The actual row is derived, and
composition retains the SAME original rates/register/operations. -/
namespace G1ActualOriginalUnrankedLocalKernel
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceForestSilentPruning
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualFuture
open G1ActualJointProgram
open scoped Classical
variable {V E Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def originalLocalRow (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (value : UnrankedView V E Copy) : PMF (UnrankedView V E Copy) :=
  if h : ∃ v : UnrankedIndex N sample keep, v.val = value then
    (unrankedProgram N r keep ops (Classical.choose h)).map Subtype.val
  else PMF.pure value

lemma actual_original_local_row_at_index (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (v : UnrankedIndex N sample keep) :
    originalLocalRow N sample r keep ops v.val = (unrankedProgram N r keep ops v).map Subtype.val := by
  have hw : ∃ z : UnrankedIndex N sample keep, z.val = v.val := ⟨v,rfl⟩
  have he : Classical.choose hw = v := Subtype.ext (Classical.choose_spec hw)
  rw [originalLocalRow,dif_pos hw,he]

/-- Actual complete original panel source row, from its unranked input ALONE.
No hidden implementation representative or desired kernel is an argument. -/
theorem actual_original_local_source_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (fun d => unrankedView (selectedView (state d) keep)) =
      originalLocalRow N sample r keep ops (unrankedView (selectedView (state s) keep)) := by
  change _ = originalLocalRow N sample r keep ops (unrankedProjection N keep s).val
  rw [actual_original_local_row_at_index N sample r keep ops (unrankedProjection N keep s)]
  have h := congrArg (fun p => p.map Subtype.val) (actual_unranked_source_program N r keep ops s)
  rw [PMF.map_comp] at h
  exact h

lemma unranked_program_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (first last : List (ProgramStep N)) (v : UnrankedIndex N sample keep) :
    unrankedProgram N r keep (first ++ last) v =
      (unrankedProgram N r keep first v).bind (unrankedProgram N r keep last) := by
  induction first generalizing v with
  | nil => simp [unrankedProgram,PMF.pure_bind]
  | cons op ops ih =>
      simp only [List.cons_append,unrankedProgram,PMF.bind_bind]
      congr 1
      funext z
      exact ih z

/-- The concrete local carrier extension composes on ACTUAL quotient values,
so finite private original words use these rows without a synthetic rate. -/
theorem actual_original_local_word_composition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (first last : List (ProgramStep N))
    (v : UnrankedIndex N sample keep) :
    originalLocalRow N sample r keep (first ++ last) v.val =
      (originalLocalRow N sample r keep first v.val).bind (originalLocalRow N sample r keep last) := by
  rw [actual_original_local_row_at_index,unranked_program_append,PMF.map_bind,
    actual_original_local_row_at_index,PMF.bind_map]
  congr 1
  funext z
  exact (actual_original_local_row_at_index N sample r keep last z).symm

#print axioms actual_original_local_source_row
#print axioms actual_original_local_word_composition
end G1ActualOriginalUnrankedLocalKernel
