import G1OriginalExitBatchBinding
import G1CanonicalThreeEpochList

/-! Composition of actual selected-state source rows. Contributor: dot,
2026-10-03. Full genealogy/population/register rows, not scalar observations. -/
namespace G1CompactSourceComposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceBoundaryProjection UnifiedLean.Source.SourceFiniteProjection
open G1ActualJointProgram
open G1SameOriginalExteriorContinuation
open UnifiedLean.Source.SourceForestSilentPruning
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

lemma actual_projected_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (xs ys : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r (xs ++ ys) s).map (projection N keep) =
      ((sourceProgram N r xs s).map (projection N keep)).bind (selectedProgram N r keep ys) := by
  rw [actual_source_program_append,PMF.map_bind,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro d _
  exact actual_source_program_projection N r keep ys d

/-- A derived full selected-state row identity remains valid under the SAME
actual original suffix, including arbitrary later panel interaction. -/
theorem actual_source_row_suffix_congr (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (xs ys tail : List (ProgramStep N))
    (s : Code N sample)
    (h : (sourceProgram N r xs s).map (projection N keep) =
      (sourceProgram N r ys s).map (projection N keep)) :
    (sourceProgram N r (xs ++ tail) s).map (projection N keep) =
      (sourceProgram N r (ys ++ tail) s).map (projection N keep) := by
  rw [actual_projected_append,actual_projected_append,h]

/-- Replace a block on its REAL actual pre support. The theorem supplies
only composition algebra; actual block identities are proved separately. -/
theorem actual_source_supported_block_congr (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (pre xs ys tail : List (ProgramStep N))
    (s : Code N sample)
    (h : ∀ d ∈ (sourceProgram N r pre s).support,
      (sourceProgram N r xs d).map (projection N keep) =
      (sourceProgram N r ys d).map (projection N keep)) :
    (sourceProgram N r (pre ++ xs ++ tail) s).map (projection N keep) =
      (sourceProgram N r (pre ++ ys ++ tail) s).map (projection N keep) := by
  rw [List.append_assoc,List.append_assoc,actual_source_program_append,actual_source_program_append,PMF.map_bind,PMF.map_bind]
  apply bind_eq_of_eq_on_support
  intro d hd
  exact actual_source_row_suffix_congr N r keep xs ys tail d (h d hd)

lemma actual_projected_support_transfer (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (p q : PMF (Code N sample))
    (h : p.map (projection N keep) = q.map (projection N keep))
    {d : Code N sample} (hd : d ∈ p.support) :
    ∃ z ∈ q.support, projection N keep z = projection N keep d := by
  have hm : projection N keep d ∈ (p.map (projection N keep)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨d,hd,rfl⟩
  rw [h] at hm
  exact (PMF.mem_support_map_iff _ _ _).mp hm

lemma actual_projected_copy_location (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s z : Code N sample)
    (h : projection N keep s = projection N keep z) (x : Copy) (hx : x ∈ keep) :
    copyLocation (state s) x = copyLocation (state z) x := by
  have he := congrArg (fun v => v.val.population x) h
  simpa [projection,selectedView,selectedLocation,hx] using he

end G1CompactSourceComposition
