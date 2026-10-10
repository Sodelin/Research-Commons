import G7EffectiveWordCoefficients
import G7EffectiveAncestralCompletion
import G7CompletedCalendarPolynomial

/-!
# Exact finite support composition with actual ancestral completion

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Every literal finite endpoint passed to completion must have full ancestral-root
support. Nonempty Copy and one positive original rate bank remain explicit.
The accepted genuine infinite-time rational completion identity is reused before
the finite literal fibre product is partitioned. No zero-survival substitution
of an arbitrary chosen epoch table, generated-calendar support or universal
native dictionary refinement is asserted. Draft pending sole-scheduler audit.
-/
namespace GProgram.G7.EffectiveCompletedWordCoefficients
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.PopulationSelectedSupport
open GProgram.G7.SparseRowProducts GProgram.G7.SparseWordComposition
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.EffectiveAncestralCompletion
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.SelectedCompletionPolynomial
open GProgram.G7.CompletedCalendarPolynomial
open scoped BigOperators NNReal

variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def completedRows {I : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (rows : Rows I (Code N sample)) : Rows I (Code N sample) :=
  bindRows rows (completionRows N)

variable [Nonempty Copy]

/-- Entire rational coefficient identity on a finite literal endpoint support.
All endpoints, including zero-weight raw rows, must satisfy the stated location
condition. Deriving this condition for generated calendars is a separate task. -/
theorem polynomial_completedRows {I : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (rows : Rows I (Code N sample))
    (hroot : ∀ row ∈ rows, AncestralRoot N row.1)
    (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (completedRows N rows) b) =
      ∑ a : SelectedIndex N sample Finset.univ,
        polynomial (readRows (project N Finset.univ) rows a) *
          MvPolynomial.C (completionRational N a b) := by
  rw [completedRows,polynomial_read_bindRows]
  have hmap :
      (rows.map fun row => polynomial row.2 *
        polynomial (readRows (project N Finset.univ) (completionRows N row.1) b)) =
      (rows.map fun row => polynomial row.2 *
        MvPolynomial.C (completionRational N (project N Finset.univ row.1) b)) := by
    apply List.map_congr_left
    intro row hrow
    rw [polynomial_completionRows,
      readRational_eq_completionRational N row.1 (hroot row hrow) b r]
  rw [hmap,sum_partition rows (fun row => project N Finset.univ row.1)
    (fun row => polynomial row.2) (fun a => MvPolynomial.C (completionRational N a b))]
  apply Finset.sum_congr rfl
  intro a _
  rw [← polynomial_readRows]

def completedWordRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (s : Code N sample) :
    Rows (WordVariable N J) (Code N sample) :=
  completedRows N (wordRows N H common word s)

theorem polynomial_completedWordRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (s : Code N sample)
    (hroot : ∀ row ∈ wordRows N H common word s, AncestralRoot N row.1)
    (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (completedWordRows N H common word s) b) =
      completedPolynomial N (wordPolynomial N H common word (project N Finset.univ s)) b := by
  rw [completedWordRows,polynomial_completedRows N _ hroot r,completedPolynomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [polynomial_wordRows]

def completedNaturalWordRows (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) : Rows (WordVariable N J) (Code N sample) :=
  completedRows N (naturalWordRows N sample H common word)

theorem polynomial_completedNaturalWordRows (N : RootedBinary V E X)
    (sample : Copy → X) (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E))
    (hroot : ∀ row ∈ naturalWordRows N sample H common word, AncestralRoot N row.1)
    (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ)
      (completedNaturalWordRows N sample H common word) b) =
      completedPolynomial N (naturalWordPolynomial N sample H common word) b := by
  rw [completedNaturalWordRows,polynomial_completedRows N _ hroot r,completedPolynomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [polynomial_naturalWordRows]

#print axioms polynomial_completedRows
#print axioms polynomial_completedWordRows
#print axioms polynomial_completedNaturalWordRows
end GProgram.G7.EffectiveCompletedWordCoefficients
