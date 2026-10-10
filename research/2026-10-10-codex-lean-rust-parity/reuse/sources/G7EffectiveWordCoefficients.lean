import G7EffectiveNodeCoefficients
import G7SelectedEpochTableUniqueness
import G7SparseWordComposition

/-!
# Concrete sparse original-word and once-drawn natural coefficients

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Instantiates the generic word recurrence with the actual complete epoch,
original exit and original-node rows. Every per-step inherited coefficient
identity is supplied by a named provider, including chosen-table independence.
The same original IDs and symbolic bank serve all letters; repeated slots share
coordinates. Natural initialization draws the complete original register once.
No generated-calendar admission, native dictionary refinement or effective
policy/QE endpoint is inferred. Draft pending sole-scheduler kernel/audit.
-/
namespace GProgram.G7.EffectiveWordCoefficients
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.PopulationSelectedSupport
open GProgram.G7.FullEpochSupport GProgram.G7.SelectedEpochTableUniqueness
open GProgram.G7.EffectiveBoundaryCoefficients GProgram.G7.EffectiveNodeCoefficients
open GProgram.G7.EffectiveInitializationCoefficients GProgram.G7.SparseWordComposition
open GProgram.G7.SymbolicProgramPolynomial
open scoped BigOperators NNReal

def renameSparse {I J : Type*} (f : I → J) (p : Sparse I) : Sparse J :=
  p.map (fun z => (z.1.map (fun a => (f a.1,a.2)),z.2))

lemma polynomial_renameSparse {I J : Type*} (f : I → J) (p : Sparse I) :
    polynomial (renameSparse f p) = MvPolynomial.rename f (polynomial p) := by
  simp only [renameSparse,polynomial,List.map_map,Function.comp_def,map_list_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro z _
  rw [map_mul,MvPolynomial.rename_C,map_list_prod]
  congr 1
  simp only [List.map_map,Function.comp_def,map_pow,MvPolynomial.rename_X]

def renameRows {I J A : Type*} (f : I → J) (rows : Rows I A) : Rows J A :=
  rows.map (fun a => (a.1,renameSparse f a.2))

lemma polynomial_read_renameRows {I J A K : Type*} [DecidableEq K]
    (f : I → J) (key : A → K) (rows : Rows I A) (target : K) :
    polynomial (readRows key (renameRows f rows) target) =
      MvPolynomial.rename f (polynomial (readRows key rows target)) := by
  rw [renameRows,readRows_map,polynomial_flatMap,polynomial_readRows,map_list_sum]
  simp only [List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  by_cases h : key a.1 = target
  · rw [if_pos h,if_pos h,polynomial_renameSparse]
  · rw [if_neg h,if_neg h]
    simp [polynomial]

variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def stepRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) :
    Symbol J V E → Code N sample → Rows (WordVariable N J) (Code N sample)
  | .interval j,s => renameRows (fun i => Sum.inl (j,i)) (epochRows N s)
  | .exit e,s => exitRows N s e
  | .enter v,s => renameRows Sum.inr (nodeRows N H common v s)

/-- Concrete discharge of the generic word theorem's exact step premise.
This is an entire coefficient identity at every literal admitted input. -/
theorem polynomial_stepRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (op : Symbol J V E)
    (s : Code N sample) (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (stepRows N H common op s) b) =
      stepPolynomial N H common op (project N Finset.univ s) b := by
  cases op with
  | interval j =>
      rw [stepRows,polynomial_read_renameRows,polynomial_epochRows_eq_epochTable,
        stepPolynomial]
  | exit e => exact polynomial_exitRows_eq_exitTable N s e b
  | enter v =>
      rw [stepRows,polynomial_read_renameRows,polynomial_nodeRows_eq_nodeTable,
        stepPolynomial]

def wordRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (s : Code N sample) :
    Rows (WordVariable N J) (Code N sample) :=
  followRows (stepRows N H common) word s

theorem polynomial_wordRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (wordRows N H common word s) b) =
      wordPolynomial N H common word (project N Finset.univ s) b :=
  polynomial_original_word N H common (stepRows N H common)
    (polynomial_stepRows N H common) word s b

theorem wordRows_actual (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (word : List (Symbol J V E)) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) (wordRows N H common word s) b)
        (wordVariables N r gamma dur) =
      (((sourceProgram N r (word.map (instantiateGamma N H gamma common dur)) s).map
        (projection N Finset.univ)) b).toReal := by
  rw [← eval_polynomial,polynomial_wordRows,project_eq]
  exact actual_source_word_polynomial N H common word s b r gamma dur

def naturalWordRows (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) : Rows (WordVariable N J) (Code N sample) :=
  bindRows (initialRows N sample Sum.inr) (wordRows N H common word)

/-- Complete natural coefficient identity: one entire original register draw,
then the concrete literal sparse word, with no arbitrary step premise. -/
theorem polynomial_naturalWordRows (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (word : List (Symbol J V E)) (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (naturalWordRows N sample H common word) b) =
      naturalWordPolynomial N sample H common word b := by
  rw [naturalWordRows,polynomial_read_bindRows]
  simp_rw [polynomial_wordRows]
  rw [sum_partition (initialRows N sample (Sum.inr : Hybrid N → WordVariable N J))
    (fun a => project N Finset.univ a.1) (fun a => polynomial a.2)
    (fun a => wordPolynomial N H common word a b),naturalWordPolynomial]
  apply Finset.sum_congr rfl
  intro a _
  rw [← polynomial_readRows,polynomial_initialRows]

theorem naturalWordRows_actual (N : RootedBinary V E X) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (p : HybridProbabilities N) (dur : J → ℝ≥0)
    (word : List (Symbol J V E)) (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) (naturalWordRows N sample H common word) b)
        (wordVariables N r (originalGamma p) dur) =
      (((initializedWordLaw N sample H p common r dur word).map
        (projection N Finset.univ)) b).toReal := by
  rw [← eval_polynomial,polynomial_naturalWordRows]
  exact actual_natural_word_polynomial N sample H p common r dur word b

#print axioms polynomial_renameSparse
#print axioms polynomial_read_renameRows
#print axioms polynomial_stepRows
#print axioms polynomial_wordRows
#print axioms wordRows_actual
#print axioms polynomial_naturalWordRows
#print axioms naturalWordRows_actual
end GProgram.G7.EffectiveWordCoefficients
