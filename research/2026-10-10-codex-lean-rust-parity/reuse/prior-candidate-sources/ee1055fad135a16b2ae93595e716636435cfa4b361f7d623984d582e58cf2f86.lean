import G7SparseRowProducts
import G7SymbolicProgramPolynomial

/-!
# Finite literal-row composition for a fixed original word

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The executable recurrence visits only complete supplied conditional supports,
retaining one literal Code per raw branch and the same symbolic variable bank.
Coefficient refinement and physical-law refinement are distinct theorems.
The former requires an exact per-step polynomial identity; physical evaluation
alone is not used to identify the inherited Classical.choose epoch table.
The actual source projection is reused unchanged, not assumed or reproved.
Draft pending sole-scheduler kernel checking and complete audit.
-/
namespace GProgram.G7.SparseWordComposition
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.SymbolicProgramPolynomial
open scoped BigOperators NNReal

def bindRows {I A B : Type*} (rows : Rows I A) (next : A → Rows I B) : Rows I B :=
  rows.flatMap fun a => (next a.1).map fun b => (b.1,product a.2 b.2)

/-- Every literal entering/destination branch contributes its entire product.
Equal endpoint keys are summed before any representative is discarded. -/
theorem polynomial_read_bindRows {I A B K : Type*} [DecidableEq K]
    (key : B → K) (rows : Rows I A) (next : A → Rows I B) (target : K) :
    polynomial (readRows key (bindRows rows next) target) =
      (rows.map fun a => polynomial a.2 *
        polynomial (readRows key (next a.1) target)).sum := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
      change polynomial (readRows key
        (((next a.1).map fun b => (b.1,product a.2 b.2)) ++ bindRows rows next) target) = _
      rw [readRows_append,polynomial_append,ih]
      simp only [List.map_cons,List.sum_cons]
      congr 1
      rw [readRows_map,polynomial_flatMap,polynomial_readRows,← list_mul_sum]
      apply congrArg List.sum
      apply List.map_congr_left
      intro b _
      by_cases h : key b.1 = target
      · rw [if_pos h,if_pos h,polynomial_product]
      · rw [if_neg h,if_neg h]
        simp [polynomial]

lemma value_readRows {I A K : Type*} [DecidableEq K]
    (key : A → K) (rows : Rows I A) (target : K) (x : I → ℝ) :
    value (readRows key rows target) x =
      (rows.map fun a => if key a.1 = target then value a.2 x else 0).sum := by
  rw [readRows,value_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  by_cases h : key a.1 = target <;> simp only [if_pos h,if_neg h,value_nil]

theorem value_read_bindRows {I A B K : Type*} [DecidableEq K]
    (key : B → K) (rows : Rows I A) (next : A → Rows I B)
    (target : K) (x : I → ℝ) :
    value (readRows key (bindRows rows next) target) x =
      (rows.map fun a => value a.2 x * value (readRows key (next a.1) target) x).sum := by
  have h := congrArg (MvPolynomial.eval₂Hom (Rat.castHom ℝ) x)
    (polynomial_read_bindRows key rows next target)
  rw [eval_polynomial,map_list_sum] at h
  simp only [List.map_map,Function.comp_def,MvPolynomial.eval₂_mul,eval_polynomial] at h
  exact h

def followRows {I A Op : Type*} (step : Op → A → Rows I A) : List Op → A → Rows I A
  | [],a => [(a,single 1)]
  | op::ops,a => bindRows (step op a) (followRows step ops)

noncomputable def tableWord {I K Op : Type*} [Fintype K] [DecidableEq K]
    (step : Op → K → K → MvPolynomial I ℚ) :
    List Op → K → K → MvPolynomial I ℚ
  | [],a,b => if a=b then 1 else 0
  | op::ops,a,b => ∑ c : K, step op a c * tableWord step ops c b

/-- Exact symbolic word identity. The premise is coefficient equality at each
step, and is stronger than equality on a physically constrained word bank.
No entire finite-state carrier is enumerated in followRows. -/
theorem polynomial_followRows {I A K Op : Type*} [Fintype K] [DecidableEq K]
    (key : A → K) (step : Op → A → Rows I A)
    (table : Op → K → K → MvPolynomial I ℚ)
    (hstep : ∀ op a b, polynomial (readRows key (step op a) b) = table op (key a) b)
    (ops : List Op) (a : A) (b : K) :
    polynomial (readRows key (followRows step ops a) b) = tableWord table ops (key a) b := by
  induction ops generalizing a with
  | nil =>
      by_cases h : key a=b <;> simp [followRows,readRows,single,polynomial,tableWord,h]
  | cons op ops ih =>
      rw [followRows,polynomial_read_bindRows]
      simp_rw [ih]
      rw [sum_partition (step op a) (fun row => key row.1) (fun row => polynomial row.2)
        (fun c => tableWord table ops c b),tableWord]
      apply Finset.sum_congr rfl
      intro c _
      rw [← polynomial_readRows,hstep]

variable {J V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- The unchanged original wordPolynomial is obtained only after every exact
selected stepPolynomial fibre identity has been discharged. In particular,
the inherited chosen epoch-table obligation is not removed by this theorem. -/
theorem polynomial_original_word (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (step : Symbol J V E → Code N sample → Rows (WordVariable N J) (Code N sample))
    (hstep : ∀ op s b,
      polynomial (readRows (project N Finset.univ) (step op s) b) =
        stepPolynomial N H common op (project N Finset.univ s) b)
    (word : List (Symbol J V E)) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (followRows step word s) b) =
      wordPolynomial N H common word (project N Finset.univ s) b := by
  have ht : ∀ ops a,
      tableWord (stepPolynomial N H common) ops a b = wordPolynomial N H common ops a b := by
    intro ops
    induction ops with
    | nil => intro a; rfl
    | cons op ops ih =>
        intro a
        rw [tableWord,wordPolynomial]
        apply Finset.sum_congr rfl
        intro c _
        rw [ih]
  rw [polynomial_followRows (project N Finset.univ) step (stepPolynomial N H common) hstep,ht]

/-- Universal physical-law refinement of the actual finite original word.
Per-step semantics are weaker premises than the coefficient theorem above.
Positive rates, nonnegative slot durations and one original gamma/mode bank
remain shared across all letters, including repeated slot IDs. -/
theorem actual_followRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (step : Symbol J V E → Code N sample → Rows (WordVariable N J) (Code N sample))
    (hstep : ∀ op s b,
      value (readRows (project N Finset.univ) (step op s) b) (wordVariables N r gamma dur) =
        (selectedProgramStep N r Finset.univ (instantiateGamma N H gamma common dur op)
          (project N Finset.univ s) b).toReal)
    (word : List (Symbol J V E)) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) (followRows step word s) b)
        (wordVariables N r gamma dur) =
      (((sourceProgram N r (word.map (instantiateGamma N H gamma common dur)) s).map
        (projection N Finset.univ)) b).toReal := by
  have hs : ∀ ops s,
      value (readRows (project N Finset.univ) (followRows step ops s) b)
          (wordVariables N r gamma dur) =
        (selectedProgram N r Finset.univ (ops.map (instantiateGamma N H gamma common dur))
          (project N Finset.univ s) b).toReal := by
    intro ops
    induction ops with
    | nil =>
        intro s
        by_cases h : project N Finset.univ s=b
        · simp [followRows,readRows,single,value,selectedProgram,PMF.pure_apply,h]
        · simp [followRows,readRows,single,value,selectedProgram,PMF.pure_apply,h,Ne.symm h]
    | cons op ops ih =>
        intro s
        rw [followRows,value_read_bindRows]
        simp_rw [ih]
        rw [sum_partition (step op s) (fun row => project N Finset.univ row.1)
          (fun row => value row.2 (wordVariables N r gamma dur))
          (fun c => (selectedProgram N r Finset.univ
            (ops.map (instantiateGamma N H gamma common dur)) c b).toReal)]
        rw [List.map_cons,selectedProgram,bind_probability_real,tsum_fintype]
        apply Finset.sum_congr rfl
        intro c _
        rw [← value_readRows,hstep]
  rw [actual_source_program_projection,← project_eq]
  exact hs word s

/-- This conclusion deliberately says physical evaluation equality. It does
not identify arbitrary symbolic coefficients of the chosen inherited table. -/
theorem evaluated_original_word (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (step : Symbol J V E → Code N sample → Rows (WordVariable N J) (Code N sample))
    (hstep : ∀ op s b,
      value (readRows (project N Finset.univ) (step op s) b) (wordVariables N r gamma dur) =
        (selectedProgramStep N r Finset.univ (instantiateGamma N H gamma common dur op)
          (project N Finset.univ s) b).toReal)
    (word : List (Symbol J V E)) (s : Code N sample)
    (b : SelectedIndex N sample Finset.univ) :
    value (readRows (project N Finset.univ) (followRows step word s) b)
        (wordVariables N r gamma dur) =
      wordEval N r gamma dur (wordPolynomial N H common word (projection N Finset.univ s) b) := by
  rw [actual_followRows N H common r gamma dur step hstep,
    actual_source_word_polynomial]

#print axioms polynomial_read_bindRows
#print axioms polynomial_followRows
#print axioms polynomial_original_word
#print axioms actual_followRows
#print axioms evaluated_original_word
end GProgram.G7.SparseWordComposition
