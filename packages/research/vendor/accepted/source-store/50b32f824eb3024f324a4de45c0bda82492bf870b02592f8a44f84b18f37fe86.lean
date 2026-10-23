import G7SinglePopulationPolynomialKernel

/-!
Codex coordinator, 10 October 2026. Candidate awaiting its own kernel receipt.
Formalizes the sharper exponent-support observation in DOT's recovered G6
quantitative assembly, using the unchanged actual G7 kernelExpr recursion.

The existing degree bound alone does not imply this statement: every nonzero
monomial is at a Kingman death level choose(j,2). This is one source coefficient
ingredient for COMMON generator compression. It does not prove coefficient
norm bounds, count-conditioned forest weights, Caratheodory compression,
positive reconstruction or the full G6 master.
-/

namespace GProgram.G6.OriginalPopulationSpectralSupport

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceFiniteJumpExpansion
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.G6.AncestralRateFree
open GProgram.G7.SinglePopulationPolynomialKernel
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The original finite-merger expression only uses actual lineage-count levels,
at every fuel budget, uniformly over its full retained entering/destination codes. -/
theorem original_kernelExpr_level_support
    (N : RootedBinary V E X) {sample : Copy → X}
    (budget : ℕ) (s d : Code N sample) :
    ∀ z ∈ kernelExpr N budget s d,
      ∃ j ≤ liveCard s, z.1 = j.choose 2 := by
  induction budget generalizing s with
  | zero =>
      intro z hz
      simp only [kernelExpr, List.mem_cons, List.not_mem_nil, or_false] at hz
      subst z
      exact ⟨0, Nat.zero_le _, by simp⟩
  | succ budget ih =>
      by_cases hk : liveCard s ≤ 1
      · intro z hz
        simp only [kernelExpr, if_pos hk, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        subst z
        exact ⟨0, Nat.zero_le _, by simp⟩
      · intro z hz
        simp only [kernelExpr, if_neg hk, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · subst z
          exact ⟨liveCard s, le_rfl, rfl⟩
        · obtain ⟨p, hp, hz⟩ := List.mem_flatMap.mp hz
          obtain ⟨w, hw, hz⟩ := List.mem_flatMap.mp hz
          obtain ⟨j, hj, he⟩ := ih (stepDestination N s (some p)) w hw
          have hc := merger_destination_card N s p
          simp only [liftTerm, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with hz | hz
          · subst z
            exact ⟨j, by omega, he⟩
          · subst z
            exact ⟨liveCard s, le_rfl, rfl⟩

lemma exprPolynomial_coeff_zero_of_missing_exponent
    (p : Expr) (m : ℕ) (hm : ∀ z ∈ p, z.1 ≠ m) :
    (exprPolynomial p).coeff m = 0 := by
  induction p with
  | nil => simp
  | cons z p ih =>
      have hz : z.1 ≠ m := hm z (by simp)
      have hp : ∀ w ∈ p, w.1 ≠ m := fun w hw => hm w (by simp [hw])
      rw [exprPolynomial_cons, Polynomial.coeff_add,
        Polynomial.C_mul_X_pow_eq_monomial]
      simp [Polynomial.coeff_monomial, hz, ih hp]

/-- All other coefficients of the unchanged full population polynomial vanish. -/
theorem original_populationPolynomial_coeff_zero_of_non_level
    (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (m : ℕ)
    (hm : ∀ j ≤ liveCard s, j.choose 2 ≠ m) :
    (populationPolynomial N s d).coeff m = 0 := by
  apply exprPolynomial_coeff_zero_of_missing_exponent
  intro z hz
  obtain ⟨j, hj, he⟩ := original_kernelExpr_level_support N _ s d z hz
  rw [he]
  exact hm j hj

/-- A nonzero coefficient supplies its actual lineage-count death level. -/
theorem original_populationPolynomial_nonzero_coeff_level
    (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (m : ℕ)
    (hm : (populationPolynomial N s d).coeff m ≠ 0) :
    ∃ j ≤ liveCard s, m = j.choose 2 := by
  classical
  by_contra h
  apply hm
  apply original_populationPolynomial_coeff_zero_of_non_level N s d m
  intro j hj he
  exact h ⟨j, hj, he.symm⟩

end GProgram.G6.OriginalPopulationSpectralSupport

#print axioms GProgram.G6.OriginalPopulationSpectralSupport.original_kernelExpr_level_support
#print axioms GProgram.G6.OriginalPopulationSpectralSupport.original_populationPolynomial_coeff_zero_of_non_level
#print axioms GProgram.G6.OriginalPopulationSpectralSupport.original_populationPolynomial_nonzero_coeff_level
