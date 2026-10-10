import G7EffectivePopulationCoefficients

/-!
# Literal merger support of the inherited executable coefficients

Contributor: Codex / lean_reuse_successor, 10 October 2026.
The search carrier uses the original Choice and merger, without enumerating all
Code states. The proof has arbitrary fuel and copy cardinality; no quotient,
resource bound, or Rust implementation theorem is asserted.
-/
namespace GProgram.G7.EffectiveCoefficientSupport

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open scoped NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Reflexive merger closure with precisely the executable coefficient fuel. -/
def destinations (N : RootedBinary V E X) {sample : Copy → X} :
    Nat → Code N sample → List (Code N sample)
  | 0, s => [s]
  | fuel + 1, s =>
      if s.val.live.card ≤ 1 then [s]
      else s :: (FinEnum.toList (Choice N s)).flatMap
        (fun p => destinations N fuel (merger N s p))

lemma liftExpr_zero_coefficients (n : Nat) (p : Expr)
    (hp : ∀ z ∈ p, z.2 = 0) :
    ∀ z ∈ liftExpr n p, z.2 = 0 := by
  intro z hz
  rcases List.mem_flatMap.mp hz with ⟨w, hw, hz⟩
  have hw0 := hp w hw
  have hz0 : z = (w.1, 0) ∨ z = (n, 0) := by
    simpa [liftTerm, hw0] using hz
  rcases hz0 with rfl | rfl <;> rfl

/-- Outside literal fuel-bounded merger support, every raw term vanishes. -/
theorem coefficients_zero_of_not_mem (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s d : Code N sample)
    (hd : d ∉ destinations N fuel s) :
    ∀ z ∈ coefficients N fuel s d, z.2 = 0 := by
  induction fuel generalizing s with
  | zero =>
      have hsd : s ≠ d := by
        intro h
        apply hd
        simp [destinations, h]
      intro z hz
      have hz0 : z = (0, 0) := by simpa [coefficients, hsd] using hz
      subst z
      rfl
  | succ fuel ih =>
      by_cases hk : s.val.live.card ≤ 1
      · have hsd : s ≠ d := by
          intro h
          apply hd
          simp [destinations, hk, h]
        intro z hz
        have hz0 : z = (0, 0) := by simpa [coefficients, hk, hsd] using hz
        subst z
        rfl
      · have hsd : s ≠ d := by
          intro h
          apply hd
          simp [destinations, hk, h]
        have hchildren (p : Choice N s) (hp : p ∈ FinEnum.toList (Choice N s)) :
            d ∉ destinations N fuel (merger N s p) := by
          intro hm
          apply hd
          simp only [destinations, if_neg hk, List.mem_cons, List.mem_flatMap]
          exact Or.inr ⟨p, hp, hm⟩
        intro z hz
        simp only [coefficients, if_neg hk, List.mem_append] at hz
        rcases hz with hz | hz
        · have hz0 : z = (s.val.live.card.choose 2, 0) := by
            simpa [hsd] using hz
          subst z
          rfl
        · rcases List.mem_flatMap.mp hz with ⟨p, hp, hz⟩
          exact liftExpr_zero_coefficients _ _
            (ih (merger N s p) (hchildren p hp)) z hz

lemma exprPolynomial_zero_of_zero_coefficients (p : Expr)
    (hp : ∀ z ∈ p, z.2 = 0) : exprPolynomial p = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      have hz : z.2 = 0 := hp z (by simp)
      have ht : ∀ w ∈ p, w.2 = 0 := fun w hw => hp w (by simp [hw])
      rw [exprPolynomial_cons, hz, Polynomial.C_0, zero_mul, zero_add]
      exact ih ht

theorem coefficients_polynomial_zero_of_not_mem (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : Nat) (s d : Code N sample)
    (hd : d ∉ destinations N fuel s) :
    exprPolynomial (coefficients N fuel s d) = 0 :=
  exprPolynomial_zero_of_zero_coefficients _
    (coefficients_zero_of_not_mem N fuel s d hd)

/-- In one actual co-located population, the support restriction is semantic. -/
theorem actual_population_zero_of_not_mem (N : RootedBinary V E X)
    {sample : Copy → X} (s d : Code N sample) (i : Option E)
    (hs : CoLocated N s i)
    (hd : d ∉ destinations N (Fintype.card Copy) s)
    (r : PositivePairRates E) (t : ℝ≥0) :
    (sourceTimeKernel N r t s d).toReal = 0 := by
  rw [← actual_population_coefficients N s d i hs r t]
  rw [coefficients_polynomial_zero_of_not_mem N _ s d hd]
  simp

end GProgram.G7.EffectiveCoefficientSupport
