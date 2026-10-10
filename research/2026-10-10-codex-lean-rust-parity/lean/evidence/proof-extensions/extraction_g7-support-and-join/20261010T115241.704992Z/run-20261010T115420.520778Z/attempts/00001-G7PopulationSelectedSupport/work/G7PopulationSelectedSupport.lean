import G7EffectiveFullEpochCoefficients
import G7EffectiveCoefficientSupport
import Mathlib.Data.List.Dedup

/-!
# Exact polynomial extraction on literal original merger support

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Uses the unchanged inherited populationSelected, coefficients and polynomial
definitions. The accepted generic outside-support proof permits a finite
deduplicated merger list in place of full Code enumeration. List order and raw
zero/duplicate monomials need not agree; the resulting rational polynomial does.
This is a new proof draft pending independent kernel checking.
-/

universe uC
namespace GProgram.G7.PopulationSelectedSupport
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.EffectiveCoefficientSupport
open scoped BigOperators NNReal

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [FinEnum V] [FinEnum E]
variable {Copy : Type uC} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

/-- No full Code carrier is enumerated by this executable readout. -/
def populationSelectedSupport (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (a : SelectedIndex N sample Finset.univ) :
    Sparse (Option E) :=
  (destinations N (Fintype.card Copy) s).dedup.flatMap fun d =>
    if project N Finset.univ d = a then
      embedExpr i (coefficients N (Fintype.card Copy) s d) else []

lemma polynomial_append {I : Type*} (a b : Sparse I) :
    polynomial (a ++ b) = polynomial a + polynomial b := by
  simp only [polynomial,List.map_append,List.sum_append]

lemma polynomial_flatMap {A I : Type*} (l : List A) (f : A → Sparse I) :
    polynomial (l.flatMap f) = (l.map fun a => polynomial (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons,polynomial_append,List.map_cons,List.sum_cons,ih]

lemma polynomial_enumerate {A I : Type*} [Fintype A] [FinEnum A]
    (f : A → Sparse I) :
    polynomial ((FinEnum.toList A).flatMap f) = ∑ a : A, polynomial (f a) := by
  rw [polynomial_flatMap]
  rw [((enumeration_perm A).map (fun a => polynomial (f a))).sum_eq]
  exact Finset.sum_map_toList _ _

lemma polynomial_embedExpr_zero {I : Type*} (i : I) (p : Expr)
    (hp : ∀ z ∈ p, z.2 = 0) : polynomial (embedExpr i p) = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
    have hz : z.2 = 0 := hp z (by simp)
    have ht : ∀ w ∈ p, w.2 = 0 := fun w hw => hp w (by simp [hw])
    change MvPolynomial.C z.2 * (MvPolynomial.X i ^ z.1 * 1) +
      polynomial (embedExpr i p) = 0
    rw [hz,MvPolynomial.C_0,zero_mul,zero_add]
    exact ih ht

/-- Equality of the entire rational polynomial, not merely physical evaluations
at a selected rate bank or a finite collection of test points. -/
theorem polynomial_populationSelectedSupport (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (populationSelectedSupport N s i a) =
      polynomial (populationSelected N s i a) := by
  classical
  rw [populationSelectedSupport,polynomial_flatMap,populationSelected,polynomial_enumerate]
  rw [← List.sum_toFinset
    (fun d : Code N sample => polynomial (if project N Finset.univ d = a then
      embedExpr i (coefficients N (Fintype.card Copy) s d) else []))
    (List.nodup_dedup (destinations N (Fintype.card Copy) s))]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  have hnot : d ∉ destinations N (Fintype.card Copy) s := by
    simpa only [List.mem_toFinset,List.mem_dedup] using hd
  by_cases h : project N Finset.univ d = a
  · rw [if_pos h]
    exact polynomial_embedExpr_zero i _
      (coefficients_zero_of_not_mem N (Fintype.card Copy) s d hnot)
  · rw [if_neg h]
    rfl

theorem value_populationSelectedSupport (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E)
    (a : SelectedIndex N sample Finset.univ) (x : Option E → ℝ) :
    value (populationSelectedSupport N s i a) x =
      value (populationSelected N s i a) x := by
  have h := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) x)
    (polynomial_populationSelectedSupport N s i a)
  rw [eval_polynomial,eval_polynomial] at h
  exact h

theorem populationSelectedSupport_actual (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (t : ℝ≥0) :
    value (populationSelectedSupport N s i a) (survival r t) =
      (((sourceTimeKernel N r t s).map (projection N Finset.univ)) a).toReal := by
  rw [value_populationSelectedSupport]
  exact populationSelected_actual N s i hs a r t

#print axioms polynomial_populationSelectedSupport
#print axioms populationSelectedSupport_actual
end GProgram.G7.PopulationSelectedSupport
