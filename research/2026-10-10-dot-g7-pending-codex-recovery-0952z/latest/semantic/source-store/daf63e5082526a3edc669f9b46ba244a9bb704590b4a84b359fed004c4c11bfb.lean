import G7EffectiveSourceEnumeration
import G7SinglePopulationPolynomialKernel
import Mathlib.Data.List.Perm.Basic

/-! Executable exact rational coefficient lists for the actual original-source
single-population kernel. Contributor: dot, 2026-10-10. FinEnum replaces the
noncomputable Finset.toList ordering; source mergers and their snapshot
encoding remain literal. Permutation equivalence binds the executable list to
the already checked analytic recurrence for all positive rates and t >= 0.
-/
namespace GProgram.G7.EffectivePopulationCoefficients
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration
open scoped NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def sourceState {N : RootedBinary V E X} {sample : Copy → X}
    (s : Code N sample) : State V E Copy := decode N.root s.val

def place (N : RootedBinary V E X) : Option E → Location V E
  | none => .rootPopulation N.root
  | some e => .edge e

def encode (s : State V E Copy) (hs : Valid s) : Snapshot V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := if h : l ∈ s.live then some ⟨s.genealogy l,hs.wellLabelled l h⟩ else none
  population l := if l ∈ s.live then some (s.location l) else none
  register := s.register

def encodeActual (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) : Code N sample :=
  ⟨encode s hs.forest,decode_encode_sourceValid N sample s hs⟩

instance choiceEnumeration (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : FinEnum (Choice N s) := by
  change FinEnum (Σ i : Option E,
    {p : Copy × Copy // p ∈ (populationRoots (sourceState s) (place N i)).offDiag})
  infer_instance

def merger (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : Code N sample :=
  encodeActual N sample (merge (sourceState s) p.2.val.1 p.2.val.2)
    (merge_source_valid N sample (state s) s.property
      (population_pair_is_source_legal (state s) (originalPlace N p.1)
        (originalPlace_not_node N p.1) p.2.property))

theorem merger_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    merger N s p = stepDestination N s (some p) := rfl

/-- Finite, rational arithmetic only. The copy cap supplies the fuel below. -/
def coefficients (N : RootedBinary V E X) {sample : Copy → X} :
    ℕ → Code N sample → Code N sample → Expr
  | 0,s,d => [(0,if s=d then 1 else 0)]
  | fuel+1,s,d =>
      if s.val.live.card ≤ 1 then [(0,if s=d then 1 else 0)]
      else [(s.val.live.card.choose 2,if s=d then 1 else 0)] ++
        (FinEnum.toList (Choice N s)).flatMap (fun p =>
          liftExpr (s.val.live.card.choose 2) (coefficients N fuel (merger N s p) d))

lemma enumeration_perm (A : Type*) [Fintype A] [FinEnum A] :
    (FinEnum.toList A).Perm (Finset.univ.toList : List A) := by
  apply (List.perm_ext_iff_of_nodup (FinEnum.nodup_toList A)
    (Finset.nodup_toList _)).mpr
  intro a
  simp

/-- Reordering the complete legal-pair list only reorders monomial terms. -/
theorem coefficients_perm_kernelExpr (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : ℕ) (s d : Code N sample) :
    (coefficients N fuel s d).Perm (kernelExpr N fuel s d) := by
  classical
  induction fuel generalizing s with
  | zero => simp [coefficients,kernelExpr]
  | succ fuel ih =>
      by_cases h : s.val.live.card ≤ 1
      · simp [coefficients,kernelExpr,liveCard,h]
      · simp only [coefficients,kernelExpr,liveCard,if_neg h]
        apply List.Perm.append (List.Perm.refl _)
        apply (enumeration_perm (Choice N s)).flatMap
        intro p _
        exact (ih (merger N s p)).flatMap_right (liftTerm (s.val.live.card.choose 2))

/-- The executable coefficient list denotes exactly the already verified
actual source polynomial, without selecting an existential polynomial. -/
theorem coefficients_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    exprPolynomial (coefficients N (Fintype.card Copy) s d) = populationPolynomial N s d := by
  unfold exprPolynomial populationPolynomial
  exact ((coefficients_perm_kernelExpr N _ s d).map _).sum_eq

theorem actual_population_coefficients (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r i * (t:ℝ)))
      (exprPolynomial (coefficients N (Fintype.card Copy) s d)) =
      (sourceTimeKernel N r t s d).toReal := by
  rw [coefficients_polynomial]
  exact actual_population_polynomial N s d i hs r t

end GProgram.G7.EffectivePopulationCoefficients
