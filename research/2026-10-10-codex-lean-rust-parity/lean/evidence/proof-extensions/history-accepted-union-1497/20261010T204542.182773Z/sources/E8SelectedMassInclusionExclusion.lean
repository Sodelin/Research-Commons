import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic

/-!
# Finite weighted required-pair mass by allowed-pair oracle inclusion–exclusion

Contributor: dot, 2026-10-02. This is the exact finite algebraic engine for the
selected-class endpoint-cell construction. It applies to any finite ensemble,
any finite emitted-pair map, and commutative-ring weights. Nonnegative real
weights give the usual mass interpretation. No RNA grammar/class-map fidelity,
pair-restricted executable adapter, sampler law or floating accuracy is assumed
or concluded. The inclusion–exclusion principle is classical mathematics.
-/
namespace GProgram.E8.SelectedMass
open scoped BigOperators
variable {Pair Structure K : Type*} [DecidableEq Pair] [CommRing K]

/-- Exact weighted mass allowed by a finite original pair mask. -/
def allowedMass (Ω : Finset Structure) (pairs : Structure → Finset Pair)
    (weight : Structure → K) (allowed : Finset Pair) : K :=
  ∑ r ∈ Ω, if pairs r ⊆ allowed then weight r else 0

/-- Exact weighted mass with allowed and mandatory original pairs. -/
def requiredMass (Ω : Finset Structure) (pairs : Structure → Finset Pair)
    (weight : Structure → K) (allowed required : Finset Pair) : K :=
  ∑ r ∈ Ω, if pairs r ⊆ allowed ∧ required ⊆ pairs r then weight r else 0

/-- The exact alternating coefficient is one iff every required pair is
present, and zero otherwise. -/
theorem alternating_disjoint_coefficient (present required : Finset Pair) :
    (∑ removed ∈ required.powerset,
      (-1 : K) ^ removed.card * (if Disjoint present removed then 1 else 0)) =
      if required ⊆ present then 1 else 0 := by
  classical
  have hfac : ∀ p : Pair, (1 : K) - (if p ∉ present then 1 else 0) =
      if p ∈ present then 1 else 0 := by
    intro p
    by_cases hp : p ∈ present <;> simp [hp]
  have h := Finset.prod_sub (fun _ : Pair => (1 : K))
    (fun p => if p ∉ present then (1 : K) else 0) required
  simp_rw [hfac] at h
  simpa only [Finset.prod_boole, Finset.prod_const_one, mul_one,
    ← Finset.subset_iff, ← Finset.disjoint_right] using h.symm

/-- Pointwise cancellation for an actual emitted-pair set and allowed mask. -/
theorem allowed_required_indicator (present allowed required : Finset Pair) :
    (∑ removed ∈ required.powerset,
      (-1 : K) ^ removed.card * (if present ⊆ allowed \ removed then 1 else 0)) =
      if present ⊆ allowed ∧ required ⊆ present then 1 else 0 := by
  classical
  by_cases ha : present ⊆ allowed
  · simpa only [Finset.subset_sdiff, ha, true_and] using
      alternating_disjoint_coefficient (K := K) present required
  · simp only [Finset.subset_sdiff, ha, false_and, ite_false, mul_zero,
      Finset.sum_const_zero]

/-- Exact weighted inclusion–exclusion. Required sets need not be subsets of
the allowed mask; impossible cells cancel to zero without an extra assumption. -/
theorem requiredMass_eq_inclusionExclusion (Ω : Finset Structure)
    (pairs : Structure → Finset Pair) (weight : Structure → K)
    (allowed required : Finset Pair) :
    requiredMass Ω pairs weight allowed required =
      ∑ removed ∈ required.powerset,
        (-1 : K) ^ removed.card * allowedMass Ω pairs weight (allowed \ removed) := by
  classical
  simp only [requiredMass, allowedMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (if pairs r ⊆ allowed ∧ required ⊆ pairs r then weight r else 0) =
        (if pairs r ⊆ allowed ∧ required ⊆ pairs r then (1 : K) else 0) * weight r := by
      split_ifs <;> simp
    _ = (∑ removed ∈ required.powerset,
          (-1 : K) ^ removed.card *
            (if pairs r ⊆ allowed \ removed then 1 else 0)) * weight r := by
      rw [allowed_required_indicator]
    _ = ∑ removed ∈ required.powerset,
          (-1 : K) ^ removed.card *
            (if pairs r ⊆ allowed \ removed then weight r else 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro removed hremoved
      split_ifs <;> simp

#print axioms alternating_disjoint_coefficient
#print axioms allowed_required_indicator
#print axioms requiredMass_eq_inclusionExclusion
end GProgram.E8.SelectedMass
