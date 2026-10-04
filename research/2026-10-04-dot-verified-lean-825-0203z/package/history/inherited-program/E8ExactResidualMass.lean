import E8DeterministicTopKCertificate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Exact residual-mass certification for a finite weighted structure ensemble.
The class map is an actual function on the ensemble, not an independently
specified probability table. Weights and sums are exact reals. The classical
residual-mass top-k method is not claimed to be historically new. No RNA
grammar fidelity, executable adapter, finite-precision accuracy or IID source
law is concluded.
-/

noncomputable section

namespace E8ExactResidualMass

open scoped BigOperators
open E8DeterministicTopKCertificate

variable {Structure Class : Type*}

def partition (ensemble : Finset Structure) (weight : Structure → ℝ) : ℝ :=
  ∑ r ∈ ensemble, weight r

def classPartition (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (c : Class) : ℝ := by
  classical
  exact ∑ r ∈ ensemble, if classify r = c then weight r else 0

def outsidePartition (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class) : ℝ := by
  classical
  exact ∑ r ∈ ensemble, if classify r ∈ selected then 0 else weight r

def classMass (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (c : Class) : ℝ :=
  classPartition ensemble classify weight c / partition ensemble weight

def residualMass (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class) : ℝ :=
  outsidePartition ensemble classify weight selected / partition ensemble weight

theorem selected_partition_decomposition
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class) :
    (∑ c ∈ selected, classPartition ensemble classify weight c) +
      outsidePartition ensemble classify weight selected = partition ensemble weight := by
  classical
  simp only [classPartition, outsidePartition, partition]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hc : classify r ∈ selected
  · simp [hc]
  · simp [hc]

theorem class_partition_nonnegative
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (c : Class)
    (hweight : ∀ r ∈ ensemble, 0 ≤ weight r) :
    0 ≤ classPartition ensemble classify weight c := by
  classical
  apply Finset.sum_nonneg
  intro r hr
  split_ifs <;> simp [hweight r hr]

theorem residual_partition_nonnegative
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class)
    (hweight : ∀ r ∈ ensemble, 0 ≤ weight r) :
    0 ≤ outsidePartition ensemble classify weight selected := by
  classical
  apply Finset.sum_nonneg
  intro r hr
  split_ifs <;> simp [hweight r hr]

theorem omitted_class_partition_le_residual
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class) (c : Class)
    (hweight : ∀ r ∈ ensemble, 0 ≤ weight r) (hc : c ∉ selected) :
    classPartition ensemble classify weight c ≤
      outsidePartition ensemble classify weight selected := by
  classical
  apply Finset.sum_le_sum
  intro r hr
  by_cases he : classify r = c
  · simp [he, hc]
  · by_cases hs : classify r ∈ selected
    · simp [he, hs]
    · simp [he, hs, hweight r hr]

theorem omitted_class_mass_le_residual
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class) (c : Class)
    (hweight : ∀ r ∈ ensemble, 0 ≤ weight r)
    (hpartition : 0 < partition ensemble weight) (hc : c ∉ selected) :
    classMass ensemble classify weight c ≤
      residualMass ensemble classify weight selected := by
  exact (div_le_div_iff_of_pos_right hpartition).mpr
    (omitted_class_partition_le_residual ensemble classify weight selected c hweight hc)

theorem normalized_residual_eq_one_sub_selected
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class)
    (hpartition : 0 < partition ensemble weight) :
    residualMass ensemble classify weight selected =
      1 - ∑ c ∈ selected, classMass ensemble classify weight c := by
  have hd := selected_partition_decomposition ensemble classify weight selected
  simp only [classMass, residualMass]
  rw [← Finset.sum_div]
  field_simp [ne_of_gt hpartition]
  linarith

theorem exact_residual_topK
    (ensemble : Finset Structure) (classify : Structure → Class)
    (weight : Structure → ℝ) (selected : Finset Class) (k : ℕ)
    (hcard : selected.card = k)
    (hweight : ∀ r ∈ ensemble, 0 ≤ weight r)
    (hpartition : 0 < partition ensemble weight)
    (hgap : ∀ c ∈ selected, residualMass ensemble classify weight selected <
      classMass ensemble classify weight c) :
    IsStrictTopKSet (classMass ensemble classify weight) selected k := by
  refine ⟨hcard, ?_⟩
  intro a ha b hb
  exact lt_of_le_of_lt
    (omitted_class_mass_le_residual ensemble classify weight selected b hweight hpartition hb)
    (hgap a ha)

end E8ExactResidualMass

#print axioms E8ExactResidualMass.selected_partition_decomposition
#print axioms E8ExactResidualMass.class_partition_nonnegative
#print axioms E8ExactResidualMass.residual_partition_nonnegative
#print axioms E8ExactResidualMass.omitted_class_partition_le_residual
#print axioms E8ExactResidualMass.omitted_class_mass_le_residual
#print axioms E8ExactResidualMass.normalized_residual_eq_one_sub_selected
#print axioms E8ExactResidualMass.exact_residual_topK
