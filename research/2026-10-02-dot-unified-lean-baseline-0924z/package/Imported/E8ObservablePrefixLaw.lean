import E8UniformPrefixLaw
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Exact observable pushforward for the strict finite prefix selector.
The finite indexed branch ensemble and classifier are actual functions. The
class mass is derived by summing selector fibers, not supplied as a law field.
This is continuous-uniform exact arithmetic; it does not certify PRISM's finite
PRNG grid, floating operations, or recurrence/classifier semantics.
-/
noncomputable section
namespace E8ObservablePrefixLaw
open MeasureTheory E8StrictPrefixSelector E8UniformPrefixLaw
open scoped BigOperators

variable {n : ℕ} {weight : ℕ → ℝ}

 theorem uniformSelect_lt_on_domain (hpositive : 0 < prefixSum weight n)
    {u : ℝ} (hu : u ∈ Set.Ico 0 1) : uniformSelect n weight hpositive u < n := by
  simp only [uniformSelect, dif_pos hu]
  exact (selected_interval n weight (u * prefixSum weight n)
    (uniform_target_valid n weight u hpositive hu.1 hu.2).1
    (uniform_target_valid n weight u hpositive hu.1 hu.2).2).1

 theorem sentinel_preimage (hpositive : 0 < prefixSum weight n) :
    {u | uniformSelect n weight hpositive u = n} = (Set.Ico (0 : ℝ) 1)ᶜ := by
  ext u
  change uniformSelect n weight hpositive u = n ↔ u ∉ Set.Ico 0 1
  by_cases hu : u ∈ Set.Ico 0 1
  · have hi := uniformSelect_lt_on_domain hpositive hu
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hu, not_true_eq_false, iff_false]
    omega
  · simp only [uniformSelect, dif_neg hu]
    exact iff_of_true trivial hu

 theorem uniformSelect_le (hpositive : 0 < prefixSum weight n) (u : ℝ) :
    uniformSelect n weight hpositive u ≤ n := by
  by_cases hu : u ∈ Set.Ico 0 1
  · exact le_of_lt (uniformSelect_lt_on_domain hpositive hu)
  · simp [uniformSelect, hu]

 theorem uniformSelect_measurable
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n) :
    Measurable (uniformSelect n weight hpositive) := by
  apply measurable_to_countable'
  intro j
  change MeasurableSet {u | uniformSelect n weight hpositive u = j}
  by_cases hj : j < n
  · rw [branch_preimage_interval n weight hweight hpositive j hj]
    exact measurableSet_Ico
  · by_cases heq : j = n
    · subst j
      rw [sentinel_preimage hpositive]
      exact measurableSet_Ico.compl
    · have hempty : {u | uniformSelect n weight hpositive u = j} = ∅ := by
        ext u
        have hle := uniformSelect_le hpositive u
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        omega
      rw [hempty]
      exact MeasurableSet.empty

 theorem selector_pushforward_singleton
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n)
    (j : ℕ) (hj : j < n) :
    (unitUniform.map (uniformSelect n weight hpositive)) {j} =
      ENNReal.ofReal (weight j / prefixSum weight n) := by
  rw [Measure.map_apply (uniformSelect_measurable hweight hpositive)
    (measurableSet_singleton j)]
  exact branch_probability n weight hweight hpositive j hj

 theorem finite_branch_event_mass
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n)
    (s : Finset ℕ) (hs : s ⊆ Finset.range n) :
    unitUniform ((uniformSelect n weight hpositive) ⁻¹' (↑s : Set ℕ)) =
      ENNReal.ofReal ((∑ j ∈ s, weight j) / prefixSum weight n) := by
  classical
  rw [← sum_measure_preimage_singleton s
    (fun j _ => (uniformSelect_measurable hweight hpositive) (measurableSet_singleton j))]
  have heq : (∑ j ∈ s, unitUniform ((uniformSelect n weight hpositive) ⁻¹' {j})) =
      ∑ j ∈ s, ENNReal.ofReal (weight j / prefixSum weight n) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact branch_probability n weight hweight hpositive j (Finset.mem_range.mp (hs hj))
  rw [heq, ← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    exact (Finset.sum_div s weight (prefixSum weight n)).symm
  · intro j hj
    exact div_nonneg (hweight j (Finset.mem_range.mp (hs hj))) (le_of_lt hpositive)

/-- No injectivity assumption on classify: distinct branches may share a label. -/
 theorem observable_class_mass {Class : Type*} [DecidableEq Class] [MeasurableSpace Class]
    [MeasurableSingletonClass Class]
    (hweight : ∀ j < n, 0 ≤ weight j) (hpositive : 0 < prefixSum weight n)
    (classify : ℕ → Class) (c : Class) :
    (unitUniform.map (classify ∘ uniformSelect n weight hpositive)) {c} =
      ENNReal.ofReal ((∑ j ∈ Finset.range n, if classify j = c then weight j else 0) /
        prefixSum weight n) := by
  classical
  have hm := (measurable_of_countable classify).comp (uniformSelect_measurable hweight hpositive)
  rw [Measure.map_apply hm (measurableSet_singleton c)]
  let s := (Finset.range n).filter (fun j => classify j = c)
  have hevent : ((classify ∘ uniformSelect n weight hpositive) ⁻¹' {c}) ∩ Set.Ico 0 1 =
      ((uniformSelect n weight hpositive) ⁻¹' (↑s : Set ℕ)) ∩ Set.Ico 0 1 := by
    ext u
    constructor
    · rintro ⟨hc, hu⟩
      exact ⟨by simpa [s] using And.intro (uniformSelect_lt_on_domain hpositive hu) hc, hu⟩
    · rintro ⟨hsu, hu⟩
      change uniformSelect n weight hpositive u ∈ s at hsu
      exact ⟨by simpa [s] using (Finset.mem_filter.mp hsu).2, hu⟩
  have hmeasure : unitUniform ((classify ∘ uniformSelect n weight hpositive) ⁻¹' {c}) =
      unitUniform ((uniformSelect n weight hpositive) ⁻¹' (↑s : Set ℕ)) := by
    rw [unitUniform, Measure.restrict_apply (hm (measurableSet_singleton c)),
      Measure.restrict_apply ((uniformSelect_measurable hweight hpositive) s.measurableSet), hevent]
  rw [hmeasure, finite_branch_event_mass hweight hpositive s (Finset.filter_subset _ _)]
  congr 1
  congr 1
  exact Finset.sum_filter _ _

end E8ObservablePrefixLaw
#print axioms E8ObservablePrefixLaw.uniformSelect_measurable
#print axioms E8ObservablePrefixLaw.selector_pushforward_singleton
#print axioms E8ObservablePrefixLaw.finite_branch_event_mass
#print axioms E8ObservablePrefixLaw.observable_class_mass
