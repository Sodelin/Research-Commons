import CMSeparation
import G4ActualPositiveGridUniqueness

/-! Formal integration of the already proved positive finite-atomic moment
supplier used by fixed-start scalar reaction and coherent-orbit arguments.
The sparse double-root separator and positive-grid interpolation are retained
checked suppliers. No stopped-law/derivative oracle or reaction admission is
assumed to be implemented here. Complete actual reaction/observation joins are
separate; this component accepts the explicit positive atomic law it describes. -/
namespace Astra.CommonMoment
open DotG4.ActualSparseCertificateExistence
open DotG4.ActualPositiveGridUniqueness
open scoped Classical BigOperators

/-- Positive weights make every off-reference atom visible to the existing
strict sparse separator. This concludes support inclusion, not just its size. -/
theorem nodes_subset_of_equal_sparse_moments
    (σ τ : FinitePositiveLaw)
    (e : Fin (2 * τ.nodes.card + 1) → ℕ) (he : Function.Injective e)
    (hm : ∀ i, moment σ (e i) = moment τ (e i)) :
    σ.nodes ⊆ τ.nodes := by
  classical
  intro x hx
  by_contra hxτ
  obtain ⟨c, _hp, hnonneg, hzero, hstrict⟩ :=
    exists_strict_sparse_separator τ.nodes τ.node_pos e he
  have hσ : 0 < expectation σ (fun x => (sparseCombination e c).eval x) := by
    apply Finset.sum_pos'
    · intro y hy
      exact mul_nonneg (σ.weight_pos y hy).le (hnonneg y (σ.node_pos y hy).le)
    · exact ⟨x, hx, mul_pos (σ.weight_pos x hx) (hstrict x (σ.node_pos x hx) hxτ)⟩
  have hτ : expectation τ (fun x => (sparseCombination e c).eval x) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    change τ.weight y * (sparseCombination e c).eval y = 0
    rw [hzero y hy, mul_zero]
  have heq : expectation σ (fun x => (sparseCombination e c).eval x) =
      expectation τ (fun x => (sparseCombination e c).eval x) := by
    rw [expectation_sparseCombination, expectation_sparseCombination]
    apply Finset.sum_congr rfl
    intro i _
    rw [hm i]
  rw [heq, hτ] at hσ
  exact (lt_irrefl (0 : ℝ)) hσ

/-- Off-support values of the structure's weight function are immaterial.
This total mass function records exactly the finite atomic measure. -/
noncomputable def atomMass (μ : FinitePositiveLaw) (x : ℝ) : ℝ :=
  if x ∈ μ.nodes then μ.weight x else 0

theorem moment_on_supergrid (μ : FinitePositiveLaw) (A : Finset ℝ)
    (hsub : μ.nodes ⊆ A) (n : ℕ) :
    (∑ a : A, atomMass μ a * (a : ℝ) ^ n) = moment μ n := by
  classical
  rw [Finset.sum_coe_sort]
  calc
    (∑ a ∈ A, atomMass μ a * a ^ n) =
        ∑ a ∈ μ.nodes, atomMass μ a * a ^ n := by
      symm
      apply Finset.sum_subset hsub
      intro a _ ha
      simp [atomMass, ha]
    _ = moment μ n := by
      unfold moment
      apply Finset.sum_congr rfl
      intro a ha
      simp [atomMass, ha]

/-- Any 2r+1 distinct nonnegative integer exponents identify the ENTIRE
positive atomic law of an r-atom reference against ALL finite positive rivals.
No rival atom-count bound is a premise. Classical separator/interpolation
mathematics is reused; this is its explicit full-law composition. -/
theorem atomMass_eq_of_equal_sparse_moments
    (σ τ : FinitePositiveLaw)
    (e : Fin (2 * τ.nodes.card + 1) → ℕ) (he : Function.Injective e)
    (hm : ∀ i, moment σ (e i) = moment τ (e i)) :
    atomMass σ = atomMass τ := by
  classical
  have hsub := nodes_subset_of_equal_sparse_moments σ τ e he hm
  let eA : Fin τ.nodes.card → ℕ := fun i => e ⟨i.val, by omega⟩
  have heA : Function.Injective eA := by
    intro i j hij
    have h := he hij
    apply Fin.ext
    exact congrArg Fin.val h
  have hgrid : (fun a : τ.nodes => atomMass σ a) =
      (fun a : τ.nodes => atomMass τ a) := by
    apply positive_grid_weights_unique τ.nodes τ.node_pos eA heA
    intro i
    rw [moment_on_supergrid σ τ.nodes hsub,
      moment_on_supergrid τ τ.nodes (Finset.Subset.refl _)]
    exact hm ⟨i.val, by omega⟩
  funext x
  by_cases hx : x ∈ τ.nodes
  · exact congrFun hgrid ⟨x, hx⟩
  · have hxσ : x ∉ σ.nodes := fun h => hx (hsub h)
    simp [atomMass, hx, hxσ]

/-- The ordinary consecutive signature used by the scalar fixed-start
reaction coefficient proof is a specialization, including its mass entry. -/
theorem atomMass_eq_of_equal_consecutive_moments
    (σ τ : FinitePositiveLaw)
    (hm : ∀ k ≤ 2 * τ.nodes.card, moment σ k = moment τ k) :
    atomMass σ = atomMass τ := by
  apply atomMass_eq_of_equal_sparse_moments σ τ (fun i => i.val)
    (fun _ _ h => Fin.ext h)
  intro i
  exact hm i.val (by omega)

/-- Exact equality of the full positive law preserves every further moment;
it need not identify individual latent reactions or repeated parameter atoms. -/
theorem all_moments_eq_of_equal_consecutive_moments
    (σ τ : FinitePositiveLaw)
    (hm : ∀ k ≤ 2 * τ.nodes.card, moment σ k = moment τ k) :
    ∀ k, moment σ k = moment τ k := by
  have hmass := atomMass_eq_of_equal_consecutive_moments σ τ hm
  intro k
  classical
  let A := σ.nodes ∪ τ.nodes
  rw [← moment_on_supergrid σ A Finset.subset_union_left k,
    ← moment_on_supergrid τ A Finset.subset_union_right k, hmass]

end Astra.CommonMoment
