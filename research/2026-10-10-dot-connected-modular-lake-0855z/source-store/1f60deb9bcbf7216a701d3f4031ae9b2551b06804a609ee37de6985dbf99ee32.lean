import E8ObservablePrefixLaw
import E8MidpointGridTV
import E8TracebackErrorComposition
import Mathlib.Algebra.BigOperators.Fin

/-!
Named integration: strict continuous/grid selection of the exact production
contributions factor*child-partition. All branch tables are derived from the
same contributions. Grid normalization is proved by actual selector-fiber
counting, allowing finite-depth perturbation composition downstream.
Uniform independent grid inputs and exact arithmetic remain explicit model
assumptions; the C++ numeric/PRNG and RNA grammar connections are not concluded.
-/
noncomputable section
namespace E8MidpointProductionKernel
open E8StrictPrefixSelector E8UniformPrefixLaw E8ObservablePrefixLaw
open E8MidpointGridLaw E8MidpointGridTV E8FiniteTracebackLaw E8TracebackErrorComposition
open scoped BigOperators

def extendWeight {b : ℕ} (weight : Fin b → ℝ) (j : ℕ) : ℝ :=
  if h : j < b then weight ⟨j, h⟩ else 0

theorem extendWeight_total {b : ℕ} (weight : Fin b → ℝ) :
    prefixSum (extendWeight weight) b = ∑ j, weight j := by
  rw [prefixSum, Finset.sum_range]
  simp [extendWeight]

theorem extendWeight_nonnegative {b : ℕ} (weight : Fin b → ℝ)
    (hw : ∀ j, 0 ≤ weight j) : ∀ j < b, 0 ≤ extendWeight weight j := by
  intro j hj
  simpa [extendWeight, hj] using hw ⟨j, hj⟩

def gridKernel {b : ℕ} (N : ℕ) (weight : Fin b → ℝ) (hW : 0 < ∑ j, weight j)
    (j : Fin b) : ℝ :=
  gridBranchMass N b (extendWeight weight) (by rw [extendWeight_total]; exact hW) j

theorem gridKernel_nonnegative {b : ℕ} (N : ℕ) (weight : Fin b → ℝ)
    (hW : 0 < ∑ j, weight j) (j : Fin b) : 0 ≤ gridKernel N weight hW j := by
  unfold gridKernel gridBranchMass
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem gridKernel_total {b : ℕ} (N : ℕ) (hN : 0 < N) (weight : Fin b → ℝ)
    (hW : 0 < ∑ j, weight j) : (∑ j, gridKernel N weight hW j) = 1 := by
  let hp : 0 < prefixSum (extendWeight weight) b := by rw [extendWeight_total]; exact hW
  let f : ℕ → ℕ := fun k => uniformSelect b (extendWeight weight) hp (midpoint N k)
  have hmap : (Finset.range N : Set ℕ).MapsTo f (Finset.range b) := by
    intro k hk
    apply Finset.mem_range.mpr
    exact uniformSelect_lt_on_domain hp (midpoint_in_domain N hN k (Finset.mem_range.mp hk))
  have hc := Finset.card_eq_sum_card_fiberwise hmap
  simp only [Finset.card_range] at hc
  have hcFin : (∑ j : Fin b, ((Finset.range N).filter (fun k => f k = j)).card) = N := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ((Finset.range N).filter (fun k => f k = j)).card) b]
    exact hc.symm
  unfold gridKernel gridBranchMass
  change (∑ j : Fin b, (((Finset.range N).filter (fun k => f k = j)).card : ℝ) / N) = 1
  rw [← Finset.sum_div, ← Nat.cast_sum, hcFin, div_self]
  exact_mod_cast (ne_of_gt hN)

theorem gridKernel_TV {b : ℕ} (N : ℕ) (hN : 0 < N) (weight : Fin b → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hW : 0 < ∑ j, weight j) :
    (∑ j, |gridKernel N weight hW j - weight j / (∑ k, weight k)|) / 2 ≤
      (b - 1 : ℕ) / (2 * N) := by
  have h := grid_branch_TV_bound N hN b (extendWeight weight)
    (extendWeight_nonnegative weight hw) (by rw [extendWeight_total]; exact hW)
  unfold branchTV at h
  rw [Finset.sum_range] at h
  simpa [gridKernel, extendWeight, extendWeight_total] using h

theorem continuous_weight_kernel {b : ℕ} (weight : Fin b → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hW : 0 < ∑ j, weight j) (j : Fin b) :
    unitUniform {u | uniformSelect b (extendWeight weight)
      (by rw [extendWeight_total]; exact hW) u = j.val} =
      ENNReal.ofReal (weight j / ∑ k, weight k) := by
  rw [branch_probability b (extendWeight weight) (extendWeight_nonnegative weight hw)
    (by rw [extendWeight_total]; exact hW) j.val j.isLt]
  simp [extendWeight, extendWeight_total]

variable {State : Type*} (b : ℕ) (factor : State → Fin b → ℝ)
    (next : State → Fin b → State) (terminal : State → ℝ)

def productionWeights (d : ℕ) (s : State) (j : Fin b) : ℝ :=
  factor s j * partition b factor next terminal d (next s j)

theorem productionWeight_total (d : ℕ) (s : State) :
    (∑ j, productionWeights b factor next terminal d s j) =
      partition b factor next terminal (d + 1) s := rfl

theorem production_continuous_branch
    (hf : ∀ s j, 0 ≤ factor s j)
    (hP : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) (j : Fin b) :
    unitUniform {u | uniformSelect b (extendWeight (productionWeights b factor next terminal d s))
      (by rw [extendWeight_total, productionWeight_total]; exact hP (d + 1) s) u = j.val} =
      ENNReal.ofReal (branchProbability b factor next terminal d s j) := by
  have hw : ∀ j, 0 ≤ productionWeights b factor next terminal d s j := fun j =>
    mul_nonneg (hf s j) (hP d (next s j)).le
  simpa [branchProbability, productionWeights, partition] using
    continuous_weight_kernel (productionWeights b factor next terminal d s) hw
      (by rw [productionWeight_total]; exact hP (d + 1) s) j

end E8MidpointProductionKernel
#print axioms E8MidpointProductionKernel.gridKernel_total
#print axioms E8MidpointProductionKernel.gridKernel_TV
#print axioms E8MidpointProductionKernel.continuous_weight_kernel
#print axioms E8MidpointProductionKernel.production_continuous_branch
