import G1ActualJointGenerator
import G1TensorExponential

/-!
# Complete joint PMF factorization of an actual separated source epoch

Contributor: dot, 2026-10-03. Independence is derived after conditioning on
the actual entering state, including its SAME original register. The shared
dummy uniformization clock is removed through the actual generator identity;
it is not asserted to be an independence argument.
-/
namespace G1ActualJointEpoch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Matrix NormedSpace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.MatrixProjectionExponential
open G1NonrootBigonKernel G1JointSeparatedSourceGeometry G1ActualJointGenerator G1TensorExponential
open scoped Classical BigOperators NNReal Kronecker Matrix.Norms.Operator
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def independentProduct {A B : Type*} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind (fun a => q.map (fun b => (a,b)))

lemma independentProduct_apply {A B : Type*} [Fintype A] [Fintype B]
    (p : PMF A) (q : PMF B) (v : A × B) : independentProduct p q v = p v.1 * q v.2 := by
  rcases v with ⟨a,b⟩
  rw [independentProduct,PMF.bind_apply,tsum_fintype]
  simp only [PMF.map_apply,tsum_fintype,Prod.mk.injEq]
  have hh (x : A) : (∑ y : B, if a = x ∧ b = y then q y else 0) =
      if a = x then q b else 0 := by
    by_cases hx : a = x
    · simp [hx]
    · simp [hx]
  simp_rw [hh,mul_ite,mul_zero]
  simp

lemma actual_panel_exponential_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s : Code N sample)
    (v : SelectedIndex N sample keep) :
    (((sourceTimeKernel N r t s).map (projection N keep)) v).toReal =
      (exp ((t:ℝ) • selectedGeneratorMatrix N r keep)) (projection N keep s) v := by
  rw [map_probability_real]
  simp_rw [source_time_kernel_eq_exponential]
  have h := congrArg (fun M => M s v) (actual_source_exponential_projection N r keep (t:ℝ))
  simpa [Matrix.mul_apply,projectionMatrix] using h

lemma actual_epoch_separation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (t : ℝ≥0)
    (s : Code N sample) (hsep : PopulationSeparated (state s) inside outside)
    {d : Code N sample} (hd : d ∈ (sourceTimeKernel N r t s).support) :
    PopulationSeparated (state d) inside outside := by
  intro x hx y hy
  rw [actual_time_copy_population N r t s hd x,actual_time_copy_population N r t s hd y]
  exact hsep x hx y hy

lemma joint_exponential_tensor (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (t : ℝ) :
    exp (t • jointGenerator N (sample := sample) r inside outside) =
      exp (t • selectedGeneratorMatrix N r inside) ⊗ₖ
        exp (t • selectedGeneratorMatrix N r outside) := by
  have he : jointGenerator N (sample := sample) r inside outside =
      selectedGeneratorMatrix N r inside ⊗ₖ (1 : Matrix (SelectedIndex N sample outside) _ ℝ) +
        (1 : Matrix (SelectedIndex N sample inside) _ ℝ) ⊗ₖ selectedGeneratorMatrix N r outside := by
    ext a b
    simp only [jointGenerator,Matrix.add_apply,kroneckerMap_apply,Matrix.one_apply]
  rw [he,smul_add,← smul_kronecker,← kronecker_smul,exp_tensor_sum]

/-- Conditional on one actual entering state, complete inside and exterior
forests have the product of their actual original-source epoch laws. No
bound on exterior labels or on carried descendant subtree sizes is imposed. -/
theorem actual_separated_joint_epoch_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (t : ℝ≥0)
    (s : Code N sample) (hsep : PopulationSeparated (state s) inside outside) :
    (sourceTimeKernel N r t s).map (jointProjection N inside outside) =
      independentProduct ((sourceTimeKernel N r t s).map (projection N inside))
        ((sourceTimeKernel N r t s).map (projection N outside)) := by
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [independentProduct_apply,ENNReal.toReal_mul,actual_panel_exponential_row,actual_panel_exponential_row]
  have h := congrArg (fun M => M s v)
    (rectangular_scaled_exp_intertwining _ _ _ (actual_joint_generator_intertwining N r inside outside) (t:ℝ))
  rw [Matrix.mul_apply,Matrix.mul_apply,joint_exponential_tensor] at h
  rw [map_probability_real]
  calc
    _ = ∑ d : Code N sample,
        (exp ((t:ℝ) • sourceGeneratorMatrix N r)) s d *
          separatedProjectionMatrix N inside outside d v := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← source_time_kernel_eq_exponential]
      by_cases hd : d ∈ (sourceTimeKernel N r t s).support
      · have hdsep := actual_epoch_separation N r inside outside t s hsep hd
        simp only [separatedProjectionMatrix,if_pos hdsep,jointProjection,Prod.ext_iff]
        by_cases hi : projection N inside d = v.1 <;>
          by_cases ho : projection N outside d = v.2 <;> simp [hi,ho]
      · have hz : sourceTimeKernel N r t s d = 0 := by simpa [PMF.mem_support_iff] using hd
        simp [hz]
    _ = _ := by
      simpa [separatedProjectionMatrix,hsep,kroneckerMap_apply,Fintype.sum_prod_type] using h

#print axioms actual_separated_joint_epoch_law
end G1ActualJointEpoch
