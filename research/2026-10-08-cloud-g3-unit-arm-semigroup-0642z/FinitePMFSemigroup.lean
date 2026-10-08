import UnifiedLean.Source.SourcePoissonExponential

/-! Genuine normalized finite-PMF Poisson semigroup, reusing the inherited
standard exponential-entry calculation. Cloud G3, 2026-10-08. UNCHECKED.
This is generic PMF algebra; the actual original source instance is separate. -/
namespace CloudG3.FinitePMFSemigroup
set_option backward.isDefEq.respectTransparency false
open ProbabilityTheory MeasureTheory Matrix NormedSpace
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def transition (R : I → PMF I) : Matrix I I ℝ := fun s d => (R s d).toReal
noncomputable def generator (R : I → PMF I) (B : ℝ≥0) : Matrix I I ℝ :=
  (B : ℝ) • (transition R - 1)

noncomputable def iteration (R : I → PMF I) : Nat → I → PMF I
  | 0,s => PMF.pure s
  | k+1,s => (R s).bind (iteration R k)

/-- Normalization is from the actual PMF constructors, not an exp positivity
or row-sum hypothesis. -/
noncomputable def timeKernel (R : I → PMF I) (B t : ℝ≥0) (s : I) : PMF I :=
  (countPMF (B*t)).bind (fun k => iteration R k s)

lemma iteration_probability (R : I → PMF I) (k : Nat) (s d : I) :
    (iteration R k s d).toReal = (transition R ^ k) s d := by
  induction k generalizing s with
  | zero =>
      simp only [iteration,pow_zero,PMF.pure_apply,Matrix.one_apply]
      by_cases h : d = s
      · simp [h]
      · simp [h,Ne.symm h]
  | succ k ih =>
      rw [iteration,bind_probability_real,tsum_fintype,pow_succ',Matrix.mul_apply]
      simp_rw [ih]
      rfl

/-- The normalized finite time row equals its generator exponential. No
source law or desired exponential entry is assumed. -/
theorem time_probability (R : I → PMF I) (B t : ℝ≥0) (s d : I) :
    (timeKernel R B t s d).toReal = (exp ((t : ℝ) • generator R B)) s d := by
  rw [timeKernel,bind_probability_real]
  simp_rw [countPMF_real,iteration_probability]
  rw [poisson_matrix_entry]
  apply congrArg (fun M : Matrix I I ℝ => (exp M) s d)
  simp only [generator,smul_smul,NNReal.coe_mul]
  congr 1
  exact mul_comm _ _

/-- Exact normalized PMF semigroup. Zero time and empty finite carriers need
no fabricated default state. The statement is conditional on its supplied s. -/
theorem time_bind (R : I → PMF I) (B a b : ℝ≥0) (s : I) :
    (timeKernel R B a s).bind (timeKernel R B b) = timeKernel R B (a+b) s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,tsum_fintype]
  simp_rw [time_probability]
  change (exp ((a : ℝ) • generator R B) * exp ((b : ℝ) • generator R B)) s d = _
  have hc : Commute ((a : ℝ) • generator R B) ((b : ℝ) • generator R B) :=
    (Commute.refl (generator R B)).smul_left (a : ℝ) |>.smul_right (b : ℝ)
  rw [← exp_add_of_commute hc]
  simp only [NNReal.coe_add,add_smul]

theorem time_zero (R : I → PMF I) (B : ℝ≥0) (s : I) :
    timeKernel R B 0 s = PMF.pure s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [time_probability]
  by_cases h : d = s
  · simp [h,PMF.pure_apply]
  · simp [h,Ne.symm h,PMF.pure_apply]

end CloudG3.FinitePMFSemigroup
