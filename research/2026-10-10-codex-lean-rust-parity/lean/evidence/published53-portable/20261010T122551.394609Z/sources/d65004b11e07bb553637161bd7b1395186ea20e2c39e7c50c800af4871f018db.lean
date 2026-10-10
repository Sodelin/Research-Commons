import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Shared-register context test for G1 marginal forest-kernel replacement

New proof contribution: dot's dedicated Lean lane, 2026-10-01.
Two live labelled input lineages have one exponential pair-merger clock.
Their unranked output forest has two states: two survivors or one merger.
The exponential waiting-time law is Mathlib's probability measure, rather than
an unproved axiom for the desired survival probability.

Context contract: the same fair parent register selects the common-bigon
population AND is retained by an exterior that can read/reuse it. This is an
exposed-register experiment, not ordinary passive gene-tree/DNA observation.
The test does not refute marginal replacement with genuinely private,
independent component coins. The accepted conditional-register contract already
retains the register, so no new failure of that accepted theorem is claimed.

No general source graph-to-kernel, grafting, root-blob preservation, source
realizability, or full G1 theorem is established by this component.
-/

namespace GProgram.G1

open ProbabilityTheory

/-- The survival event for the one pair-merger exponential holding time. -/
noncomputable def pairSurvival (rate duration : ℝ) : ℝ :=
  1 - cdf (expMeasure rate) duration

theorem pairSurvival_eq_exp {rate duration : ℝ}
    (hr : 0 < rate) (ht : 0 ≤ duration) :
    pairSurvival rate duration = Real.exp (-(rate * duration)) := by
  rw [pairSurvival, cdf_expMeasure_eq hr]
  simp only [if_pos ht]
  ring

theorem positive_bigon_pair_rates : 0 < Real.log 2 ∧ 0 < Real.log 4 := by
  exact ⟨Real.log_pos (by norm_num), Real.log_pos (by norm_num)⟩

theorem pairSurvival_log_two : pairSurvival (Real.log 2) 1 = 1 / 2 := by
  rw [pairSurvival_eq_exp positive_bigon_pair_rates.1 (by norm_num)]
  simp only [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem pairSurvival_log_four : pairSurvival (Real.log 4) 1 = 1 / 4 := by
  rw [pairSurvival_eq_exp positive_bigon_pair_rates.2 (by norm_num)]
  simp only [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- `true` means the two original labelled forest tokens remain separate;
`false` means their one possible merger has happened. -/
noncomputable def pairForestKernel (rate duration : ℝ) (separate : Bool) : ℝ :=
  if separate then pairSurvival rate duration else 1 - pairSurvival rate duration

theorem pairForestKernel_normalized (rate duration : ℝ) :
    pairForestKernel rate duration true + pairForestKernel rate duration false = 1 := by
  simp only [pairForestKernel, Bool.false_eq_true, if_true, if_false]
  ring

theorem pairForestKernel_nonnegative {rate duration : ℝ}
    (hr : 0 < rate) (ht : 0 ≤ duration) (separate : Bool) :
    0 ≤ pairForestKernel rate duration separate := by
  cases separate
  · simp only [pairForestKernel, Bool.false_eq_true, if_false]
    rw [pairSurvival_eq_exp hr ht]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  · simp only [pairForestKernel, if_true]
    rw [pairSurvival_eq_exp hr ht]
    exact (Real.exp_pos _).le

/-- `p` is the probability that the retained original parent register is 0. -/
def registerWeight (p : ℝ) (register : Bool) : ℝ := if register then 1 - p else p

noncomputable def commonBigonConditional (rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  pairForestKernel (if register then rate1 else rate0) 1 separate

noncomputable def retainedRegisterJoint (p rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  registerWeight p register * commonBigonConditional rate0 rate1 register separate

/-- The unconditional component forest kernel, with the register marginalized. -/
noncomputable def marginalForestKernel (p rate0 rate1 : ℝ) (separate : Bool) : ℝ :=
  retainedRegisterJoint p rate0 rate1 false separate +
    retainedRegisterJoint p rate0 rate1 true separate

/-- The invalid candidate replacement draws from the marginal forest kernel
independently of the exterior's retained original register. -/
noncomputable def freshMarginalJoint (p rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  registerWeight p register * marginalForestKernel p rate0 rate1 separate

theorem retained_register_joint_normalized (p rate0 rate1 : ℝ) :
    retainedRegisterJoint p rate0 rate1 false true +
    retainedRegisterJoint p rate0 rate1 false false +
    retainedRegisterJoint p rate0 rate1 true true +
    retainedRegisterJoint p rate0 rate1 true false = 1 := by
  simp [retainedRegisterJoint, registerWeight, commonBigonConditional, pairForestKernel]
  ring

theorem retained_register_joint_nonnegative {p rate0 rate1 : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (h0 : 0 < rate0) (h1 : 0 < rate1)
    (register separate : Bool) :
    0 ≤ retainedRegisterJoint p rate0 rate1 register separate := by
  unfold retainedRegisterJoint commonBigonConditional
  apply mul_nonneg
  · cases register <;> simp only [registerWeight, Bool.false_eq_true, if_true, if_false]
    · exact hp
    · linarith
  · apply pairForestKernel_nonnegative _ (by norm_num)
    cases register <;> simp_all

theorem shared_register_exact_counterexample :
    marginalForestKernel (1 / 2) (Real.log 2) (Real.log 4) true = 3 / 8 ∧
    retainedRegisterJoint (1 / 2) (Real.log 2) (Real.log 4) false true = 1 / 4 ∧
    freshMarginalJoint (1 / 2) (Real.log 2) (Real.log 4) false true = 3 / 16 := by
  norm_num [marginalForestKernel, retainedRegisterJoint, freshMarginalJoint,
    registerWeight, commonBigonConditional, pairForestKernel,
    pairSurvival_log_two, pairSurvival_log_four]

theorem resampling_changes_exposed_context :
    retainedRegisterJoint (1 / 2) (Real.log 2) (Real.log 4) ≠
      freshMarginalJoint (1 / 2) (Real.log 2) (Real.log 4) := by
  intro heq
  have h := congrFun (congrFun heq false) true
  rw [shared_register_exact_counterexample.2.1,
    shared_register_exact_counterexample.2.2] at h
  norm_num at h

theorem register_survival_difference (p x0 x1 : ℝ) :
    p * x0 - p * (p * x0 + (1 - p) * x1) = p * (1 - p) * (x0 - x1) := by
  ring

/-- For an interior binary shared register, matching the exposed-register
survival event by marginal resampling is possible exactly when the two
conditional survival probabilities are equal. -/
theorem exposed_event_preserved_iff_equal_conditionals {p x0 x1 : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    p * x0 = p * (p * x0 + (1 - p) * x1) ↔ x0 = x1 := by
  constructor
  · intro heq
    have hzero : p * (1 - p) * (x0 - x1) = 0 := by
      rw [← register_survival_difference p x0 x1]
      exact sub_eq_zero.mpr heq
    have hpos : 0 < p * (1 - p) := mul_pos hp (by linarith)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos))
  · intro heq
    subst x1
    ring

#print axioms pairSurvival_eq_exp
#print axioms pairSurvival_log_two
#print axioms pairSurvival_log_four
#print axioms shared_register_exact_counterexample
#print axioms retained_register_joint_normalized
#print axioms retained_register_joint_nonnegative
#print axioms resampling_changes_exposed_context
#print axioms exposed_event_preserved_iff_equal_conditionals

end GProgram.G1
