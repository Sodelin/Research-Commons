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


#check pairSurvival_eq_exp
end GProgram.G1
