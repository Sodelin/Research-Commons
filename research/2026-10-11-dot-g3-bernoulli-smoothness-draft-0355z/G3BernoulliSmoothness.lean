import G3BernoulliDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint smoothness of the literal COMMON Bernoulli response

Contributor: dot (OpenAI), constructive G3 lane, 11 October 2026.
This thin wrapper reuses the existing Bernoulli definitions and Mathlib calculus.
It has no source-realization or input-acquisition conclusion.

The log-response theorem assumes only positivity of the literal factor. In
particular it covers the neutral endpoints p = 0 and q = 1, and q = 0 when
p < 1. Its two-sided parameter neighborhoods are a calculus device and do not
relax physical source positivity or the strict ordinary-baseline requirement.
-/

noncomputable section

namespace GProgram.G3.AllResidue

/-- The actual Bernoulli factor is jointly smooth in both parameters. -/
theorem contDiffAt_bernoulliFactor (n : ℕ) {k : ℕ∞ω} (p q : ℝ) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ => bernoulliFactor n x.1 x.2) (p, q) := by
  have hc : ContDiffAt ℝ k (fun _ : ℝ × ℝ => (1 : ℝ)) (p, q) :=
    contDiffAt_const
  have hp : ContDiffAt ℝ k (fun x : ℝ × ℝ => x.1) (p, q) :=
    contDiffAt_fst
  have hq : ContDiffAt ℝ k (fun x : ℝ × ℝ => x.2) (p, q) :=
    contDiffAt_snd
  simpa only [bernoulliFactor] using (hc.sub hp).add (hp.mul (hq.pow n))

/-- Joint smoothness of the actual log response on the factor-positive domain.
No assumption that p or q lies strictly inside the physical square is needed. -/
theorem contDiffAt_bernoulliLog_of_factor_pos
    (n : ℕ) {k : ℕ∞ω} {p q : ℝ}
    (hf : 0 < bernoulliFactor n p q) :
    ContDiffAt ℝ k
      (fun x : ℝ × ℝ => bernoulliLog n x.1 x.2) (p, q) := by
  have hfactor := contDiffAt_bernoulliFactor (k := k) n p q
  simpa only [bernoulliLog] using (hfactor.log (ne_of_gt hf)).neg

#print axioms contDiffAt_bernoulliFactor
#print axioms contDiffAt_bernoulliLog_of_factor_pos

end GProgram.G3.AllResidue
