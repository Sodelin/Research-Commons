import G3BernoulliSmoothness
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Literal finite normalized COMMON word: product/log and smoothness bridge

Contributor: dot (OpenAI), constructive G3 lane, 11 October 2026.
Source draft, uncompiled. This composes the accepted cell definitions with
finite products and sums. It introduces no new probability process and does
not assert that an arbitrary original source has this normalized word form.
Original-source extraction/construction remains a separately stated receiver
obligation; the full supplied exponent vector uses ONE common parameter tuple.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace GProgram.G3.AllResidue

abbrev FiniteWordParameters (N : ℕ) := ℝ × (Fin N → ℝ × ℝ)

/-- The literal normalized finite product, without killing or residual terms. -/
def finiteWordMoment {N : ℕ} (n : ℕ) (x : FiniteWordParameters N) : ℝ :=
  x.1 ^ n * ∏ i, bernoulliFactor n (x.2 i).1 (x.2 i).2

/-- The same parameters in the additive log coordinates used by the hand proofs. -/
def finiteWordLog {N : ℕ} (n : ℕ) (x : FiniteWordParameters N) : ℝ :=
  -(n : ℝ) * Real.log x.1 + ∑ i, bernoulliLog n (x.2 i).1 (x.2 i).2

/-- Positivity permits neutral factors at chart boundaries, but does not assert
strict physical admission of their parameters. -/
theorem finiteWordMoment_pos {N : ℕ} (n : ℕ) (x : FiniteWordParameters N)
    (hA : 0 < x.1)
    (hf : ∀ i, 0 < bernoulliFactor n (x.2 i).1 (x.2 i).2) :
    0 < finiteWordMoment n x := by
  exact mul_pos (pow_pos hA n) (Finset.prod_pos (fun i _ => hf i))

/-- Exact product-to-log identity; no response identity is supplied as a premise. -/
theorem neg_log_finiteWordMoment {N : ℕ} (n : ℕ) (x : FiniteWordParameters N)
    (hA : 0 < x.1)
    (hf : ∀ i, 0 < bernoulliFactor n (x.2 i).1 (x.2 i).2) :
    -Real.log (finiteWordMoment n x) = finiteWordLog n x := by
  have hprod : (∏ i, bernoulliFactor n (x.2 i).1 (x.2 i).2) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hf i))
  rw [finiteWordMoment, Real.log_mul (pow_ne_zero n (ne_of_gt hA)) hprod,
    Real.log_pow, Real.log_prod (fun i _ => ne_of_gt (hf i))]
  simp only [finiteWordLog, bernoulliLog, Finset.sum_neg_distrib]
  ring

/-- Recovery of every literal moment from the same additive log response. -/
theorem exp_neg_finiteWordLog {N : ℕ} (n : ℕ) (x : FiniteWordParameters N)
    (hA : 0 < x.1)
    (hf : ∀ i, 0 < bernoulliFactor n (x.2 i).1 (x.2 i).2) :
    Real.exp (-finiteWordLog n x) = finiteWordMoment n x := by
  rw [← neg_log_finiteWordMoment n x hA hf, neg_neg]
  exact Real.exp_log (finiteWordMoment_pos n x hA hf)

/-- Joint regularity in the ordinary survival and every literal cell pair. -/
theorem contDiffAt_finiteWordLog {N : ℕ} (n : ℕ) {k : ℕ∞ω}
    (x : FiniteWordParameters N) (hA : 0 < x.1)
    (hf : ∀ i, 0 < bernoulliFactor n (x.2 i).1 (x.2 i).2) :
    ContDiffAt ℝ k (finiteWordLog n) x := by
  have hAmap : ContDiffAt ℝ k (fun y : FiniteWordParameters N => y.1) x :=
    contDiffAt_fst
  have hc : ContDiffAt ℝ k (fun _ : FiniteWordParameters N => -(n : ℝ)) x :=
    contDiffAt_const
  have hbase := hc.mul (hAmap.log (ne_of_gt hA))
  have hcell (i : Fin N) : ContDiffAt ℝ k
      (fun y : FiniteWordParameters N => bernoulliLog n (y.2 i).1 (y.2 i).2) x := by
    have htail : ContDiffAt ℝ k
        (fun y : FiniteWordParameters N => y.2) x := contDiffAt_snd
    have heval : ContDiffAt ℝ k
        (fun y : FiniteWordParameters N => y.2 i) x :=
      (contDiffAt_apply ℝ (ℝ × ℝ) i x.2).comp x htail
    exact (contDiffAt_bernoulliLog_of_factor_pos (k := k) n (hf i)).comp x heval
  have hsum : ContDiffAt ℝ k
      (fun y : FiniteWordParameters N => ∑ i, bernoulliLog n (y.2 i).1 (y.2 i).2) x :=
    ContDiffAt.sum (fun i _ => hcell i)
  exact hbase.add hsum

/-- A finite observation exponent vector shares the same word parameter bank. -/
theorem contDiffAt_finiteWordLog_vector {N d : ℕ} (lambda : Fin d → ℕ)
    {k : ℕ∞ω} (x : FiniteWordParameters N) (hA : 0 < x.1)
    (hf : ∀ j i, 0 < bernoulliFactor (lambda j) (x.2 i).1 (x.2 i).2) :
    ContDiffAt ℝ k
      (fun y : FiniteWordParameters N => fun j => finiteWordLog (lambda j) y) x := by
  exact contDiffAt_pi.mpr (fun j => contDiffAt_finiteWordLog (lambda j) x hA (hf j))

#print axioms finiteWordMoment_pos
#print axioms neg_log_finiteWordMoment
#print axioms exp_neg_finiteWordLog
#print axioms contDiffAt_finiteWordLog
#print axioms contDiffAt_finiteWordLog_vector

end GProgram.G3.AllResidue
