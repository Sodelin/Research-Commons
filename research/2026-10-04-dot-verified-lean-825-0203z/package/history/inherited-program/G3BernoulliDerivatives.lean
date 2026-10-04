import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Actual COMMON Bernoulli signature factor and its logarithmic responses.
The source definition is 1-p+p*q^n at integer exponent n. These are genuine
analytic derivative identities; no opaque response functions or source
realization conclusions are supplied as hypotheses. -/
noncomputable section

namespace GProgram.G3.AllResidue

def bernoulliFactor (n : ℕ) (p q : ℝ) : ℝ := 1-p+p*q^n

def bernoulliLog (n : ℕ) (p q : ℝ) : ℝ := -Real.log (bernoulliFactor n p q)

theorem bernoulli_factor_pos {n : ℕ} {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    0 < bernoulliFactor n p q := by
  unfold bernoulliFactor
  have hpow : 0 ≤ q^n := pow_nonneg hq0.le n
  nlinarith [mul_nonneg hp0.le hpow]

theorem bernoulli_factor_lt_one {n : ℕ} {p q : ℝ}
    (hn : n ≠ 0) (hp0 : 0 < p) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    bernoulliFactor n p q < 1 := by
  have hpow : q^n < 1 := pow_lt_one₀ hq0 hq1 hn
  have hm := mul_lt_mul_of_pos_left hpow hp0
  unfold bernoulliFactor
  nlinarith

theorem hasDerivAt_bernoulliFactor_p (n : ℕ) (p q : ℝ) :
    HasDerivAt (fun x => bernoulliFactor n x q) (q^n-1) p := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 p := hasDerivAt_id p
  have h1 : HasDerivAt (fun x : ℝ => 1-x) (-1) p := hid.const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => x*q^n) (q^n) p := by
    simpa using hid.mul_const (q^n)
  have h := h1.add h2
  have he : (-1 : ℝ)+q^n = q^n-1 := by ring
  rw [he] at h
  exact h

theorem hasDerivAt_bernoulliFactor_q (n : ℕ) (p q : ℝ) :
    HasDerivAt (fun x => bernoulliFactor n p x)
      (p*(n : ℝ)*q^(n-1)) q := by
  have hpow : HasDerivAt (fun x : ℝ => x^n) ((n : ℝ)*q^(n-1)) q :=
    hasDerivAt_pow n q
  have h := (hpow.const_mul p).const_add (1-p)
  simpa only [bernoulliFactor, mul_assoc] using h

theorem hasDerivAt_bernoulliLog_p {n : ℕ} {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    HasDerivAt (fun x => bernoulliLog n x q)
      ((1-q^n)/bernoulliFactor n p q) p := by
  have hf := hasDerivAt_bernoulliFactor_p n p q
  have hne : bernoulliFactor n p q ≠ 0 :=
    ne_of_gt (bernoulli_factor_pos hp0 hp1 hq0)
  have h := (hf.log hne).neg
  have he : -((q^n-1)/bernoulliFactor n p q) =
      (1-q^n)/bernoulliFactor n p q := by ring
  rw [he] at h
  exact h

theorem hasDerivAt_bernoulliLog_q {n : ℕ} {p q : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) :
    HasDerivAt (fun x => bernoulliLog n p x)
      ((-p*(n : ℝ)*q^(n-1))/bernoulliFactor n p q) q := by
  have hf := hasDerivAt_bernoulliFactor_q n p q
  have hne : bernoulliFactor n p q ≠ 0 :=
    ne_of_gt (bernoulli_factor_pos hp0 hp1 hq0)
  have h := (hf.log hne).neg
  have he : -(p*(n : ℝ)*q^(n-1)/bernoulliFactor n p q) =
      (-p*(n : ℝ)*q^(n-1))/bernoulliFactor n p q := by ring
  rw [he] at h
  exact h

#print axioms bernoulli_factor_pos
#print axioms bernoulli_factor_lt_one
#print axioms hasDerivAt_bernoulliFactor_p
#print axioms hasDerivAt_bernoulliFactor_q
#print axioms hasDerivAt_bernoulliLog_p
#print axioms hasDerivAt_bernoulliLog_q

end GProgram.G3.AllResidue
