import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Sum

/- Finite binomial-sum interface for the exact P1 scalar moment request.
This file introduces no quantum, independent-coordinate or Gibbs assumption. -/
namespace P1ScalarMoments

open scoped BigOperators

noncomputable def binomialMean (p q : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
    (p ^ k * q ^ (n - k) * f ((k : ℝ) - ((n - k : ℕ) : ℝ)))

theorem binomialMean_step (p q : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    binomialMean p q (n + 1) f =
      q * binomialMean p q n (fun x => f (x - 1)) +
      p * binomialMean p q n (fun x => f (x + 1)) := by
  unfold binomialMean
  rw [show n + 1 + 1 = n + 2 by omega]
  rw [Finset.sum_choose_succ_mul (fun a b =>
    p ^ a * q ^ b * f ((a : ℝ) - (b : ℝ))) n]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [show n + 1 - k = n - k + 1 by omega, pow_succ, Nat.cast_add, Nat.cast_one]
    have harg : (k : ℝ) - (((n - k : ℕ) : ℝ) + 1) =
        ((k : ℝ) - ((n - k : ℕ) : ℝ)) - 1 := by ring
    rw [harg]
    ring
  · apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have harg : ((k : ℝ) + 1) - ((n - k : ℕ) : ℝ) =
        ((k : ℝ) - ((n - k : ℕ) : ℝ)) + 1 := by ring
    rw [harg]
    ring

theorem binomialMean_const (p q c : ℝ) (n : ℕ) :
    binomialMean p q n (fun _ => c) = (p + q) ^ n * c := by
  unfold binomialMean
  calc
    _ = (∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * p ^ k * q ^ (n - k)) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (p + q) ^ n * c := by
      congr 1
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem binomialMean_congr (p q : ℝ) (n : ℕ) {f g : ℝ → ℝ}
    (h : ∀ x, f x = g x) : binomialMean p q n f = binomialMean p q n g := by
  unfold binomialMean
  apply Finset.sum_congr rfl
  intro k hk
  rw [h]

theorem binomialMean_add (p q : ℝ) (n : ℕ) (f g : ℝ → ℝ) :
    binomialMean p q n (fun x => f x + g x) =
      binomialMean p q n f + binomialMean p q n g := by
  simp only [binomialMean, mul_add, Finset.sum_add_distrib]

theorem binomialMean_smul (p q c : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    binomialMean p q n (fun x => c * f x) = c * binomialMean p q n f := by
  unfold binomialMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem binomialMean_poly4 (p q : ℝ) (n : ℕ) (h : p + q = 1)
    (c0 c1 c2 c3 c4 : ℝ) :
    binomialMean p q n (fun x => c0 + c1*x + c2*x^2 + c3*x^3 + c4*x^4) =
      c0 + c1 * binomialMean p q n (fun x => x) +
        c2 * binomialMean p q n (fun x => x^2) +
        c3 * binomialMean p q n (fun x => x^3) +
        c4 * binomialMean p q n (fun x => x^4) := by
  simp only [binomialMean_add, binomialMean_smul, binomialMean_const,
    h, one_pow, one_mul]
  rw [binomialMean_smul p q c1 n (fun x => x)]

theorem binomialMean_shifted_moments (p q : ℝ) (n : ℕ)
    (h : p + q = 1) (t : ℝ) :
    binomialMean p q n (fun x => x+t) =
      binomialMean p q n (fun x => x) + t ∧
    binomialMean p q n (fun x => (x+t)^2) =
      binomialMean p q n (fun x => x^2) +
        2*t*binomialMean p q n (fun x => x) + t^2 ∧
    binomialMean p q n (fun x => (x+t)^3) =
      binomialMean p q n (fun x => x^3) +
        3*t*binomialMean p q n (fun x => x^2) +
        3*t^2*binomialMean p q n (fun x => x) + t^3 ∧
    binomialMean p q n (fun x => (x+t)^4) =
      binomialMean p q n (fun x => x^4) +
        4*t*binomialMean p q n (fun x => x^3) +
        6*t^2*binomialMean p q n (fun x => x^2) +
        4*t^3*binomialMean p q n (fun x => x) + t^4 := by
  have eval (c0 c1 c2 c3 c4 : ℝ) := binomialMean_poly4 p q n h c0 c1 c2 c3 c4
  constructor
  · calc
      _ = binomialMean p q n (fun x => t + 1*x + 0*x^2 + 0*x^3 + 0*x^4) := by
        apply binomialMean_congr
        intro x
        ring
      _ = _ := by rw [eval]; ring
  constructor
  · calc
      _ = binomialMean p q n (fun x => t^2 + (2*t)*x + 1*x^2 + 0*x^3 + 0*x^4) := by
        apply binomialMean_congr
        intro x
        ring
      _ = _ := by rw [eval]; ring
  constructor
  · calc
      _ = binomialMean p q n (fun x => t^3 + (3*t^2)*x + (3*t)*x^2 + 1*x^3 + 0*x^4) := by
        apply binomialMean_congr
        intro x
        ring
      _ = _ := by rw [eval]; ring
  · calc
      _ = binomialMean p q n (fun x => t^4 + (4*t^3)*x + (6*t^2)*x^2 + (4*t)*x^3 + 1*x^4) := by
        apply binomialMean_congr
        intro x
        ring
      _ = _ := by rw [eval]; ring

/-- The real falling products are valid even for n=0,1,2,3. -/
theorem binomialMean_moments (p q r : ℝ) (hpq : p + q = 1) (hr : p - q = r)
    (n : ℕ) :
    binomialMean p q n (fun x => x) = (n:ℝ)*r ∧
    binomialMean p q n (fun x => x^2) = (n:ℝ)+(n:ℝ)*((n:ℝ)-1)*r^2 ∧
    binomialMean p q n (fun x => x^3) =
      (n:ℝ)*(3*(n:ℝ)-2)*r + (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)*r^3 ∧
    binomialMean p q n (fun x => x^4) =
      (n:ℝ)*(3*(n:ℝ)-2) + 2*(n:ℝ)*((n:ℝ)-1)*(3*(n:ℝ)-4)*r^2 +
        (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)*((n:ℝ)-3)*r^4 := by
  have hp : p = (1+r)/2 := by linarith
  have hq : q = (1-r)/2 := by linarith
  induction n with
  | zero => simp [binomialMean]
  | succ n ih =>
    rcases ih with ⟨h1,h2,h3,h4⟩
    rcases binomialMean_shifted_moments p q n hpq (-1) with ⟨hm1,hm2,hm3,hm4⟩
    rcases binomialMean_shifted_moments p q n hpq 1 with ⟨hp1,hp2,hp3,hp4⟩
    constructor
    · rw [binomialMean_step]
      simp only [sub_eq_add_neg]
      rw [hm1,hp1,h1,hp,hq]
      push_cast
      ring
    constructor
    · rw [binomialMean_step]
      simp only [sub_eq_add_neg]
      rw [hm2,hp2,h1,h2,hp,hq]
      push_cast
      ring
    constructor
    · rw [binomialMean_step]
      simp only [sub_eq_add_neg]
      rw [hm3,hp3,h1,h2,h3,hp,hq]
      push_cast
      ring
    · rw [binomialMean_step]
      simp only [sub_eq_add_neg]
      rw [hm4,hp4,h1,h2,h3,h4,hp,hq]
      push_cast
      ring

end P1ScalarMoments
