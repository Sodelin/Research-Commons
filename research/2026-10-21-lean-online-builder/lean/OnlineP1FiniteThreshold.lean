import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity


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


namespace P1ScalarMoments

open scoped BigOperators

noncomputable def signedMean (r : ℝ) (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  binomialMean ((1+r)/2) ((1-r)/2) n f

noncomputable def moment (r : ℝ) (n j : ℕ) : ℝ :=
  signedMean r n (fun x => x^j)

theorem signedMean_const (r c : ℝ) (n : ℕ) :
    signedMean r n (fun _ => c) = c := by
  unfold signedMean
  rw [binomialMean_const]
  have h : (1+r)/2 + (1-r)/2 = 1 := by ring
  rw [h, one_pow, one_mul]

theorem signedMean_poly4 (r : ℝ) (n : ℕ) (c0 c1 c2 c3 c4 : ℝ) :
    signedMean r n (fun x => c0 + c1*x + c2*x^2 + c3*x^3 + c4*x^4) =
      c0 + c1*moment r n 1 + c2*moment r n 2 + c3*moment r n 3 + c4*moment r n 4 := by
  have h : (1+r)/2 + (1-r)/2 = 1 := by ring
  simpa only [signedMean, moment, pow_one] using
    binomialMean_poly4 ((1+r)/2) ((1-r)/2) n h c0 c1 c2 c3 c4

theorem signedMean_congr (r : ℝ) (n : ℕ) {f g : ℝ → ℝ}
    (h : ∀ x, f x = g x) : signedMean r n f = signedMean r n g :=
  binomialMean_congr _ _ _ h

theorem moment_formulas (r : ℝ) (n : ℕ) :
    moment r n 1 = (n:ℝ)*r ∧
    moment r n 2 = (n:ℝ)+(n:ℝ)*((n:ℝ)-1)*r^2 ∧
    moment r n 3 = (n:ℝ)*(3*(n:ℝ)-2)*r + (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)*r^3 ∧
    moment r n 4 = (n:ℝ)*(3*(n:ℝ)-2) + 2*(n:ℝ)*((n:ℝ)-1)*(3*(n:ℝ)-4)*r^2 +
      (n:ℝ)*((n:ℝ)-1)*((n:ℝ)-2)*((n:ℝ)-3)*r^4 := by
  have hpq : (1+r)/2 + (1-r)/2 = 1 := by ring
  have hr : (1+r)/2 - (1-r)/2 = r := by ring
  simpa only [moment, signedMean, pow_one] using
    binomialMean_moments ((1+r)/2) ((1-r)/2) r hpq hr n

noncomputable def pairMean (r s : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  signedMean r n (fun x => signedMean s n (f x))

theorem pairMean_congr (r s : ℝ) (n : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ x y, f x y = g x y) : pairMean r s n f = pairMean r s n g := by
  apply signedMean_congr
  intro x
  apply signedMean_congr
  exact h x

theorem pairMean_quadratic (r s a b c : ℝ) (n : ℕ) :
    pairMean r s n (fun x y => a*x^2 + a*y^2 + b*x*y + c) =
      a*(moment r n 2 + moment s n 2) + b*moment r n 1*moment s n 1 + c := by
  unfold pairMean
  have inner (x : ℝ) :
      signedMean s n (fun y => a*x^2 + a*y^2 + b*x*y + c) =
      (a*moment s n 2+c) + (b*moment s n 1)*x + a*x^2 + 0*x^3 + 0*x^4 := by
    calc
      _ = signedMean s n (fun y => (a*x^2+c) + (b*x)*y + a*y^2 + 0*y^3 + 0*y^4) := by
        apply signedMean_congr
        intro y
        ring
      _ = _ := by rw [signedMean_poly4]; ring
  simp_rw [inner]
  rw [signedMean_poly4]
  ring

theorem pairMean_quadratic_square (r s a b c : ℝ) (n : ℕ) :
    pairMean r s n (fun x y => (a*x^2 + a*y^2 + b*x*y + c)^2) =
      a^2*(moment r n 4 + moment s n 4) +
      (2*a^2+b^2)*moment r n 2*moment s n 2 +
      2*a*b*(moment r n 3*moment s n 1 + moment r n 1*moment s n 3) +
      2*a*c*(moment r n 2+moment s n 2) +
      2*b*c*moment r n 1*moment s n 1 + c^2 := by
  unfold pairMean
  have inner (x : ℝ) :
      signedMean s n (fun y => (a*x^2 + a*y^2 + b*x*y + c)^2) =
      (c^2+2*a*c*moment s n 2+a^2*moment s n 4) +
      (2*b*c*moment s n 1+2*a*b*moment s n 3)*x +
      (2*a*c+(b^2+2*a^2)*moment s n 2)*x^2 +
      (2*a*b*moment s n 1)*x^3 + a^2*x^4 := by
    calc
      _ = signedMean s n (fun y => (a*x^2+c)^2 +
          (2*(a*x^2+c)*b*x)*y + (b^2*x^2+2*a*(a*x^2+c))*y^2 +
          (2*a*b*x)*y^3 + a^2*y^4) := by
        apply signedMean_congr
        intro y
        ring
      _ = _ := by rw [signedMean_poly4]; ring
  simp_rw [inner]
  rw [signedMean_poly4]
  ring

noncomputable def quadraticStatistic (n : ℕ) (x y : ℝ) : ℝ :=
  (x^2-(n:ℝ))/((n:ℝ)*((n:ℝ)-1)) +
  (y^2-(n:ℝ))/((n:ℝ)*((n:ℝ)-1)) - 2*x*y/(n:ℝ)^2

theorem quadratic_mean_variance (r s : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    pairMean r s n (quadraticStatistic n) = (r-s)^2 ∧
    pairMean r s n (fun x y => (quadraticStatistic n x y-(r-s)^2)^2) =
      4*(r-s)^2*((1-r^2)+(1-s^2))/(n:ℝ) +
      2*((1-r^2)^2+(1-s^2)^2)/((n:ℝ)*((n:ℝ)-1)) +
      4*(1-r^2)*(1-s^2)/(n:ℝ)^2 := by
  have hnreal : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  rcases moment_formulas r n with ⟨hr1,hr2,hr3,hr4⟩
  rcases moment_formulas s n with ⟨hs1,hs2,hs3,hs4⟩
  constructor
  · calc
      _ = pairMean r s n (fun x y =>
          (1/((n:ℝ)*((n:ℝ)-1)))*x^2 +
          (1/((n:ℝ)*((n:ℝ)-1)))*y^2 +
          (-2/(n:ℝ)^2)*x*y + (-2*(n:ℝ)/((n:ℝ)*((n:ℝ)-1)))) := by
        apply pairMean_congr
        intro x y
        unfold quadraticStatistic
        ring
      _ = _ := by
        rw [pairMean_quadratic,hr1,hr2,hs1,hs2]
        field_simp [hn0,hn1]
        ring
  · calc
      _ = pairMean r s n (fun x y =>
          ((1/((n:ℝ)*((n:ℝ)-1)))*x^2 +
          (1/((n:ℝ)*((n:ℝ)-1)))*y^2 +
          (-2/(n:ℝ)^2)*x*y + (-2*(n:ℝ)/((n:ℝ)*((n:ℝ)-1))-(r-s)^2))^2) := by
        apply pairMean_congr
        intro x y
        unfold quadraticStatistic
        ring
      _ = _ := by
        rw [pairMean_quadratic_square,hr1,hr2,hr3,hr4,hs1,hs2,hs3,hs4]
        field_simp [hn0,hn1]
        ring

noncomputable def countWeight (r : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (((1+r)/2)^k * ((1-r)/2)^(n-k))

theorem signedMean_eq_count_sum (r : ℝ) (n : ℕ) (f : ℝ → ℝ) :
    signedMean r n f = ∑ k ∈ Finset.range (n+1),
      countWeight r n k * f (2*(k:ℝ)-(n:ℝ)) := by
  unfold signedMean binomialMean countWeight
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have harg : (k:ℝ)-((n-k:ℕ):ℝ) = 2*(k:ℝ)-(n:ℝ) := by
    rw [Nat.cast_sub hkn]
    ring
  rw [harg]
  ring

theorem pairMean_eq_count_sum (r s : ℝ) (n : ℕ) (f : ℝ → ℝ → ℝ) :
    pairMean r s n f = ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      countWeight r n a * countWeight s n b *
        f (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ)) := by
  unfold pairMean
  rw [signedMean_eq_count_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [signedMean_eq_count_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem countWeight_nonnegative (r : ℝ) (hr : -1 ≤ r ∧ r ≤ 1) (n k : ℕ) :
    0 ≤ countWeight r n k := by
  have hp : 0 ≤ (1+r)/2 := by linarith [hr.1]
  have hq : 0 ≤ (1-r)/2 := by linarith [hr.2]
  unfold countWeight
  positivity

theorem countWeight_normalized (r : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), countWeight r n k) = 1 := by
  have h := signedMean_const r 1 n
  rw [signedMean_eq_count_sum] at h
  simpa only [mul_one] using h

theorem pair_countWeight_normalized (r s : ℝ) (n : ℕ) :
    (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      countWeight r n a * countWeight s n b) = 1 := by
  simp_rw [← Finset.mul_sum, countWeight_normalized, mul_one]
  exact countWeight_normalized r n

/-- The literal independent-binomial experiment: normalized nonnegative weights,
unbiased quadratic statistic and its exact variance, for the original domain. -/
theorem finite_binomial_quadratic_moments (n : ℕ) (hn : 2 ≤ n) (r s : ℝ)
    (hr : -1 ≤ r ∧ r ≤ 1) (hs : -1 ≤ s ∧ s ≤ 1) :
    (∀ a b : ℕ, 0 ≤ countWeight r n a * countWeight s n b) ∧
    (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      countWeight r n a * countWeight s n b) = 1 ∧
    (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      countWeight r n a * countWeight s n b *
        quadraticStatistic n (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ))) = (r-s)^2 ∧
    (∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1),
      countWeight r n a * countWeight s n b *
        (quadraticStatistic n (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ))-(r-s)^2)^2) =
      4*(r-s)^2*((1-r^2)+(1-s^2))/(n:ℝ) +
      2*((1-r^2)^2+(1-s^2)^2)/((n:ℝ)*((n:ℝ)-1)) +
      4*(1-r^2)*(1-s^2)/(n:ℝ)^2 := by
  refine ⟨?_, pair_countWeight_normalized r s n, ?_⟩
  · intro a b
    exact mul_nonneg (countWeight_nonnegative r hr n a) (countWeight_nonnegative s hs n b)
  · have h := quadratic_mean_variance r s n hn
    rw [pairMean_eq_count_sum, pairMean_eq_count_sum] at h
    exact h

end P1ScalarMoments


namespace FiniteProductMoments

open scoped BigOperators

variable {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]

noncomputable def productWeight (w : J → A → ℝ) (z : J → A) : ℝ := ∏ j, w j (z j)

theorem factor (f : J → A → ℝ) :
    (∑ z : J → A, ∏ j, f j (z j)) = ∏ j, ∑ a, f j a :=
  (Fintype.prod_sum f).symm

theorem normalized (w : J → A → ℝ) (hw : ∀ j, ∑ a, w j a = 1) :
    (∑ z : J → A, productWeight w z) = 1 := by
  unfold productWeight
  rw [factor]
  simp only [hw, Finset.prod_const_one]

theorem nonnegative (w : J → A → ℝ) (hw : ∀ j a, 0 ≤ w j a) (z : J → A) :
    0 ≤ productWeight w z := Finset.prod_nonneg (fun j _ => hw j (z j))

theorem coordinate_mean (w : J → A → ℝ) (hw : ∀ j, ∑ a, w j a = 1)
    (i : J) (f : A → ℝ) :
    (∑ z : J → A, productWeight w z * f (z i)) = ∑ a, w i a*f a := by
  have hleft (z : J → A) :
      (∏ j, w j (z j) * (if j=i then f (z j) else 1)) = productWeight w z*f (z i) := by
    rw [Finset.prod_mul_distrib]
    simp [productWeight]
  have hright (j : J) :
      (∑ a, w j a * (if j=i then f a else 1)) = if j=i then (∑ a, w i a*f a) else 1 := by
    by_cases hji : j=i
    · subst j
      simp
    · simp [hji,hw]
  calc
    _ = ∑ z : J → A, ∏ j, w j (z j)*(if j=i then f (z j) else 1) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hleft z).symm
    _ = _ := by
      rw [factor (fun j a => w j a*(if j=i then f a else 1))]
      simp only [hright]
      simp

theorem two_coordinate_mean (w : J → A → ℝ) (hw : ∀ j, ∑ a, w j a = 1)
    (i j : J) (hij : i ≠ j) (f g : A → ℝ) :
    (∑ z : J → A, productWeight w z * (f (z i)*g (z j))) =
      (∑ a, w i a*f a)*(∑ a, w j a*g a) := by
  have hleft (z : J → A) :
      (∏ k, w k (z k)*((if k=i then f (z k) else 1)*(if k=j then g (z k) else 1))) =
        productWeight w z*(f (z i)*g (z j)) := by
    rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    simp [productWeight]
  have hright (k : J) :
      (∑ a, w k a*((if k=i then f a else 1)*(if k=j then g a else 1))) =
        (if k=i then (∑ a, w i a*f a) else 1)*
        (if k=j then (∑ a, w j a*g a) else 1) := by
    by_cases hki : k=i
    · subst k
      simp [hij]
    · by_cases hkj : k=j
      · subst k
        simp [Ne.symm hij]
      · simp [hki,hkj,hw]
  calc
    _ = ∑ z : J → A, ∏ k, w k (z k)*
        ((if k=i then f (z k) else 1)*(if k=j then g (z k) else 1)) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact (hleft z).symm
    _ = _ := by
      rw [factor (fun k a => w k a*((if k=i then f a else 1)*(if k=j then g a else 1)))]
      simp only [hright,Finset.prod_mul_distrib]
      simp

/-- Explicit finite product law: centered cross terms vanish by factorization,
with no physical independence axiom or probability-space model. -/
theorem sum_mean_and_variance (w u : J → A → ℝ) (d V : J → ℝ)
    (hwnorm : ∀ j, ∑ a, w j a = 1)
    (hmean : ∀ j, ∑ a, w j a*u j a = d j)
    (hvar : ∀ j, ∑ a, w j a*(u j a-d j)^2 = V j) :
    (∑ z : J → A, productWeight w z*(∑ j, u j (z j))) = ∑ j, d j ∧
    (∑ z : J → A, productWeight w z*((∑ j, u j (z j))-(∑ j, d j))^2) =
      ∑ j, V j := by
  let c : J → A → ℝ := fun j a => u j a-d j
  have hc (j : J) : (∑ a, w j a*c j a) = 0 := by
    simp only [c,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hmean,hwnorm,one_mul,sub_self]
  constructor
  · calc
      _ = ∑ j, ∑ z : J → A, productWeight w z*u j (z j) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := by simp only [coordinate_mean w hwnorm,hmean]
  · have hcarg (z : J → A) :
        ((∑ j, u j (z j))-(∑ j, d j))^2 = ∑ i, ∑ j, c i (z i)*c j (z j) := by
      rw [← Finset.sum_sub_distrib,pow_two,Finset.sum_mul_sum]
    calc
      _ = ∑ i, ∑ j, ∑ z : J → A, productWeight w z*(c i (z i)*c j (z j)) := by
        simp_rw [hcarg,Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i : J, ∑ j : J, if i=j then V i else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i=j
        · subst j
          simpa only [ite_true,← pow_two,c] using
            (coordinate_mean w hwnorm i (fun a => (u i a-d i)^2)).trans (hvar i)
        · rw [two_coordinate_mean w hwnorm i j hij, hc, hc]
          simp [hij]
      _ = _ := by simp

end FiniteProductMoments


namespace P1ScalarMoments

open scoped BigOperators

abbrev CountOutcome (n : ℕ) := Fin (n+1) × Fin (n+1)

noncomputable def coordinateWeight (r s : ℝ) (n : ℕ) (a : CountOutcome n) : ℝ :=
  countWeight r n a.1.val * countWeight s n a.2.val

noncomputable def coordinateValue (n : ℕ) (a : CountOutcome n) : ℝ :=
  quadraticStatistic n (2*(a.1.val:ℝ)-(n:ℝ)) (2*(a.2.val:ℝ)-(n:ℝ))

noncomputable def scalarVariance (n : ℕ) (r s : ℝ) : ℝ :=
  4*(r-s)^2*((1-r^2)+(1-s^2))/(n:ℝ) +
  2*((1-r^2)^2+(1-s^2)^2)/((n:ℝ)*((n:ℝ)-1)) +
  4*(1-r^2)*(1-s^2)/(n:ℝ)^2

theorem coordinate_statistics (n : ℕ) (hn : 2 ≤ n) (r s : ℝ)
    (hr : -1 ≤ r ∧ r ≤ 1) (hs : -1 ≤ s ∧ s ≤ 1) :
    (∀ a : CountOutcome n, 0 ≤ coordinateWeight r s n a) ∧
    (∑ a : CountOutcome n, coordinateWeight r s n a) = 1 ∧
    (∑ a : CountOutcome n, coordinateWeight r s n a*coordinateValue n a) = (r-s)^2 ∧
    (∑ a : CountOutcome n, coordinateWeight r s n a*(coordinateValue n a-(r-s)^2)^2) =
      scalarVariance n r s := by
  have h := finite_binomial_quadratic_moments n hn r s hr hs
  refine ⟨fun a => h.1 a.1.val a.2.val, ?_⟩
  have convsum (f : ℕ → ℕ → ℝ) :
      (∑ a : Fin (n+1), ∑ b : Fin (n+1), f a.val b.val) =
        ∑ a ∈ Finset.range (n+1), ∑ b ∈ Finset.range (n+1), f a b := by
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (n+1), f a b.val) (n+1)]
    apply Finset.sum_congr rfl
    intro a ha
    exact Fin.sum_univ_eq_sum_range (fun b => f a b) (n+1)
  change (∑ a : CountOutcome n, countWeight r n a.1.val * countWeight s n a.2.val) = 1 ∧ _
  simp only [Fintype.sum_prod_type,coordinateWeight,coordinateValue,scalarVariance]
  rw [convsum (fun a b => countWeight r n a * countWeight s n b),
    convsum (fun a b => countWeight r n a * countWeight s n b *
      quadraticStatistic n (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ))),
    convsum (fun a b => countWeight r n a * countWeight s n b *
      (quadraticStatistic n (2*(a:ℝ)-(n:ℝ)) (2*(b:ℝ)-(n:ℝ))-(r-s)^2)^2)]
  exact h.2

theorem bounded_scalar_variance (m d v w : ℝ) (hm : 2 ≤ m) (hd : 0 ≤ d)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    4*d*(v+w)/m + 2*(v^2+w^2)/(m*(m-1)) + 4*v*w/m^2 ≤
      8*d/m + 12/m^2 := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hv2 : v^2 ≤ 1 := by nlinarith [mul_nonneg hv.1 (sub_nonneg.mpr hv.2)]
  have hw2 : w^2 ≤ 1 := by nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
  have hvw : v*w ≤ 1 := by
    have h := mul_le_mul hv.2 hw.2 hw.1 (by norm_num : (0:ℝ) ≤ 1)
    simpa only [one_mul] using h
  have hfirst : 4*d*(v+w)/m ≤ 8*d/m :=
    div_le_div_of_nonneg_right (by nlinarith) hm0.le
  have hsecond : 2*(v^2+w^2)/(m*(m-1)) ≤ 8/m^2 := by
    calc
      _ ≤ 4/(m*(m-1)) := div_le_div_of_nonneg_right (by linarith) (mul_pos hm0 hm1).le
      _ ≤ _ := by
        apply (div_le_div_iff₀ (mul_pos hm0 hm1) (pow_pos hm0 2)).mpr
        nlinarith
  have hthird : 4*v*w/m^2 ≤ 4/m^2 :=
    div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg m)
  calc
    _ ≤ 8*d/m + 8/m^2 + 4/m^2 :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by ring

/-- The requested finite product experiment. Physical measurement/product-state
semantics are separate; this theorem uses exactly the displayed product W. -/
theorem finite_product_quadratic_moments {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (hn : 2 ≤ n) (r s : J → ℝ)
    (hr : ∀ j, -1 ≤ r j ∧ r j ≤ 1) (hs : ∀ j, -1 ≤ s j ∧ s j ≤ 1) :
    let W := FiniteProductMoments.productWeight (fun j => coordinateWeight (r j) (s j) n)
    let U := fun z : J → CountOutcome n => ∑ j, coordinateValue n (z j)
    let S := ∑ j, (r j-s j)^2
    (∀ z, 0 ≤ W z) ∧ (∑ z, W z) = 1 ∧
    (∑ z, W z*U z) = S ∧
    (∑ z, W z*(U z-S)^2) = (∑ j, scalarVariance n (r j) (s j)) ∧
    (∑ j, scalarVariance n (r j) (s j)) ≤ 8*S/(n:ℝ)+12*(Fintype.card J:ℝ)/(n:ℝ)^2 := by
  dsimp only
  have hcoord (j : J) := coordinate_statistics n hn (r j) (s j) (hr j) (hs j)
  have hprod := FiniteProductMoments.sum_mean_and_variance
    (fun j => coordinateWeight (r j) (s j) n) (fun _ => coordinateValue n)
    (fun j => (r j-s j)^2) (fun j => scalarVariance n (r j) (s j))
    (fun j => (hcoord j).2.1) (fun j => (hcoord j).2.2.1) (fun j => (hcoord j).2.2.2)
  refine ⟨FiniteProductMoments.nonnegative _ (fun j a => (hcoord j).1 a),
    FiniteProductMoments.normalized _ (fun j => (hcoord j).2.1), hprod.1,hprod.2,?_⟩
  have hb (j : J) : scalarVariance n (r j) (s j) ≤
      8*(r j-s j)^2/(n:ℝ)+12/(n:ℝ)^2 := by
    have hv : 0 ≤ 1-(r j)^2 ∧ 1-(r j)^2 ≤ 1 := by
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hr j).2) (by linarith [(hr j).1] : 0 ≤ 1+r j)]
      · nlinarith [sq_nonneg (r j)]
    have hw : 0 ≤ 1-(s j)^2 ∧ 1-(s j)^2 ≤ 1 := by
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr (hs j).2) (by linarith [(hs j).1] : 0 ≤ 1+s j)]
      · nlinarith [sq_nonneg (s j)]
    exact bounded_scalar_variance (n:ℝ) _ _ _ (by exact_mod_cast hn) (sq_nonneg _) hv hw
  calc
    _ ≤ ∑ j, (8*(r j-s j)^2/(n:ℝ)+12/(n:ℝ)^2) := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by
      simp only [Finset.sum_add_distrib,div_eq_mul_inv,← Finset.sum_mul,← Finset.mul_sum,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end P1ScalarMoments


namespace P1FiniteThreshold

open scoped BigOperators

noncomputable def mass {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (bad : Omega → Prop) [DecidablePred bad] : ℝ :=
  ∑ x ∈ Finset.univ.filter bad, w x

theorem weighted_bad_mass {Omega : Type*} [Fintype Omega]
    (w f : Omega → ℝ) (bad : Omega → Prop) [DecidablePred bad] (b : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hf : ∀ x, 0 ≤ f x)
    (hbad : ∀ x, bad x → b ≤ f x) :
    b * mass w bad ≤ ∑ x, w x*f x := by
  unfold mass
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ x ∈ Finset.univ.filter bad, w x*f x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [mul_comm b (w x)]
      exact mul_le_mul_of_nonneg_left (hbad x (Finset.mem_filter.mp hx).2) (hw x)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => mul_nonneg (hw x) (hf x))

theorem centered_bad_mass {Omega : Type*} [Fintype Omega]
    (w U : Omega → ℝ) (bad : Omega → Prop) [DecidablePred bad] (S b : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hb : 0 < b)
    (hbad : ∀ x, bad x → b ≤ (U x-S)^2) :
    mass w bad ≤ (∑ x, w x*(U x-S)^2)/b := by
  apply (le_div_iff₀ hb).mpr
  rw [mul_comm]
  exact weighted_bad_mass w (fun x => (U x-S)^2) bad b hw (fun x => sq_nonneg _) hbad

theorem sample_budget_bounds (m N a q : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hma : 128 ≤ m*a) (hbudget : 16384*N ≤ (m*a)^2) (haq : a ≤ q) :
    32/(m*q) ≤ 1/4 ∧ 144*N/(m^2*q^2) ≤ 9/1024 := by
  have hq : 0 < q := lt_of_lt_of_le ha haq
  have hmq : 0 < m*q := mul_pos hm hq
  have hcomp : m*a ≤ m*q := mul_le_mul_of_nonneg_left haq hm.le
  have hsq : (m*a)^2 ≤ (m*q)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcomp) (by positivity : 0 ≤ m*q+m*a)]
  constructor
  · apply (div_le_iff₀ hmq).mpr
    linarith
  · apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hm) (sq_pos_of_pos hq))).mpr
    have heq : (m*q)^2 = m^2*q^2 := by ring
    rw [heq] at hsq
    nlinarith

/-- The literal strict-accept/non-strict-reject finite experiment. Physical
Born/product laws, entropy separation and sqrt/ceil copy budgets are separate. -/
theorem finite_threshold_errors {Omega : Type*} [Fintype Omega]
    (w U : Omega → ℝ) (m N : ℕ) (a S : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hnorm : ∑ x, w x = 1)
    (hmean : ∑ x, w x*U x = S)
    (hvar : (∑ x, w x*(U x-S)^2) ≤ 8*S/(m:ℝ)+36*(N:ℝ)/(m:ℝ)^2)
    (hm : 2 ≤ m) (ha : 0 < a) (hma : 128 ≤ (m:ℝ)*a)
    (hbudget : 16384*(N:ℝ) ≤ ((m:ℝ)*a)^2) :
    (S = 0 → mass w (fun x => a/2 ≤ U x) ≤ 9/1024) ∧
    (a ≤ S → mass w (fun x => U x < a/2) ≤ 265/1024) ∧
    (265/1024 : ℝ) < 1/3 := by
  classical
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have ha2 : 0 < (a/2)^2 := sq_pos_of_pos (by linarith)
  refine ⟨?_,?_,by norm_num⟩
  · intro hS
    have hbad := centered_bad_mass w U (fun x => a/2 ≤ U x) S ((a/2)^2) hw ha2 (by
      intro x hx
      rw [hS]
      nlinarith [mul_nonneg (by linarith : 0 ≤ U x-a/2) (by linarith : 0 ≤ U x+a/2)])
    have hb := (sample_budget_bounds (m:ℝ) (N:ℝ) a a hmpos ha hma hbudget le_rfl).2
    calc
      _ ≤ (8*S/(m:ℝ)+36*(N:ℝ)/(m:ℝ)^2)/((a/2)^2) :=
        hbad.trans (div_le_div_of_nonneg_right hvar ha2.le)
      _ = 144*(N:ℝ)/((m:ℝ)^2*a^2) := by rw [hS]; field_simp; ring
      _ ≤ _ := hb
  · intro hSa
    have hSpos : 0 < S := lt_of_lt_of_le ha hSa
    have hS2 : 0 < (S/2)^2 := sq_pos_of_pos (by linarith)
    have hbad := centered_bad_mass w U (fun x => U x < a/2) S ((S/2)^2) hw hS2 (by
      intro x hx
      nlinarith [mul_nonneg (by linarith : 0 ≤ S-U x-S/2)
        (by linarith : 0 ≤ S-U x+S/2)])
    have hb := sample_budget_bounds (m:ℝ) (N:ℝ) a S hmpos ha hma hbudget hSa
    calc
      _ ≤ (8*S/(m:ℝ)+36*(N:ℝ)/(m:ℝ)^2)/((S/2)^2) :=
        hbad.trans (div_le_div_of_nonneg_right hvar hS2.le)
      _ = 32/((m:ℝ)*S)+144*(N:ℝ)/((m:ℝ)^2*S^2) := by
        field_simp [ne_of_gt hmpos,ne_of_gt hSpos]
        ring
      _ ≤ 1/4+9/1024 := add_le_add hb.1 hb.2
      _ = _ := by norm_num

/-- Direct finite assembly for 3N product coordinates. The actual physical
experiment and its 6m total-copy interpretation are still separate suppliers. -/
theorem finite_product_threshold_errors (m N : ℕ) (a : ℝ)
    (r s : Fin (3*N) → ℝ) (hm : 2 ≤ m) (ha : 0 < a)
    (hr : ∀ j, -1 ≤ r j ∧ r j ≤ 1) (hs : ∀ j, -1 ≤ s j ∧ s j ≤ 1)
    (hma : 128 ≤ (m:ℝ)*a) (hbudget : 16384*(N:ℝ) ≤ ((m:ℝ)*a)^2) :
    let W := FiniteProductMoments.productWeight
      (fun j => P1ScalarMoments.coordinateWeight (r j) (s j) m)
    let U := fun z : Fin (3*N) → P1ScalarMoments.CountOutcome m =>
      ∑ j, P1ScalarMoments.coordinateValue m (z j)
    let S := ∑ j, (r j-s j)^2
    (S = 0 → mass W (fun z => a/2 ≤ U z) ≤ 9/1024) ∧
    (a ≤ S → mass W (fun z => U z < a/2) ≤ 265/1024) ∧
    (265/1024 : ℝ) < 1/3 := by
  dsimp only
  have h := P1ScalarMoments.finite_product_quadratic_moments m hm r s hr hs
  dsimp only at h
  apply finite_threshold_errors _ _ m N a _ h.1 h.2.1 h.2.2.1 _ hm ha hma hbudget
  rw [h.2.2.2.1]
  calc
    _ ≤ _ := h.2.2.2.2
    _ = _ := by simp only [Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]; ring

end P1FiniteThreshold
