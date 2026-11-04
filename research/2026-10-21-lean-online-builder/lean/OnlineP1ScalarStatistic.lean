import Mathlib.Tactic.FieldSimp
import Mathlib.Basic.Real.Basic
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
