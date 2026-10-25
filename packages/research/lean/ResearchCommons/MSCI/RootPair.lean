import ExponentialClockMoments
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Formal use-site of the already proved two-site/nine-feature theorem, Section 3.
This proves the actual shifted-exponential pair subproblem, not the complete
six-copy pulse family, the nine-feature Jacobian, or a numerical inverse.
The actual whole-source AC-pair/sequence-character correspondence is separate.
No new identifiability principle or empirical accuracy claim is asserted.
-/
noncomputable section
set_option autoImplicit false
namespace ResearchCommons.MSCI.RootPair

open MeasureTheory ProbabilityTheory

/-- Actual Laplace mean of an onset plus an exponential waiting time.
The harmless positive-part extension agrees with the actual waiting time
almost surely under expMeasure; it reuses the existing integral supplier. -/
def moment (c onset rate : ℝ) : ℝ :=
  ∫ x, Real.exp (-c * (onset + max 0 x)) ∂expMeasure rate

theorem moment_formula {c onset rate : ℝ} (hc : 0 < c) (hr : 0 < rate) :
    moment c onset rate = Real.exp (-c * onset) * rate / (rate + c) := by
  unfold moment
  calc
    (∫ x, Real.exp (-c * (onset + max 0 x)) ∂expMeasure rate) =
        ∫ x, Real.exp (-c * onset) * Real.exp ((-c) * max 0 x)
          ∂expMeasure rate := by
      congr 1
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (-c * onset) * rate / (rate + c) := by
      rw [integral_const_mul,
        GProgram.Kingman.ClockMoments.exponential_positivePart_integral hr
          (by linarith : -c < rate)]
      simp only [sub_neg_eq_add]
      ring

/-- The two literal root-pair rational moments determine their common positive
survival factor and rate. Neither a square-root oracle nor a rate separation
assumption is used. -/
theorem scaled_moments_injective {c b b' r r' : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hb' : 0 < b')
    (hr : 0 < r) (hr' : 0 < r')
    (hfirst : b*r/(r+c) = b'*r'/(r'+c))
    (hsecond : b^2*r/(r+2*c) = b'^2*r'/(r'+2*c)) :
    b = b' ∧ r = r' := by
  have ratio (v a : ℝ) (hv : 0 < v) (ha : 0 < a) :
      (v^2*a/(a+2*c)) / (v*a/(a+c))^2 =
        (a+c)^2 / (a*(a+2*c)) := by
    have h1 : a+c ≠ 0 := ne_of_gt (by positivity)
    have h2 : a+2*c ≠ 0 := ne_of_gt (by positivity)
    field_simp [hv.ne', ha.ne', h1, h2] <;> ring
  have hq : (r+c)^2/(r*(r+2*c)) = (r'+c)^2/(r'*(r'+2*c)) := by
    rw [← ratio b r hb hr, ← ratio b' r' hb' hr', hfirst, hsecond]
  have hd : r*(r+2*c) ≠ 0 := ne_of_gt (by positivity)
  have hd' : r'*(r'+2*c) ≠ 0 := ne_of_gt (by positivity)
  have hcross := (div_eq_div_iff hd hd').mp hq
  have hprod : (r-r')*(r+r'+2*c)*c^2 = 0 := by nlinarith [hcross]
  have hz : (r-r')*(r+r'+2*c) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (pow_ne_zero 2 hc.ne')
  have hsum : r+r'+2*c ≠ 0 := ne_of_gt (by positivity)
  have heq : r = r' := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hsum)
  subst r'
  have hden : r+c ≠ 0 := ne_of_gt (by positivity)
  have hbprod : b*r = b'*r := (div_left_inj' hden).mp hfirst
  exact ⟨mul_right_cancel₀ hr.ne' hbprod, rfl⟩

/-- Two actual pair means identify the onset and rate globally at fixed c>0.
The onset may be any real value; in the original source it is strictly positive.
This is only the root-pair step of the completed nine-parameter hand theorem. -/
theorem moments_injective {c t t' r r' : ℝ}
    (hc : 0 < c) (hr : 0 < r) (hr' : 0 < r')
    (hfirst : moment c t r = moment c t' r')
    (hsecond : moment (2*c) t r = moment (2*c) t' r') :
    t = t' ∧ r = r' := by
  have hexp (a : ℝ) : Real.exp (-(2*c)*a) = Real.exp (-c*a)^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [moment_formula hc hr, moment_formula hc hr'] at hfirst
  rw [moment_formula (by positivity : 0 < 2*c) hr,
    moment_formula (by positivity : 0 < 2*c) hr', hexp t, hexp t'] at hsecond
  obtain ⟨hbeta, hrate⟩ := scaled_moments_injective hc
    (Real.exp_pos _) (Real.exp_pos _) hr hr' hfirst hsecond
  have ht : -c*t = -c*t' := Real.exp_injective hbeta
  exact ⟨mul_left_cancel₀ (neg_ne_zero.mpr hc.ne') ht, hrate⟩

end ResearchCommons.MSCI.RootPair
