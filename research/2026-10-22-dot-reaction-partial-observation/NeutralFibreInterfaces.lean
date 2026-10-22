import Mathlib

/-!
Author: dot (OpenAI), 22 October 2026.

UNCOMPILED SOURCE PROPOSAL. No Lean invocation or axiom audit has occurred.

The real-algebra proofs below are proposed tactic scripts, not verified results.
The full stochastic assertion is conditional on the explicit PhysicalBridge.
That bridge has NO implementation here. Its fields are substantial outstanding
proof obligations, not established axioms of a physical model. In particular,
an arbitrary function called `observe` is not a reaction-diffusion law.

The hand manuscript NEUTRAL-THREE-SPECIES-OBSERVATION-FIBRE.md gives the complete
mathematical argument and separately attributed hand review. Classical bracket
observability and two-node moment inversion remain prior methods. The optional
five-moment Commons supplier is not needed by this known-family algebra.
-/

namespace ResearchCommons.ReactionPartialObservation.Neutral

structure Initial where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  c_pos : 0 < c

def total (I : Initial) : ℝ := I.a + I.b + I.c

/-- The SAME fixed initial point is used for every rival in an experiment. -/
structure Experiment (I : Initial) where
  lower : ℝ
  upper : ℝ
  horizon : ℝ
  lower_pos : 0 < lower
  starts_above : lower < I.a
  starts_below : I.a < upper
  upper_lt_total : upper < total I
  horizon_pos : 0 < horizon

/-- Opposite directions have rates p/2, q/2 and r/2 respectively.
The hidden pair is absent exactly when r=0. No other channels are admitted. -/
structure Rates where
  p : ℝ
  q : ℝ
  r : ℝ
  p_pos : 0 < p
  q_pos : 0 < q
  r_nonneg : 0 ≤ r

def moment (b c p q : ℝ) (j : ℕ) : ℝ := b * p ^ j + c * q ^ j

def mu (I : Initial) (θ : Rates) (j : ℕ) : ℝ :=
  moment I.b I.c θ.p θ.q j

def determinant (I : Initial) (θ : Rates) : ℝ :=
  I.b * I.c * (θ.p - θ.q) ^ 2

def bracketVariance (I : Initial) (θ : Rates) : ℝ :=
  I.a * mu I θ 3 + θ.r * determinant I θ

/-- Equality of the four deterministically recovered initial bracket data.
The zeroth moment is already fixed by the common initial condition. -/
def DataEq (I : Initial) (θ η : Rates) : Prop :=
  mu I θ 1 = mu I η 1 ∧
  mu I θ 2 = mu I η 2 ∧
  mu I θ 3 = mu I η 3 ∧
  bracketVariance I θ = bracketVariance I η

/-- Exact target fibre, including balance, r=0 and equal-mass label swapping. -/
def Fibre (I : Initial) (θ η : Rates) : Prop :=
  (θ.p = θ.q ∧ η.p = θ.p ∧ η.q = θ.p) ∨
  (θ.p ≠ θ.q ∧ η.r = θ.r ∧
    ((η.p = θ.p ∧ η.q = θ.q) ∨
      (I.b = I.c ∧ η.p = θ.q ∧ η.q = θ.p)))

theorem determinant_identity (b c p q : ℝ) :
    (b + c) * moment b c p q 2 - (moment b c p q 1) ^ 2 =
      b * c * (p - q) ^ 2 := by
  unfold moment
  ring

theorem positive_determinant (I : Initial) (θ : Rates) (h : θ.p ≠ θ.q) :
    0 < determinant I θ := by
  unfold determinant
  exact mul_pos (mul_pos I.b_pos I.c_pos)
    (sq_pos_of_ne_zero (sub_ne_zero.mpr h))

theorem equal_moments_sum_product
    (b c p q u v : ℝ) (hb : 0 < b) (hc : 0 < c) (hpq : p ≠ q)
    (h1 : moment b c p q 1 = moment b c u v 1)
    (h2 : moment b c p q 2 = moment b c u v 2)
    (h3 : moment b c p q 3 = moment b c u v 3) :
    p + q = u + v ∧ p * q = u * v := by
  let D := (b + c) * moment b c p q 2 - (moment b c p q 1) ^ 2
  have hDpos : 0 < D := by
    dsimp [D]
    rw [determinant_identity]
    exact mul_pos (mul_pos hb hc)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hpq))
  have hs : D * (p + q) = D * (u + v) := by
    calc
      D * (p + q) = (b + c) * moment b c p q 3 -
          moment b c p q 1 * moment b c p q 2 := by
        dsimp [D, moment]
        ring
      _ = (b + c) * moment b c u v 3 -
          moment b c u v 1 * moment b c u v 2 := by rw [h1, h2, h3]
      _ = ((b + c) * moment b c u v 2 -
          (moment b c u v 1) ^ 2) * (u + v) := by
        unfold moment
        ring
      _ = D * (u + v) := by rw [← h1, ← h2]
  have ht : D * (p * q) = D * (u * v) := by
    calc
      D * (p * q) = moment b c p q 1 * moment b c p q 3 -
          (moment b c p q 2) ^ 2 := by
        dsimp [D, moment]
        ring
      _ = moment b c u v 1 * moment b c u v 3 -
          (moment b c u v 2) ^ 2 := by rw [h1, h2, h3]
      _ = ((b + c) * moment b c u v 2 -
          (moment b c u v 1) ^ 2) * (u * v) := by
        unfold moment
        ring
      _ = D * (u * v) := by rw [← h1, ← h2]
  exact ⟨mul_left_cancel₀ (ne_of_gt hDpos) hs,
    mul_left_cancel₀ (ne_of_gt hDpos) ht⟩

theorem roots_from_sum_product (p q u v : ℝ)
    (hs : p + q = u + v) (ht : p * q = u * v) :
    (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
  have hv : v = p + q - u := by linarith
  rw [hv] at ht
  have hroot : (u - p) * (u - q) = 0 := by nlinarith [ht]
  rcases mul_eq_zero.mp hroot with h | h
  · left
    constructor <;> linarith
  · right
    constructor <;> linarith

theorem equal_moments_balanced
    (b c p u v : ℝ) (hb : 0 < b) (hc : 0 < c)
    (h1 : moment b c p p 1 = moment b c u v 1)
    (h2 : moment b c p p 2 = moment b c u v 2) :
    u = p ∧ v = p := by
  have hscaled := congrArg (fun z : ℝ => 2 * p * z) h1
  have hcenter : b * (u - p) ^ 2 + c * (v - p) ^ 2 = 0 := by
    unfold moment at hscaled h2
    norm_num only [pow_one] at hscaled
    nlinarith [hscaled, h2]
  have hu_nonneg : 0 ≤ b * (u - p) ^ 2 :=
    mul_nonneg (le_of_lt hb) (sq_nonneg _)
  have hv_nonneg : 0 ≤ c * (v - p) ^ 2 :=
    mul_nonneg (le_of_lt hc) (sq_nonneg _)
  have hu0 : b * (u - p) ^ 2 = 0 := by linarith
  have hv0 : c * (v - p) ^ 2 = 0 := by linarith
  have hu2 : (u - p) ^ 2 = 0 :=
    (mul_eq_zero.mp hu0).resolve_left (ne_of_gt hb)
  have hv2 : (v - p) ^ 2 = 0 :=
    (mul_eq_zero.mp hv0).resolve_left (ne_of_gt hc)
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hu2),
    sub_eq_zero.mp (sq_eq_zero_iff.mp hv2)⟩

/-- Complete proposed algebraic necessity, not a stochastic-law theorem. -/
theorem data_implies_fibre (I : Initial) (θ η : Rates) (h : DataEq I θ η) :
    Fibre I θ η := by
  rcases h with ⟨h1, h2, h3, hν⟩
  by_cases hpq : θ.p = θ.q
  · left
    have hm1 : moment I.b I.c θ.p θ.p 1 =
        moment I.b I.c η.p η.q 1 := by
      simpa only [mu, ← hpq] using h1
    have hm2 : moment I.b I.c θ.p θ.p 2 =
        moment I.b I.c η.p η.q 2 := by
      simpa only [mu, ← hpq] using h2
    exact ⟨hpq, equal_moments_balanced I.b I.c θ.p η.p η.q
      I.b_pos I.c_pos hm1 hm2⟩
  · right
    have hDpos := positive_determinant I θ hpq
    have hDeq : determinant I η = determinant I θ := by
      calc
        determinant I η = (I.b + I.c) * mu I η 2 - (mu I η 1) ^ 2 := by
          exact (determinant_identity I.b I.c η.p η.q).symm
        _ = (I.b + I.c) * mu I θ 2 - (mu I θ 1) ^ 2 := by rw [← h1, ← h2]
        _ = determinant I θ := determinant_identity I.b I.c θ.p θ.q
    have hν' : I.a * mu I θ 3 + θ.r * determinant I θ =
        I.a * mu I θ 3 + η.r * determinant I θ := by
      simpa only [bracketVariance, hDeq, ← h3] using hν
    have hrmul : θ.r * determinant I θ = η.r * determinant I θ := by
      linarith
    have hr : η.r = θ.r :=
      (mul_right_cancel₀ (ne_of_gt hDpos) hrmul).symm
    have hst := equal_moments_sum_product I.b I.c θ.p θ.q η.p η.q
      I.b_pos I.c_pos hpq h1 h2 h3
    have hroots := roots_from_sum_product θ.p θ.q η.p η.q hst.1 hst.2
    refine ⟨hpq, hr, ?_⟩
    rcases hroots with hid | hswap
    · exact Or.inl hid
    · right
      have hlabel : (I.b - I.c) * (θ.p - θ.q) = 0 := by
        dsimp [mu, moment] at h1
        rw [hswap.1, hswap.2] at h1
        norm_num only [pow_one] at h1
        nlinarith [h1]
      have hbc : I.b = I.c := sub_eq_zero.mp
        ((mul_eq_zero.mp hlabel).resolve_right (sub_ne_zero.mpr hpq))
      exact ⟨hbc, hswap⟩

/-
UNIMPLEMENTED PHYSICAL PROVIDER, with explicit one-experiment scope.

For the required instance, `observe θ` must be the probability measure on
C([0,E.horizon], R) of A, started at I, continued at absorbing zero faces,
stopped on leaving (E.lower,E.upper), and then held. No hidden-dependent exit
is substituted; no initial-state panel is used; no projected Markov property
is assumed. Positivity of p,q and nonnegativity of r come from Rates.

`extract_initial_data` requires an actual measurable recursive bracket
construction, common-law/null-set handling, division by the surviving A,
left-limit continuation at the observable stop, right limits at time zero,
and [M1]'(0)=a0*mu3+r*b0*c0*(p-q)^2.

The sufficiency fields require well-posedness of the global absorbing-face
model, scalar martingale-problem uniqueness in the balanced case, and the
initial-state-preserving B/C permutation in the equal-mass case. None of
these fields follows from the real-algebra lemmas above.
-/
structure PhysicalBridge (I : Initial) (E : Experiment I) (Law : Type*) where
  observe : Rates → Law
  extract_initial_data : ∀ θ η, observe θ = observe η → DataEq I θ η
  same_rates : ∀ θ η,
    η.p = θ.p → η.q = θ.q → η.r = θ.r → observe θ = observe η
  balanced : ∀ θ η,
    θ.p = θ.q → η.p = θ.p → η.q = θ.p → observe θ = observe η
  equal_mass_swap : ∀ θ η,
    I.b = I.c → η.p = θ.q → η.q = θ.p → η.r = θ.r →
      observe θ = observe η

/-- Full target, conditional on ALL physical provider obligations above.
Even future compilation would certify only this conditional theorem unless
a concrete physical provider is separately constructed and checked. -/
theorem observation_eq_iff_fibre_conditionally
    {I : Initial} {E : Experiment I} {Law : Type*}
    (P : PhysicalBridge I E Law) (θ η : Rates) :
    P.observe θ = P.observe η ↔ Fibre I θ η := by
  constructor
  · intro h
    exact data_implies_fibre I θ η (P.extract_initial_data θ η h)
  · intro h
    rcases h with hbalanced | hunbalanced
    · exact P.balanced θ η hbalanced.1 hbalanced.2.1 hbalanced.2.2
    · rcases hunbalanced with ⟨_, hr, hid | hswap⟩
      · exact P.same_rates θ η hid.1 hid.2 hr
      · exact P.equal_mass_swap θ η hswap.1 hswap.2.1 hswap.2.2 hr

def covarianceAA (I : Initial) (θ : Rates) : ℝ :=
  I.a * (θ.p * I.b + θ.q * I.c)

def covarianceAB (I : Initial) (θ : Rates) : ℝ := -θ.p * I.a * I.b

def covarianceBB (I : Initial) (θ : Rates) : ℝ :=
  θ.p * I.a * I.b + θ.r * I.b * I.c

/-- Proposed algebra for the added labeled B observation, including balance.
Extraction of these entries from a physical joint A,B-law is not proved here. -/
theorem initial_joint_covariance_identifies (I : Initial) (θ η : Rates)
    (haa : covarianceAA I θ = covarianceAA I η)
    (hab : covarianceAB I θ = covarianceAB I η)
    (hbb : covarianceBB I θ = covarianceBB I η) :
    θ.p = η.p ∧ θ.q = η.q ∧ θ.r = η.r := by
  have hp_mul : θ.p * (I.a * I.b) = η.p * (I.a * I.b) := by
    unfold covarianceAB at hab
    nlinarith [hab]
  have hp : θ.p = η.p :=
    mul_right_cancel₀ (ne_of_gt (mul_pos I.a_pos I.b_pos)) hp_mul
  have hq_mul : θ.q * (I.a * I.c) = η.q * (I.a * I.c) := by
    unfold covarianceAA at haa
    rw [hp] at haa
    nlinarith [haa]
  have hq : θ.q = η.q :=
    mul_right_cancel₀ (ne_of_gt (mul_pos I.a_pos I.c_pos)) hq_mul
  have hr_mul : θ.r * (I.b * I.c) = η.r * (I.b * I.c) := by
    unfold covarianceBB at hbb
    rw [hp] at hbb
    nlinarith [hbb]
  have hr : θ.r = η.r :=
    mul_right_cancel₀ (ne_of_gt (mul_pos I.b_pos I.c_pos)) hr_mul
  exact ⟨hp, hq, hr⟩

end ResearchCommons.ReactionPartialObservation.Neutral
