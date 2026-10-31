import MSCi.TwoSite.ABOrderingDraft

/-!
Uncompiled candidate assembly of the global AB two-moment argument.

The proof follows the ordered-onset single-crossing route for the transcribed
analytic moments. It composes uncompiled candidates for the survival identity,
rate order, root-tail integral and fixed-onset monotonicity. This file does not
construct the six-sample process, prove the JC observation bridge, identify the
tied B rate or establish the Jacobian and interval claims.
-/

noncomputable section

namespace MSCi.TwoSite

/-- Two shifted formula moments force the AB onsets to agree. -/
theorem ab_onset_eq_of_two_shifted_moments (T R r₁ r₂ c a₁ a₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (h₁T : a₁ < T) (h₂T : a₂ < T)
    (hR : 0 < R) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hc : 0 < c)
    (hfirst : pulseShiftedMoment T R r₁ c a₁ = pulseShiftedMoment T R r₂ c a₂)
    (hsecond : pulseShiftedMoment T R r₁ (2 * c) a₁ =
      pulseShiftedMoment T R r₂ (2 * c) a₂) : a₁ = a₂ := by
  have h2c : 0 < 2 * c := by positivity
  rcases lt_trichotomy a₁ a₂ with hlt | heq | hgt
  · have hzero₁ := ab_equal_shifted_moment_implies_zero_weight T R r₁ r₂ c a₁ a₂
      ha₁ ha₂ (le_of_lt h₁T) (le_of_lt h₂T) hR hr₁ hr₂ hc hfirst
    have hrr := ab_earlier_rate_lt_of_zero_weight a₁ r₁ a₂ r₂ T R c
      ha₁ hlt h₂T hr₁ hr₂ hR hc hzero₁
    have hsT := ab_crossing_before_root_of_zero_weight a₁ r₁ a₂ r₂ T R c
      ha₁ hlt h₂T hr₁ hrr hR hc hzero₁
    have hneg := ab_ordered_crossing_separates a₁ r₁ a₂ r₂ T R c
      ha₁ hlt hr₁ hrr hR hc hsT hzero₁
    have hzero₂ := ab_equal_shifted_moment_implies_zero_weight T R r₁ r₂ (2 * c) a₁ a₂
      ha₁ ha₂ (le_of_lt h₁T) (le_of_lt h₂T) hR hr₁ hr₂ h2c hsecond
    linarith
  · exact heq
  · have hzero₁ := ab_equal_shifted_moment_implies_zero_weight T R r₂ r₁ c a₂ a₁
      ha₂ ha₁ (le_of_lt h₂T) (le_of_lt h₁T) hR hr₂ hr₁ hc hfirst.symm
    have hrr := ab_earlier_rate_lt_of_zero_weight a₂ r₂ a₁ r₁ T R c
      ha₂ hgt h₁T hr₂ hr₁ hR hc hzero₁
    have hsT := ab_crossing_before_root_of_zero_weight a₂ r₂ a₁ r₁ T R c
      ha₂ hgt h₁T hr₂ hrr hR hc hzero₁
    have hneg := ab_ordered_crossing_separates a₂ r₂ a₁ r₁ T R c
      ha₂ hgt hr₂ hrr hR hc hsT hzero₁
    have hzero₂ := ab_equal_shifted_moment_implies_zero_weight T R r₂ r₁ (2 * c) a₂ a₁
      ha₂ ha₁ (le_of_lt h₂T) (le_of_lt h₁T) hR hr₂ hr₁ h2c hsecond.symm
    linarith

/-- Two shifted formula moments force both onset and ancestral rate to agree. -/
theorem ab_onset_rate_eq_of_two_shifted_moments (T R r₁ r₂ c a₁ a₂ : ℝ)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (h₁T : a₁ < T) (h₂T : a₂ < T)
    (hR : 0 < R) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hc : 0 < c)
    (hfirst : pulseShiftedMoment T R r₁ c a₁ = pulseShiftedMoment T R r₂ c a₂)
    (hsecond : pulseShiftedMoment T R r₁ (2 * c) a₁ =
      pulseShiftedMoment T R r₂ (2 * c) a₂) : a₁ = a₂ ∧ r₁ = r₂ := by
  have ha := ab_onset_eq_of_two_shifted_moments T R r₁ r₂ c a₁ a₂
    ha₁ ha₂ h₁T h₂T hR hr₁ hr₂ hc hfirst hsecond
  have hfirst' : pulseShiftedMoment T R r₁ c a₁ = pulseShiftedMoment T R r₂ c a₁ := by
    simpa [← ha] using hfirst
  exact ⟨ha, ab_rate_eq_at_fixed_onset T R r₁ r₂ c a₁ hR hr₁ hr₂ hc h₁T hfirst'⟩

/-- Candidate AB parameter recovery from equality of the nine formula features. -/
theorem ab_parameters_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p.t1 = q.t1 ∧ p.rAB = q.rAB := by
  have ht := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hmom := ab_shifted_moments_eq_of_nineRawFeatures_eq p q hp hq hF
  rw [← ht, ← hR] at hmom
  have hp₀ : 0 ≤ p.t1 := le_of_lt (lt_trans hp.1 hp.2.1)
  have hq₀ : 0 ≤ q.t1 := le_of_lt (lt_trans hq.1 hq.2.1)
  have hpT : p.t1 < p.t0 := hp.2.2.1
  have hqT : q.t1 < p.t0 := by simpa [ht] using hq.2.2.1
  have hpR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hpR⟩; exact hpR
  have hpr : 0 < p.rAB := by rcases hp with ⟨_, _, _, _, _, _, _, _, hpr, _⟩; exact hpr
  have hqr : 0 < q.rAB := by rcases hq with ⟨_, _, _, _, _, _, _, _, hqr, _⟩; exact hqr
  have hc : 0 < jcPairExponent := by norm_num [jcPairExponent]
  exact ab_onset_rate_eq_of_two_shifted_moments p.t0 p.rR p.rAB q.rAB jcPairExponent p.t1 q.t1
    hp₀ hq₀ hpT hqT hpR hpr hqr hc hmom.1 hmom.2

/-- Candidate composition with the A-rate fixed-continuation step. -/
theorem a_and_ab_parameters_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) :
    p.t1 = q.t1 ∧ p.rAB = q.rAB ∧ p.rA = q.rA := by
  have hAB := ab_parameters_eq_of_nineRawFeatures_eq p q hp hq hF
  exact ⟨hAB.1, hAB.2, a_rate_eq_of_nineRawFeatures_eq p q hp hq hF hAB.1 hAB.2⟩

end MSCi.TwoSite
