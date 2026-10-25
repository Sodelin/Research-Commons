import SocialScience.Identifiability

namespace SocialScience.Measurement

/-- An illustrative additive indicator, in integer score units. -/
def response (latent intercept : Int) : Int := latent + intercept

theorem common_intercept_preserves_order (a b intercept : Int) :
    response a intercept ≤ response b intercept ↔ a ≤ b := by
  simp only [response]
  omega

theorem common_intercept_preserves_difference (a b intercept : Int) :
    response a intercept - response b intercept = a - b := by
  simp only [response]
  omega

theorem shift_invariance (latent intercept shift : Int) :
    response (latent + shift) (intercept - shift) = response latent intercept := by
  simp only [response]
  omega

theorem population_shift_invariance {Person : Type} (latent : Person → Int)
    (intercept shift : Int) :
    (fun p => response (latent p + shift) (intercept - shift)) =
      (fun p => response (latent p) intercept) := by
  funext p
  exact shift_invariance (latent p) intercept shift

theorem known_intercept_identifies (a b intercept : Int)
    (same : response a intercept = response b intercept) : a = b := by
  simp only [response] at same
  omega

theorem anchor_identifies_intercept (anchor first second : Int)
    (same : response anchor first = response anchor second) : first = second := by
  simp only [response] at same
  omega

/-- Unequal intercepts can reverse a latent ordering. This is a synthetic witness. -/
theorem group_intercepts_can_reverse_order :
    (0 : Int) < 1 ∧ response 1 0 < response 0 2 := by decide

/-- An assumed bound on differential bias yields a bound on the latent difference. -/
theorem bounded_bias_interval (a b biasA biasB δ : Int)
    (lower : -δ ≤ biasA - biasB) (upper : biasA - biasB ≤ δ) :
    (response a biasA - response b biasB) - δ ≤ a - b ∧
    a - b ≤ (response a biasA - response b biasB) + δ := by
  simp only [response]
  omega

theorem difference_exceeding_bias_identifies_order (a b biasA biasB δ : Int)
    (upper : biasA - biasB ≤ δ)
    (gap : δ < response a biasA - response b biasB) : b < a := by
  simp only [response] at gap
  omega

end SocialScience.Measurement
