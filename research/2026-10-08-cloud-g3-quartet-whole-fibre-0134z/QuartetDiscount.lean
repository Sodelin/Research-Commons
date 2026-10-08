import Mathlib.Tactic

/-!
UNCHECKED scalar accompaniment to the original-quartet whole-fibre hand candidate.
These statements prove only discounted composition/strictness. They do not
formalize source admission, the quartet provider, RCF minimization or extraction.
No compiler was invoked for this file.
-/

namespace CloudG3.QuartetDiscount

theorem lower_comp (m c₁ c₂ t₁ t₂ : ℝ)
    (hc₁ : 0 ≤ c₁)
    (h₁ : m * (1 - c₁) ≤ t₁)
    (h₂ : m * (1 - c₂) ≤ t₂) :
    m * (1 - c₁ * c₂) ≤ t₁ + c₁ * t₂ := by
  have hmul := mul_le_mul_of_nonneg_left h₂ hc₁
  nlinarith

theorem upper_comp (M c₁ c₂ t₁ t₂ : ℝ)
    (hc₁ : 0 ≤ c₁)
    (h₁ : t₁ ≤ M * (1 - c₁))
    (h₂ : t₂ ≤ M * (1 - c₂)) :
    t₁ + c₁ * t₂ ≤ M * (1 - c₁ * c₂) := by
  have hmul := mul_le_mul_of_nonneg_left h₂ hc₁
  nlinarith

theorem lower_strict (m c t : ℝ) (hm : m < 0) (hc : 0 < c)
    (h : m * (1 - c) ≤ t) : m < t := by
  nlinarith

theorem upper_strict (M c t : ℝ) (hM : 0 < M) (hc : 0 < c)
    (h : t ≤ M * (1 - c)) : t < M := by
  nlinarith

end CloudG3.QuartetDiscount
