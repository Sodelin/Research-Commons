import G4StrictMargin

/-!
# Conditional preservation of a distinguishing value

Contributor: Codex delegated margin extension, 14 October 2026.
Status: UNCOMPILED source draft.

This extends the forward strict-margin implication of Astra's
`ALGEBRAIC-JET-THEOREM.md`, section 4, to preserve `h z ≠ 0` on the SAME
corrected zero. The external error bound, nearby-zero existence, and the
Lipschitz/value-error adapter are explicit premises. There is no claim of
algebraic coefficient replacement, Nash curve selection, or a G4 construction.

Only `G4StrictMargin` is imported. Its frozen source SHA256 is
`a78e639389a08a5d9ab384956d82d4f650cc23842208dde2b978b4a8fcc5fdb4`.
Its narrow arithmetic tactic imports supply the tactics used below.
-/

namespace G4DistinctMargin

open G4StrictMargin

/-- A correction with value error below a positive absolute-value margin
cannot make the corrected value zero. -/
theorem nonzero_of_value_error {u v η E : ℝ}
    (positiveMargin : 0 < η) (valueMargin : η ≤ |u|)
    (closeValue : |v - u| ≤ E) (errorBelowMargin : E < η) : v ≠ 0 := by
  intro hv
  rw [hv, zero_sub, abs_neg] at closeValue
  linarith

/-- Scaling an external radius bound by a nonnegative Lipschitz constant.
This is arithmetic; existence of a Lipschitz constant is not assumed proved. -/
theorem scaled_external_error_bound {e L C residual : ℝ} {R : ℕ}
    (hL : 0 ≤ L) (externalErrorBound : e ^ R ≤ C * residual) :
    (L * e) ^ R ≤ (L ^ R * C) * residual := by
  calc
    (L * e) ^ R = L ^ R * e ^ R := mul_pow L e R
    _ ≤ L ^ R * (C * residual) := mul_le_mul_of_nonneg_left
      externalErrorBound (pow_nonneg hL R)
    _ = (L ^ R * C) * residual := by ring

/-- The maximum-order gap supplies both the domain and value-order gaps. -/
theorem component_order_gaps {r s R q : ℕ}
    (exponentGap : max r s * R < q) : r * R < q ∧ s * R < q := by
  constructor
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right R (Nat.le_max_left r s)) exponentGap
  · exact lt_of_le_of_lt (Nat.mul_le_mul_right R (Nat.le_max_right r s)) exponentGap

/-- A pointwise whole-vector zero preserves both strict coordinates and a
specified nonzero distinction. The tuple is chosen ONCE from `nearbyZero`.
`lipschitzAdapter` controls value error; it does not assume nonvanishing. -/
theorem exists_strict_distinct_zero_of_power_error_bound
    {ι β : Type*} [Zero β] (F : (ι → ℝ) → β) (h : (ι → ℝ) → ℝ)
    (residual : β → ℝ) {p : ι → ℝ} {t c₀ c₁ e C B L : ℝ} {r s R q : ℕ}
    (ht : 0 < t) (htOne : t ≤ 1) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (exponentGap : max r s * R < q)
    (margin : CoordinateMargin p (c₀ * t ^ r))
    (distinctionMargin : c₁ * t ^ s ≤ |h p|)
    (externalErrorBound : e ^ R ≤ C * residual (F p))
    (residualBound : residual (F p) ≤ B * t ^ q)
    (nearbyZero : ∃ z, F z = 0 ∧ CoordinateError p z e)
    (lipschitzAdapter : ∀ z, CoordinateError p z e → |h z - h p| ≤ L * e)
    (smallDomainParameter : C * B * t < c₀ ^ R)
    (smallValueParameter : (L ^ R * C) * B * t < c₁ ^ R) :
    ∃ z, F z = 0 ∧ StrictCube z ∧ h z ≠ 0 := by
  obtain ⟨hrGap, hsGap⟩ := component_order_gaps exponentGap
  have hRadius : e < c₀ * t ^ r := error_lt_power_margin ht htOne hc₀ hC hB
    hrGap externalErrorBound residualBound smallDomainParameter
  have hScaledC : 0 ≤ L ^ R * C := mul_nonneg (pow_nonneg hL R) hC
  have hValueRadius : L * e < c₁ * t ^ s := error_lt_power_margin ht htOne hc₁
    hScaledC hB hsGap (scaled_external_error_bound hL externalErrorBound)
    residualBound smallValueParameter
  obtain ⟨z, hz, hcoord⟩ := nearbyZero
  refine ⟨z, hz, strictCube_of_coordinateMargin margin hcoord hRadius, ?_⟩
  exact nonzero_of_value_error (mul_pos hc₁ (pow_pos ht s)) distinctionMargin
    (lipschitzAdapter z hcoord) hValueRadius

/-- Natural-order eventual strict exactification with a nonzero distinction
on the SAME tuple. All complete residual equations are expressed by `F z = 0`.

Both small-parameter conditions are proved from positive cutoffs, rather than
assumed for every parameter. The supplied Lipschitz/value-error adapter may be
local; it is only required for the indicated radius about the supplied curve.
The architecture and coordinate type remain fixed. -/
theorem eventually_exists_strict_distinct_zero_of_order_gap
    {ι β : Type*} [Zero β] (F : (ι → ℝ) → β) (h : (ι → ℝ) → ℝ)
    (residual : β → ℝ) (p : ℝ → (ι → ℝ)) (e : ℝ → ℝ)
    {a c₀ c₁ C B L : ℝ} {r s R q : ℕ}
    (ha : 0 < a) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (exponentGap : max r s * R < q)
    (margin : ∀ t, 0 < t → t < a → CoordinateMargin (p t) (c₀ * t ^ r))
    (distinctionMargin : ∀ t, 0 < t → t < a → c₁ * t ^ s ≤ |h (p t)|)
    (externalErrorBound : ∀ t, 0 < t → t < a →
      e t ^ R ≤ C * residual (F (p t)))
    (residualBound : ∀ t, 0 < t → t < a →
      residual (F (p t)) ≤ B * t ^ q)
    (nearbyZero : ∀ t, 0 < t → t < a →
      ∃ z, F z = 0 ∧ CoordinateError (p t) z (e t))
    (lipschitzAdapter : ∀ t, 0 < t → t < a → ∀ z,
      CoordinateError (p t) z (e t) → |h z - h (p t)| ≤ L * e t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∃ z, F z = 0 ∧ StrictCube z ∧ h z ≠ 0 := by
  have hScaledC : 0 ≤ L ^ R * C := mul_nonneg (pow_nonneg hL R) hC
  obtain ⟨δ₀, hδ₀, hcut₀⟩ := positive_cutoff (R := R) ha hc₀ (mul_nonneg hC hB)
  obtain ⟨δ₁, hδ₁, hcut₁⟩ := positive_cutoff (R := R) ha hc₁
    (mul_nonneg hScaledC hB)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro t ht htδ
  have htδ₀ : t < δ₀ := lt_of_lt_of_le htδ (min_le_left _ _)
  have htδ₁ : t < δ₁ := lt_of_lt_of_le htδ (min_le_right _ _)
  obtain ⟨hta, htOne, hsmall₀⟩ := hcut₀ t ht htδ₀
  obtain ⟨hta₁, htOne₁, hsmall₁⟩ := hcut₁ t ht htδ₁
  exact exists_strict_distinct_zero_of_power_error_bound F h residual ht htOne
    hc₀ hc₁ hC hB hL exponentGap (margin t ht hta) (distinctionMargin t ht hta)
    (externalErrorBound t ht hta) (residualBound t ht hta) (nearbyZero t ht hta)
    (lipschitzAdapter t ht hta) hsmall₀ hsmall₁

-- Execution of these requests belongs to the existing compiler/integration owner.
#check nonzero_of_value_error
#check scaled_external_error_bound
#check component_order_gaps
#check exists_strict_distinct_zero_of_power_error_bound
#check eventually_exists_strict_distinct_zero_of_order_gap
#print axioms nonzero_of_value_error
#print axioms scaled_external_error_bound
#print axioms component_order_gaps
#print axioms exists_strict_distinct_zero_of_power_error_bound
#print axioms eventually_exists_strict_distinct_zero_of_order_gap

end G4DistinctMargin
