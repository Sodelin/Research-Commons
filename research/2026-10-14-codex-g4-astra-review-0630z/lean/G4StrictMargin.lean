import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional strict-margin exactification

Contributor: Codex delegated margin formalization, 14 October 2026.
Source: `2026-10-14-g4-independent-astra-exact-fibre-0535z/MARGIN-LIFT.md`, §4.

The external polynomial error bound and existence of a nearby zero are explicit
premises. This file does not prove either external theorem, construct a physical
jet, or identify a source-specific degree/exponent. Exponents here are natural
numbers. The conclusion applies to one whole vector equation on one tuple.

Compilation has not been executed in this environment.
-/

namespace G4StrictMargin

/-- The strict physical coordinate cube; additional source restrictions require
their own hypotheses. -/
def StrictCube {ι : Type*} (p : ι → ℝ) : Prop :=
  ∀ i, 0 < p i ∧ p i < 1

/-- A common lower bound for both boundary margins of every coordinate. -/
def CoordinateMargin {ι : Type*} (p : ι → ℝ) (μ : ℝ) : Prop :=
  ∀ i, μ ≤ p i ∧ μ ≤ 1 - p i

/-- A coordinatewise error radius. An ambient norm bound can be converted to
this premise once its coordinate domination theorem is supplied. -/
def CoordinateError {ι : Type*} (p z : ι → ℝ) (e : ℝ) : Prop :=
  ∀ i, |z i - p i| ≤ e

/-- Strict positivity survives a correction smaller than every margin. -/
theorem strictCube_of_coordinateMargin {ι : Type*} {p z : ι → ℝ} {μ e : ℝ}
    (margin : CoordinateMargin p μ) (coordinateError : CoordinateError p z e)
    (errorBelowMargin : e < μ) : StrictCube z := by
  intro i
  obtain ⟨hlo, hhi⟩ := margin i
  obtain ⟨heLo, heHi⟩ := abs_le.mp (coordinateError i)
  constructor <;> linarith

/-- A whole-vector zero with a sufficiently small correction is a strict zero.
`nearbyZero` does not assume strictness of the zero. -/
theorem exists_strict_zero_of_coordinate_error
    {ι β : Type*} [Zero β] (F : (ι → ℝ) → β) {p : ι → ℝ} {μ e : ℝ}
    (margin : CoordinateMargin p μ)
    (nearbyZero : ∃ z, F z = 0 ∧ CoordinateError p z e)
    (errorBelowMargin : e < μ) : ∃ z, F z = 0 ∧ StrictCube z := by
  obtain ⟨z, hz, he⟩ := nearbyZero
  exact ⟨z, hz, strictCube_of_coordinateMargin margin he errorBelowMargin⟩

/-- Elementary power estimate used to expose the actual exponent gap. -/
theorem pow_le_one_of_unit_interval {t : ℝ} (ht : 0 ≤ t) (htOne : t ≤ 1)
    (k : ℕ) : t ^ k ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        t ^ (k + 1) = t ^ k * t := pow_succ t k
        _ ≤ 1 * 1 := mul_le_mul ih htOne ht (by norm_num)
        _ = 1 := by ring

/-- For a strict natural exponent gap and `0 < t ≤ 1`, one full extra factor
of `t` can be extracted. This is where `q > r R` is used. -/
theorem pow_le_lower_power_mul {t : ℝ} {a q : ℕ}
    (ht : 0 ≤ t) (htOne : t ≤ 1) (exponentGap : a < q) :
    t ^ q ≤ t ^ a * t := by
  let k := q - (a + 1)
  have hq : q = a + (k + 1) := by dsimp [k]; omega
  have hk : t ^ (k + 1) ≤ t := by
    calc
      t ^ (k + 1) = t ^ k * t := pow_succ t k
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right
        (pow_le_one_of_unit_interval ht htOne k) ht
      _ = t := one_mul t
  calc
    t ^ q = t ^ a * t ^ (k + 1) := by rw [hq, pow_add]
    _ ≤ t ^ a * t := mul_le_mul_of_nonneg_left hk (pow_nonneg ht a)

/-- Quantitative scalar consequence of an external power error bound and a
residual bound. No root extraction or real-power asymptotics are assumed.
The explicit small-`t` condition is weaker than assuming the desired conclusion. -/
theorem error_lt_power_margin {t c e C B residual : ℝ} {r R q : ℕ}
    (ht : 0 < t) (htOne : t ≤ 1) (hc : 0 < c)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (exponentGap : r * R < q)
    (externalErrorBound : e ^ R ≤ C * residual)
    (residualBound : residual ≤ B * t ^ q)
    (smallParameter : C * B * t < c ^ R) : e < c * t ^ r := by
  have hK : 0 ≤ C * B := mul_nonneg hC hB
  have hePower : e ^ R ≤ C * B * (t ^ (r * R) * t) := by
    calc
      e ^ R ≤ C * residual := externalErrorBound
      _ ≤ C * (B * t ^ q) := mul_le_mul_of_nonneg_left residualBound hC
      _ = C * B * t ^ q := by ring
      _ ≤ C * B * (t ^ (r * R) * t) := mul_le_mul_of_nonneg_left
        (pow_le_lower_power_mul (le_of_lt ht) htOne exponentGap) hK
  have heStrict : e ^ R < (c * t ^ r) ^ R := by
    calc
      e ^ R ≤ C * B * (t ^ (r * R) * t) := hePower
      _ = (C * B * t) * t ^ (r * R) := by ring
      _ < c ^ R * t ^ (r * R) :=
        mul_lt_mul_of_pos_right smallParameter (pow_pos ht _)
      _ = (c * t ^ r) ^ R := by rw [mul_pow, pow_mul]
  by_contra h
  have hmargin : 0 ≤ c * t ^ r := le_of_lt (mul_pos hc (pow_pos ht _))
  have hle : (c * t ^ r) ^ R ≤ e ^ R :=
    pow_le_pow_left₀ hmargin (le_of_not_gt h) R
  exact (not_lt_of_ge hle) heStrict

/-- Pointwise finite-jet consequence. The external theorem supplies a radius
power bound; nearest-zero existence supplies a zero within that radius.
Neither premise includes the strict-domain conclusion. -/
theorem exists_strict_zero_of_power_error_bound
    {ι β : Type*} [Zero β] (F : (ι → ℝ) → β) (residual : β → ℝ)
    {p : ι → ℝ} {t c e C B : ℝ} {r R q : ℕ}
    (ht : 0 < t) (htOne : t ≤ 1) (hc : 0 < c)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (exponentGap : r * R < q)
    (margin : CoordinateMargin p (c * t ^ r))
    (externalErrorBound : e ^ R ≤ C * residual (F p))
    (residualBound : residual (F p) ≤ B * t ^ q)
    (nearbyZero : ∃ z, F z = 0 ∧ CoordinateError p z e)
    (smallParameter : C * B * t < c ^ R) : ∃ z, F z = 0 ∧ StrictCube z := by
  apply exists_strict_zero_of_coordinate_error F margin nearbyZero
  exact error_lt_power_margin ht htOne hc hC hB exponentGap
    externalErrorBound residualBound smallParameter

/-- A positive explicit cutoff supplies the small-parameter inequality. -/
theorem positive_cutoff {a c K : ℝ} {R : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      t < a ∧ t ≤ 1 ∧ K * t < c ^ R := by
  let δ := min a (min 1 (c ^ R / (K + 1)))
  have hdenom : 0 < K + 1 := by linarith
  have hcut : 0 < c ^ R / (K + 1) := div_pos (pow_pos hc _) hdenom
  refine ⟨δ, lt_min ha (lt_min (by norm_num) hcut), ?_⟩
  intro t ht htδ
  have hta : t < a := lt_of_lt_of_le htδ (min_le_left _ _)
  have htInner : t < min 1 (c ^ R / (K + 1)) :=
    lt_of_lt_of_le htδ (min_le_right _ _)
  have htOne : t ≤ 1 := le_of_lt
    (lt_of_lt_of_le htInner (min_le_left _ _))
  have htCut : t < c ^ R / (K + 1) :=
    lt_of_lt_of_le htInner (min_le_right _ _)
  have htProduct : t * (K + 1) < c ^ R := (lt_div_iff₀ hdenom).mp htCut
  exact ⟨hta, htOne, by nlinarith⟩

/-- Natural-order version of the eventual strict exactification implication.
For every sufficiently small positive parameter, there is one strict exact
zero of the full supplied map. The architecture/coordinate type is fixed.

The named `externalErrorBound` and `nearbyZero` hypotheses retain the analytic
inputs that this elementary Lean module does not prove. -/
theorem eventually_exists_strict_zero_of_order_gap
    {ι β : Type*} [Zero β] (F : (ι → ℝ) → β) (residual : β → ℝ)
    (p : ℝ → (ι → ℝ)) (e : ℝ → ℝ) {a c C B : ℝ} {r R q : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (exponentGap : r * R < q)
    (margin : ∀ t, 0 < t → t < a → CoordinateMargin (p t) (c * t ^ r))
    (externalErrorBound : ∀ t, 0 < t → t < a →
      e t ^ R ≤ C * residual (F (p t)))
    (residualBound : ∀ t, 0 < t → t < a →
      residual (F (p t)) ≤ B * t ^ q)
    (nearbyZero : ∀ t, 0 < t → t < a →
      ∃ z, F z = 0 ∧ CoordinateError (p t) z (e t)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      ∃ z, F z = 0 ∧ StrictCube z := by
  obtain ⟨δ, hδ, hcut⟩ := positive_cutoff (R := R) ha hc (mul_nonneg hC hB)
  refine ⟨δ, hδ, ?_⟩
  intro t ht htδ
  obtain ⟨hta, htOne, hsmall⟩ := hcut t ht htδ
  exact exists_strict_zero_of_power_error_bound F residual ht htOne hc hC hB
    exponentGap (margin t ht hta) (externalErrorBound t ht hta)
    (residualBound t ht hta) (nearbyZero t ht hta) hsmall

#print axioms strictCube_of_coordinateMargin
#print axioms exists_strict_zero_of_coordinate_error
#print axioms pow_le_one_of_unit_interval
#print axioms pow_le_lower_power_mul
#print axioms error_lt_power_margin
#print axioms exists_strict_zero_of_power_error_bound
#print axioms positive_cutoff
#print axioms eventually_exists_strict_zero_of_order_gap

end G4StrictMargin
