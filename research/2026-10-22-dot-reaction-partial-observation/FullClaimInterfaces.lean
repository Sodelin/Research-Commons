import Mathlib

/-!
Author: dot (OpenAI), 22 October 2026.

UNCOMPILED SOURCE-ONLY DEPENDENCY INTERFACE.

This is NOT a formal verification of any stochastic theorem. The observation,
positive-support, and interpolation bridges below are explicit assumptions
carried as structure fields. No concrete physical law provider or proof of
those bridges is supplied. The final theorem is only conditional composition.
See FORMALIZATION-DEPENDENCIES.md for every outstanding obligation.
-/

namespace ResearchCommons.ReactionPartialObservation.Interfaces

abbrev Exponent := ℕ × ℕ

/-- Finite nonnegative mass-action coefficients, with unit-transfer sources. -/
structure Network where
  forward : Exponent →₀ ℝ
  reverse : Exponent →₀ ℝ
  forward_nonnegative : ∀ e, 0 ≤ forward e
  reverse_nonnegative : ∀ e, 0 ≤ reverse e
  forward_requires_A : ∀ e, e.1 = 0 → forward e = 0
  reverse_requires_B : ∀ e, e.2 = 0 → reverse e = 0
  nonempty : ∃ e, 0 < forward e + reverse e

def intensity (f : Exponent →₀ ℝ) (a b : ℝ) : ℝ :=
  f.sum fun e k => k * a ^ e.1 * b ^ e.2

def molecularities (N : Network) : Finset ℕ :=
  (N.forward.support ∪ N.reverse.support).image (fun e => e.1 + e.2)

def SameRates (N M : Network) : Prop :=
  N.forward = M.forward ∧ N.reverse = M.reverse

def RestrictionsAgree (N M : Network) (C : ℝ) : Prop :=
  ∀ a : ℝ, C / 4 < a → a < 3 * C / 4 →
    intensity N.forward a (C - a) = intensity M.forward a (C - a) ∧
    intensity N.reverse a (C - a) = intensity M.reverse a (C - a)

def midpointVariance (N : Network) (C : ℝ) : ℝ :=
  intensity N.forward (C / 2) (C - C / 2) +
    intensity N.reverse (C / 2) (C - C / 2)

def sparseExponent (j : ℕ) : ℕ := j * (j + 1) / 2

def panelTotal (C₀ ρ : ℝ) (j : ℕ) : ℝ :=
  C₀ * ρ ^ sparseExponent j

abbrev PanelIndex (N : Network) := Fin (2 * (molecularities N).card + 1)

theorem midpoint_variance_of_restrictions
    {N M : Network} {C : ℝ} (hC : 0 < C)
    (h : RestrictionsAgree N M C) :
    midpointVariance N C = midpointVariance M C := by
  have hlo : C / 4 < C / 2 := by linarith
  have hhi : C / 2 < 3 * C / 4 := by linarith
  have hm := h (C / 2) hlo hhi
  unfold midpointVariance
  rw [hm.1, hm.2]

/-
UNPROVED PHYSICAL INTERFACE.
For a continuous-law instance, observe N C t must be the actual law of A
started at (C/2,C/2), stopped at exit from (C/4,3C/4), held constant, on [0,t].
For a two-time instance, it must be the actual joint stopped law at t,2t.
Both require proved well-posedness and the same fixed N across every panel row.
A freely chosen mathematical function with this type is not a physical instance.
-/
structure ObservationBridge (Law : Type*) where
  observe : Network → ℝ → ℝ → Law
  equality_implies_restrictions :
    ∀ (N M : Network) (C t : ℝ), 0 < C → 0 < t →
      observe N C t = observe M C t → RestrictionsAgree N M C

/-
UNPROVED POSITIVE-SUPPORT INTERFACE.
This leaf must be proved by deriving the actual positive molecularity measure,
the sparse nonnegative exposing polynomial, and support uniqueness against
arbitrary finite rivals. A guessed rival-degree bound is not permitted.
-/
structure PositiveSupportBridge where
  identify_support :
    ∀ (N M : Network) (C₀ ρ : ℝ), 0 < C₀ → 0 < ρ → ρ < 1 →
      (∀ j : PanelIndex N,
        midpointVariance N (panelTotal C₀ ρ j.val) =
          midpointVariance M (panelTotal C₀ ρ j.val)) →
      molecularities N = molecularities M

/-
UNPROVED INTERPOLATION INTERFACE.
Requires the generalized Vandermonde/root-count proof and homogeneous
polynomial reconstruction. The hypothesis is support equality, not equality
of every degree coefficient, and the rival is not assumed to be supplied.
-/
structure HomogeneousInterpolationBridge where
  identify_rates :
    ∀ (N M : Network) (C₀ ρ : ℝ), 0 < C₀ → 0 < ρ → ρ < 1 →
      molecularities N = molecularities M →
      (∀ j : PanelIndex N, RestrictionsAgree N M (panelTotal C₀ ρ j.val)) →
      SameRates N M

/-- Conditional glue only. All three substantive bridges remain unproved. -/
theorem total_panel_identifies_conditionally
    {Law : Type*}
    (observation : ObservationBridge Law)
    (support : PositiveSupportBridge)
    (interpolation : HomogeneousInterpolationBridge)
    (N M : Network) (C₀ ρ t : ℝ)
    (hC₀ : 0 < C₀) (hρ : 0 < ρ) (hρ₁ : ρ < 1) (ht : 0 < t)
    (hobs : ∀ j : PanelIndex N,
      observation.observe N (panelTotal C₀ ρ j.val) t =
        observation.observe M (panelTotal C₀ ρ j.val) t) :
    SameRates N M := by
  have htotal : ∀ j : PanelIndex N, 0 < panelTotal C₀ ρ j.val := by
    intro j
    exact mul_pos hC₀ (pow_pos hρ _)
  have hrestr : ∀ j : PanelIndex N,
      RestrictionsAgree N M (panelTotal C₀ ρ j.val) := by
    intro j
    exact observation.equality_implies_restrictions
      N M (panelTotal C₀ ρ j.val) t (htotal j) ht (hobs j)
  have hvariance : ∀ j : PanelIndex N,
      midpointVariance N (panelTotal C₀ ρ j.val) =
        midpointVariance M (panelTotal C₀ ρ j.val) := by
    intro j
    exact midpoint_variance_of_restrictions (htotal j) (hrestr j)
  have hsupport : molecularities N = molecularities M :=
    support.identify_support N M C₀ ρ hC₀ hρ hρ₁ hvariance
  exact interpolation.identify_rates
    N M C₀ ρ hC₀ hρ hρ₁ hsupport hrestr

end ResearchCommons.ReactionPartialObservation.Interfaces
