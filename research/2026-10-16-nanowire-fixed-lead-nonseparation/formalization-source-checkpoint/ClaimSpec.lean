/-
UNCOMPILED SPECIFICATION ONLY, 17 October 2026.
No proof of the claims below is provided. Defining a proposition does not prove it.
Exact source: ALL-CHANNEL-CONDUCTANCE-REGION-CANDIDATE-07.md,
SHA256 a8a2fafe2a8acc613997284f345b97f9c5b36fd88b741539fe6b31b98c4470e5.
No axiom, sorry, or assumption asserting the target is introduced.
-/
import Mathlib

noncomputable section
open scoped BigOperators

namespace NanowireAllChannelSpec

abbrev Channel (N : ℕ) := Sum (Fin N) (Fin N)
abbrev Reflection (N : ℕ) := Matrix (Channel N) (Channel N) ℂ

def swapChannel {N : ℕ} : Channel N → Channel N
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

def absSq (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

/-- Canonical zero-energy particle-hole symmetry, electron sector first. -/
def PHS {N : ℕ} (r : Reflection N) : Prop :=
  ∀ a b, r a b = star (r (swapChannel a) (swapChannel b))

/-- Euclidean operator contraction, stated without a hidden norm convention. -/
def Contractive {N : ℕ} (r : Reflection N) : Prop :=
  ∀ v : Channel N → ℂ,
    (∑ a, absSq (∑ b, r a b * v b)) ≤ ∑ a, absSq (v a)

def Admissible {N : ℕ} (r : Reflection N) : Prop := PHS r ∧ Contractive r

/-- Dimensionless local conductance in e²/h; spin already counted in N. -/
def conductance {N : ℕ} (r : Reflection N) : ℝ :=
  (N : ℝ)
    - (∑ i : Fin N, ∑ j : Fin N, absSq (r (Sum.inl i) (Sum.inl j)))
    + (∑ i : Fin N, ∑ j : Fin N, absSq (r (Sum.inl i) (Sum.inr j)))

/-- Exact full region, including real determinant, both parities and endpoints. -/
def Region (N : ℕ) (g q : ℝ) : Prop :=
  0 ≤ g ∧ g ≤ 2 * (N : ℝ) ∧
  -1 ≤ q ∧ q ≤ 1 ∧
  1 - g ≤ q ∧
  g - (2 * (N : ℝ) - 1) ≤ (if N % 2 = 0 then q else -q)

/-- The full target: necessary bounds AND attainment of every allowed pair. -/
def FullRegionClaim : Prop :=
  ∀ N : ℕ, 0 < N → ∀ g q : ℝ,
    (∃ r : Reflection N, Admissible r ∧ conductance r = g ∧
      Matrix.det r = (q : ℂ)) ↔ Region N g q

/-- Separate reality obligation; not concealed by naming the real part Q. -/
def DeterminantRealityClaim : Prop :=
  ∀ N : ℕ, ∀ r : Reflection N, PHS r → (Matrix.det r).im = 0

/-- Exact compatibility with a source promise; does not assert that promise. -/
def PositiveCompatible (N : ℕ) (m g : ℝ) : Prop :=
  ∃ r : Reflection N, ∃ q : ℝ,
    Admissible r ∧ conductance r = g ∧ Matrix.det r = (q : ℂ) ∧ m ≤ q

def NegativeCompatible (N : ℕ) (m g : ℝ) : Prop :=
  ∃ r : Reflection N, ∃ q : ℝ,
    Admissible r ∧ conductance r = g ∧ Matrix.det r = (q : ℂ) ∧ q ≤ -m

def MarginCompatibilityClaim : Prop :=
  ∀ N : ℕ, 0 < N → ∀ m g : ℝ, 0 < m → m ≤ 1 →
    (PositiveCompatible N m g ↔
      0 ≤ g ∧ g ≤ (if N % 2 = 0 then 2 * (N : ℝ) else 2 * (N : ℝ) - 1 - m)) ∧
    (NegativeCompatible N m g ↔
      1 + m ≤ g ∧ g ≤ (if N % 2 = 0 then 2 * (N : ℝ) - 1 - m else 2 * (N : ℝ)))

/-- Closed report-error interval; eta must separately be nonnegative. -/
def PositiveReportCompatible (N : ℕ) (m y eta : ℝ) : Prop :=
  ∃ g : ℝ, y - eta ≤ g ∧ g ≤ y + eta ∧ PositiveCompatible N m g

def NegativeReportCompatible (N : ℕ) (m y eta : ℝ) : Prop :=
  ∃ g : ℝ, y - eta ≤ g ∧ g ≤ y + eta ∧ NegativeCompatible N m g

end NanowireAllChannelSpec
