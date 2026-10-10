import UnifiedLean.Source.NativePairClockLaw
import UnifiedLean.Source.NativeIndependentPairMixture
import Mathlib.Tactic.FieldSimp

/-!
# Source-exact inverse-rate rewriting of natural G6 hazard cells

Contributor: dot, 2026-10-09. Compilation and scope are recorded in the accompanying receipt.
Classical positive reciprocal substitution, specialized to the actual original
Calendar, PositivePairRates and HybridProbabilities carriers. No source law,
image membership, QE result or witness-existence conclusion is an input field.
Strict rational linear elimination and the full finite-cell compiler are
separate next implementation obligations.
-/
namespace UnifiedLean.G6.NaturalCellInverseRates
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture

structure RationalBound where
  value : ℚ
  strict : Bool

structure RationalInterval where
  lower : Option RationalBound
  upper : Option RationalBound

def RationalInterval.contains (c : RationalInterval) (x : ℝ) : Prop :=
  (∀ b ∈ c.lower, if b.strict then (b.value : ℝ) < x else (b.value : ℝ) ≤ x) ∧
  (∀ b ∈ c.upper, if b.strict then x < (b.value : ℝ) else x ≤ (b.value : ℝ))

/-- Every row is affine in duration d and the ONE physical inverse rate u.
An absent upper endpoint (saturation) remains absent. -/
def RationalInterval.scaled (c : RationalInterval) (d u : ℝ) : Prop :=
  (∀ b ∈ c.lower, if b.strict then (b.value : ℝ) * u < d else (b.value : ℝ) * u ≤ d) ∧
  (∀ b ∈ c.upper, if b.strict then d < (b.value : ℝ) * u else d ≤ (b.value : ℝ) * u)

theorem interval_div_iff (c : RationalInterval) (d u : ℝ) (hu : 0 < u) :
    c.contains (d / u) ↔ c.scaled d u := by
  unfold RationalInterval.contains RationalInterval.scaled
  constructor
  · rintro ⟨hl, hh⟩
    constructor
    · intro b hb
      have h := hl b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (le_div_iff₀ hu).mp h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (lt_div_iff₀ hu).mp h
    · intro b hb
      have h := hh b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (div_le_iff₀ hu).mp h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (div_lt_iff₀ hu).mp h
  · rintro ⟨hl, hh⟩
    constructor
    · intro b hb
      have h := hl b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (le_div_iff₀ hu).mpr h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (lt_div_iff₀ hu).mpr h
    · intro b hb
      have h := hh b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (div_le_iff₀ hu).mpr h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (div_lt_iff₀ hu).mpr h

theorem interval_rate_iff (c : RationalInterval) (rho d : ℝ) (hr : 0 < rho) :
    c.contains (rho * d) ↔ c.scaled d rho⁻¹ := by
  have he : rho * d = d / rho⁻¹ := by simp only [div_inv_eq_mul, mul_comm]
  rw [he]
  exact interval_div_iff c d rho⁻¹ (inv_pos.mpr hr)

variable {V E X I : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Source graph and original IDs are unchanged. none is the SAME ancestral
population used by every finite post-root exposure. -/
noncomputable def inverseBank (r : PositivePairRates E) : Option E → ℝ :=
  fun e => (pairRate r e)⁻¹

theorem inverse_bank_pos (r : PositivePairRates E) (e : Option E) :
    0 < inverseBank r e := inv_pos.mpr (pairRate_pos r e)

noncomputable def ratesOfInverse (u : Option E → ℝ) (hu : ∀ e, 0 < u e) :
    PositivePairRates E where
  edge e := (u (some e))⁻¹
  edge_pos e := inv_pos.mpr (hu (some e))
  ancestral := (u none)⁻¹
  ancestral_pos := inv_pos.mpr (hu none)

theorem constructed_pair_rate (u : Option E → ℝ) (hu : ∀ e, 0 < u e)
    (e : Option E) : pairRate (ratesOfInverse u hu) e = (u e)⁻¹ := by
  cases e <;> rfl

theorem reconstructed_inverse_bank (u : Option E → ℝ) (hu : ∀ e, 0 < u e) :
    inverseBank (ratesOfInverse u hu) = u := by
  funext e
  simp only [inverseBank, constructed_pair_rate, inv_inv]

/-- An endpoint is a literal original node age or a fixed rational cut/zero.
The syntax cannot silently supply an arbitrary nonlinear age expression. -/
inductive AgeAtom (V : Type*)
  | node (v : V)
  | fixed (q : ℚ)

def AgeAtom.eval (a : V → ℝ) : AgeAtom V → ℝ
  | .node v => a v
  | .fixed q => q

structure Exposure (V E : Type*) where
  population : Option E
  younger : AgeAtom V
  older : AgeAtom V
  cell : RationalInterval

def Exposure.duration (e : Exposure V E) (a : V → ℝ) : ℝ :=
  e.older.eval a - e.younger.eval a

/-- The identical bank is used for ALL exposure indices, including different
menu rows or epochs which refer to the same physical population. -/
theorem all_hazard_cells_iff (rows : I → Exposure V E) (a : V → ℝ)
    (r : PositivePairRates E) :
    (∀ i, (rows i).cell.contains (pairRate r (rows i).population * (rows i).duration a)) ↔
      (∀ i, (rows i).cell.scaled ((rows i).duration a)
        (inverseBank r (rows i).population)) := by
  constructor
  · intro h i
    exact (interval_rate_iff (rows i).cell _ _ (pairRate_pos r _)).mp (h i)
  · intro h i
    exact (interval_rate_iff (rows i).cell _ _ (pairRate_pos r _)).mpr (h i)

/-- Construct an ACTUAL original Calendar directly from its linear edge-age
constraints. No physically altered graph or suppressed demographic node. -/
def calendarOfAges (N : RootedBinary V E X) (a : V → ℝ)
    (ha : ∀ e, a (N.graph.target e) < a (N.graph.source e)) : Calendar N.graph :=
  ⟨a, ha⟩

/-- The original shared inheritance carrier is built from its strict linear
bounds; COMMON/INDEPENDENT observation kernels remain separately defined. -/
def inheritanceOfValues (N : RootedBinary V E X) (g : Hybrid N → ℝ)
    (hg0 : ∀ h, 0 < g h) (hg1 : ∀ h, g h < 1) : HybridProbabilities N :=
  ⟨g, hg0, hg1⟩

/-- Back-substitution into the genuine original positive rate bank satisfies
all original cells simultaneously. This supplies no desired observation law. -/
theorem reconstructed_bank_satisfies (rows : I → Exposure V E) (a : V → ℝ)
    (u : Option E → ℝ) (hu : ∀ e, 0 < u e)
    (hc : ∀ i, (rows i).cell.scaled ((rows i).duration a) (u (rows i).population)) :
    ∀ i, (rows i).cell.contains
      (pairRate (ratesOfInverse u hu) (rows i).population * (rows i).duration a) := by
  apply (all_hazard_cells_iff rows a (ratesOfInverse u hu)).mpr
  rw [reconstructed_inverse_bank]
  exact hc

/-- Rational affine chronology atoms include exact ties, as required by a
complete weak order of original ages and fixed observation cuts. -/
inductive AgeComparison
  | strict | weak | equal

def AgeComparison.holds (cmp : AgeComparison) (x y : ℝ) : Prop :=
  match cmp with
  | .strict => x < y
  | .weak => x ≤ y
  | .equal => x = y

structure AgeConstraint (V : Type*) where
  left : AgeAtom V
  right : AgeAtom V
  comparison : AgeComparison

def AgeConstraint.holds (c : AgeConstraint V) (a : V → ℝ) : Prop :=
  c.comparison.holds (c.left.eval a) (c.right.eval a)

variable {C : Type*}

/-- All rows refer to one literal original calendar, rate bank and inheritance
bank. Graph admission is fixed before this definition, not replaced by a
larger graph or independently fit rowwise sources. -/
def originalCellFeasible (N : RootedBinary V E X)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Prop :=
  ∃ (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N),
    (∀ x, c.age (N.leaf x) = 0) ∧
    (∀ j, (chronology j).holds c.age) ∧
    (∀ h, (coins h).contains (g.gamma h)) ∧
    (∀ i, (rows i).cell.contains
      (pairRate r (rows i).population * (rows i).duration c.age))

/-- An explicit rational-affine system: all coefficients in age comparisons,
exposure bounds and gamma cells are rational constants. u has one coordinate
per original edge and ONE ancestral coordinate. -/
def inverseCellFeasible (N : RootedBinary V E X)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Prop :=
  ∃ (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ),
    (∀ e, a (N.graph.target e) < a (N.graph.source e)) ∧
    (∀ x, a (N.leaf x) = 0) ∧
    (∀ e, 0 < u e) ∧
    (∀ h, 0 < g h) ∧ (∀ h, g h < 1) ∧
    (∀ j, (chronology j).holds a) ∧
    (∀ h, (coins h).contains (g h)) ∧
    (∀ i, (rows i).cell.scaled ((rows i).duration a) (u (rows i).population))

/-- Exact simultaneous source-to-cell equivalence. No approximation,
feasibility oracle, source-image equality or source witness is assumed. -/
theorem original_cell_iff_inverse (N : RootedBinary V E X)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) :
    originalCellFeasible N chronology rows coins ↔
      inverseCellFeasible N chronology rows coins := by
  constructor
  · rintro ⟨c, r, g, htip, horder, hcoins, hrows⟩
    exact ⟨c.age, inverseBank r, g.gamma, c.edge_older, htip,
      inverse_bank_pos r, g.positive, g.below_one, horder, hcoins,
      (all_hazard_cells_iff rows c.age r).mp hrows⟩
  · rintro ⟨a, u, g, hedge, htip, hu, hg0, hg1, horder, hcoins, hrows⟩
    exact ⟨calendarOfAges N a hedge, ratesOfInverse u hu,
      inheritanceOfValues N g hg0 hg1, htip, horder, hcoins,
      reconstructed_bank_satisfies rows a u hu hrows⟩

#print axioms interval_div_iff
#print axioms interval_rate_iff
#print axioms inverse_bank_pos
#print axioms constructed_pair_rate
#print axioms reconstructed_inverse_bank
#print axioms all_hazard_cells_iff
#print axioms reconstructed_bank_satisfies
#print axioms original_cell_iff_inverse
end UnifiedLean.G6.NaturalCellInverseRates
