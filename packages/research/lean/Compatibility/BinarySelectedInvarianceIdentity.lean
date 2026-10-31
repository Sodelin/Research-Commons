import BinaryConditionalIndependenceAlgebra

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual finite-sum D6 identity. Standard indicator/x binary independence
on a fixed selected conditioning slice is equivalent to equality of the
baseline and named replacement conditional x laws on that slice. The
indicator's unconditional root probability is never identified with its
selection-conditioned probability. D1 and final graph/game assembly are
separate obligations.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk CanonicalSelection LatentRoots

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [DecidableEq T]

def pointAssignment (x : V) (c : Assignment V) (b : Bool) : Assignment V :=
  fun v => if v = x then b else c v

theorem matches_point_assignment (x : V) (C : Finset V) (c w : Assignment V) (b : Bool)
    (outside : x ∉ C) :
    Matches (insert x C) (pointAssignment x c b) w ↔ w x = b ∧ Matches C c w := by
  constructor
  · intro matching
    constructor
    · simpa (config := {instances := true}) [pointAssignment] using matching x (Finset.mem_insert_self _ _)
    · intro v member
      have different : v ≠ x := by intro same; subst v; exact outside member
      simpa only [pointAssignment, if_neg different] using matching v (Finset.mem_insert_of_mem member)
  · rintro ⟨atX, matching⟩ v member
    rcases Finset.mem_insert.mp member with same | member
    · subst v
      simpa (config := {instances := true}) [pointAssignment] using atX
    · have different : v ≠ x := by intro same; subst v; exact outside member
      simpa only [pointAssignment, if_neg different] using matching v member

theorem cylinder_partition_at_vertex (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (x : V) (C : Finset V) (c : Assignment V) (outside : x ∉ C) :
    cylinderMass D θ C c =
      cylinderMass D θ (insert x C) (pointAssignment x c false) +
      cylinderMass D θ (insert x C) (pointAssignment x c true) := by
  classical
  unfold cylinderMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases matching : Matches C c w
  · rw [if_pos matching]
    cases value : w x with
    | false =>
        have falseMatch := (matches_point_assignment x C c w false outside).mpr ⟨value, matching⟩
        have notTrue : ¬ Matches (insert x C) (pointAssignment x c true) w := by
          intro h
          have «impossible» := (matches_point_assignment x C c w true outside).mp h
          rw [value] at «impossible»
          exact Bool.noConfusion «impossible».1
        rw [if_pos falseMatch, if_neg notTrue, add_zero]
    | true =>
        have trueMatch := (matches_point_assignment x C c w true outside).mpr ⟨value, matching⟩
        have notFalse : ¬ Matches (insert x C) (pointAssignment x c false) w := by
          intro h
          have «impossible» := (matches_point_assignment x C c w false outside).mp h
          rw [value] at «impossible»
          exact Bool.noConfusion «impossible».1
        rw [if_neg notFalse, if_pos trueMatch, zero_add]
  · have noCell : ∀ b, ¬ Matches (insert x C) (pointAssignment x c b) w :=
      fun b h => matching ((matches_point_assignment x C c w b outside).mp h).2
    rw [if_neg matching, if_neg (noCell false), if_neg (noCell true), add_zero]

theorem indicator_cell_assignment (x : V) (c : Assignment V) (i b : Bool) :
    cellAssignment none (some x) (withIndicator false c) i b =
      withIndicator i (pointAssignment x c b) := by
  funext v
  cases v with
  | none => rfl
  | some v =>
      by_cases same : v = x
      · subst v
        simp only [cellAssignment, withIndicator, pointAssignment, if_pos rfl,
          Option.some_ne_none, if_false]
      · simp only [cellAssignment, withIndicator, pointAssignment, if_neg same,
          Option.some_ne_none, Option.some.injEq, if_false]

theorem indicator_cell_condition (x : V) (C : Finset V) :
    insert none (insert (some x) (C.image some)) = withIndicatorCondition (insert x C) := by
  ext v
  cases v <;> simp [withIndicatorCondition]

noncomputable def indicatorCellMass (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (x : V) (C : Finset V) (c : Assignment V) : Bool → Bool → ℚ :=
  fun i b => cellMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
    none (some x) (C.image some) (withIndicator false c) i b

theorem indicator_cell_mass_factor (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (x : V) (C : Finset V) (c : Assignment V) (i b : Bool) :
    indicatorCellMass D target t θ x C c i b = bernoulliMass θ (.inr (.inr t)) i *
      cylinderMass D (θ ∘ regimeCoordinate D target t i) (insert x C) (pointAssignment x c b) := by
  unfold indicatorCellMass cellMass
  rw [indicator_cell_assignment, indicator_cell_condition]
  exact shared_indicator_cylinder_mass D target t θ i _ _

theorem indicator_row_mass_factor (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (x : V) (C : Finset V) (c : Assignment V) (i : Bool)
    (outside : x ∉ C) :
    indicatorCellMass D target t θ x C c i false + indicatorCellMass D target t θ x C c i true =
      bernoulliMass θ (.inr (.inr t)) i * cylinderMass D (θ ∘ regimeCoordinate D target t i) C c := by
  rw [indicator_cell_mass_factor, indicator_cell_mass_factor, ← mul_add,
    ← cylinder_partition_at_vertex D (θ ∘ regimeCoordinate D target t i) x C c outside]

noncomputable def regimeConditionalMass (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (x : V) (C : Finset V) (c : Assignment V) (i b : Bool) : ℚ :=
  cylinderMass D (θ ∘ regimeCoordinate D target t i) (insert x C) (pointAssignment x c b) /
    cylinderMass D (θ ∘ regimeCoordinate D target t i) C c

theorem indicator_row_conditional_mass (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ k, 0 < θ k ∧ θ k < 1)
    (x : V) (C : Finset V) (c : Assignment V) (i b : Bool) (outside : x ∉ C) :
    indicatorCellMass D target t θ x C c i b /
      (indicatorCellMass D target t θ x C c i false + indicatorCellMass D target t θ x C c i true) =
    regimeConditionalMass D target t θ x C c i b := by
  rw [indicator_cell_mass_factor, indicator_row_mass_factor D target t θ x C c i outside]
  exact mul_div_mul_left _ _ (ne_of_gt (bernoulli_mass_pos θ positive (.inr (.inr t)) i))

theorem indicator_independent_iff_regime_invariant_at (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ k, 0 < θ k ∧ θ k < 1)
    (x : V) (C : Finset V) (c : Assignment V) (outside : x ∉ C) :
    BinaryMassIndependent (indicatorCellMass D target t θ x C c) ↔
      ∀ b, regimeConditionalMass D target t θ x C c false b =
        regimeConditionalMass D target t θ x C c true b := by
  have rowsPositive : ∀ i, 0 < indicatorCellMass D target t θ x C c i false +
      indicatorCellMass D target t θ x C c i true := by
    intro i
    rw [indicator_row_mass_factor D target t θ x C c i outside]
    exact mul_pos (bernoulli_mass_pos θ positive (.inr (.inr t)) i)
      (regime_cylinder_positive D target t θ positive i C c)
  rw [binary_independent_iff_rows_equal _ (ne_of_gt (rowsPositive false)) (ne_of_gt (rowsPositive true))]
  unfold BinaryRowsEqual
  constructor <;> intro h b
  · simpa only [indicator_row_conditional_mass D target t θ positive x C c false b outside,
      indicator_row_conditional_mass D target t θ positive x C c true b outside] using h b
  · rw [indicator_row_conditional_mass D target t θ positive x C c false b outside,
      indicator_row_conditional_mass D target t θ positive x C c true b outside]
    exact h b

/-- Standard cross-product CI restricted to the selected slice S=1,
quantified over EVERY conditioning assignment, is exactly the cross-regime
conditional invariance statement. C is intended as Z union S; no root
probability after selection is identified with its unconditional value. -/
theorem selected_indicator_independent_iff_invariant (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ k, 0 < θ k ∧ θ k < 1)
    (x : V) (C S : Finset V) (selected : S ⊆ C) (outside : x ∉ C) :
    (∀ c : Assignment V, Matches S (fun _ => true) c →
      BinaryMassIndependent (indicatorCellMass D target t θ x C c)) ↔
    (∀ c : Assignment V, Matches S (fun _ => true) c → ∀ b,
      regimeConditionalMass D target t θ x C c false b =
        regimeConditionalMass D target t θ x C c true b) := by
  constructor
  · intro h c selectedValues
    exact (indicator_independent_iff_regime_invariant_at D target t θ positive x C c outside).mp
      (h c selectedValues)
  · intro h c selectedValues
    exact (indicator_independent_iff_regime_invariant_at D target t θ positive x C c outside).mpr
      (h c selectedValues)

end RestrictedCausal.ProbabilitySource.BinaryCPT
