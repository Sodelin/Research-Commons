import BinarySharedMechanismRegistry
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.BigOperators

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual indicator-mixture product law for the shared soft mechanisms.
One indicator bit selects the common baseline table or its named target
replacement; all other original CPT rows remain shared. This is a factor
identity over complete original assignments, not yet the selected
conditional-invariance equivalence or arbitrary-DAG global Markov proof.

Read-only API pin: mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Algebra/BigOperators/Option.lean: 4a80f4a7dcf056801dc92a8287ea31e042ed6641.
Data/Finset/Option.lean: 52154bd8c0dd6375807dc40a60950cf7ac9c22d6.
Data/Fintype/BigOperators.lean: cbf19a0177656e09af2bf6d87ab2a8a672895817.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk CanonicalSelection LatentRoots

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [DecidableEq T]

def withIndicator (indicator : Bool) (w : Assignment V) : Assignment (Option V)
  | none => indicator
  | some vertex => w vertex

def indicatorAssignmentEquiv : Assignment (Option V) ≃ Bool × Assignment V where
  toFun w := (w none, fun v => w (some v))
  invFun pair := withIndicator pair.1 pair.2
  left_inv w := by funext v; cases v <;> rfl
  right_inv pair := by cases pair; rfl

theorem sum_indicator_assignments (f : Assignment (Option V) → ℚ) :
    (∑ w, f w) = ∑ indicator : Bool, ∑ w : Assignment V, f (withIndicator indicator w) := by
  rw [Fintype.sum_equiv indicatorAssignmentEquiv f
    (fun pair => f (withIndicator pair.1 pair.2)) (fun w => by
      exact congrArg f (indicatorAssignmentEquiv.left_inv w).symm)]
  exact Fintype.sum_prod_type _

noncomputable def regimeCoordinate (D : V → V → Prop) (target : T → V) (t : T) (indicator : Bool) :
    Coordinate D → SharedCoordinate D target := by
  classical
  intro coordinate
  rcases coordinate with ⟨vertex, parents⟩
  by_cases isTarget : vertex = target t
  · subst vertex
    exact if indicator then .inr (.inl ⟨t, parents⟩) else .inl ⟨target t, parents⟩
  · exact .inl ⟨vertex, parents⟩

theorem control_coordinate_is_baseline (D : V → V → Prop) (target : T → V) (t : T) :
    regimeCoordinate D target t false = baselineCoordinate D target := by
  classical
  funext coordinate
  rcases coordinate with ⟨vertex, parents⟩
  by_cases isTarget : vertex = target t
  · subst vertex
    simp (config := {instances := true}) [regimeCoordinate, dif_pos rfl, Bool.false_eq_true, if_false, baselineCoordinate]
  · simp (config := {instances := true}) [regimeCoordinate, dif_neg isTarget, baselineCoordinate]

theorem indicator_row_at_old (D : V → V → Prop) (target vertex : V) (indicator : Bool) (w : Assignment V) :
    row (AddIndicator D target) (withIndicator indicator w) (some vertex) =
      ⟨some vertex, extendParentRow D target vertex (fun p => w p.val) indicator⟩ := by
  have rows : (fun p : {p // AddIndicator D target p (some vertex)} =>
      withIndicator indicator w p.val) = extendParentRow D target vertex (fun p => w p.val) indicator := by
    funext p
    rcases p with ⟨parent, allowed⟩
    cases parent <;> rfl
  exact congrArg (fun parents => (⟨some vertex, parents⟩ : Coordinate (AddIndicator D target))) rows

theorem original_factor_coordinate (D : V → V → Prop) (target : T → V) (t : T)
    (indicator : Bool) (w : Assignment V) (vertex : V) :
    singleIndicatorCoordinate D target t
      (row (AddIndicator D (target t)) (withIndicator indicator w) (some vertex)) =
      regimeCoordinate D target t indicator (row D w vertex) := by
  classical
  rw [indicator_row_at_old]
  by_cases isTarget : vertex = target t
  · subst vertex
    cases indicator with
    | false =>
        rw [targeted_coordinate_control]
        simp (config := {instances := true}) [regimeCoordinate, row, dif_pos rfl, Bool.false_eq_true, if_false]
    | true =>
        rw [targeted_coordinate_replacement]
        simp (config := {instances := true}) [regimeCoordinate, row, dif_pos rfl, if_true]
  · rw [untargeted_coordinate_shared D target t vertex isTarget]
    simp (config := {instances := true}) [regimeCoordinate, row, isTarget]

theorem product_option (f : Option V → ℚ) : (∏ v, f v) = f none * ∏ v : V, f (some v) := by
  have all : (Finset.univ : Finset (Option V)) = Finset.insertNone (Finset.univ : Finset V) := by
    ext v
    cases v <;> simp [Finset.mem_insertNone]
  rw [all]
  exact Finset.prod_insertNone f Finset.univ

theorem shared_indicator_joint_mass (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (indicator : Bool) (w : Assignment V) :
    jointMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
      (withIndicator indicator w) =
      bernoulliMass θ (.inr (.inr t)) indicator *
        jointMass D (θ ∘ regimeCoordinate D target t indicator) w := by
  unfold jointMass
  rw [product_option]
  have rootRow : row (AddIndicator D (target t)) (withIndicator indicator w) none =
      rootCoordinate D (target t) := rootCoordinate_unique D (target t) _
  have rootFactor : bernoulliMass (θ ∘ singleIndicatorCoordinate D target t)
      (row (AddIndicator D (target t)) (withIndicator indicator w) none)
      (withIndicator indicator w none) = bernoulliMass θ (.inr (.inr t)) indicator := by
    rw [rootRow]
    cases indicator <;>
      simp (config := {instances := true}) [withIndicator, bernoulliMass, Function.comp_apply, indicator_root_coordinate]
  rw [rootFactor]
  congr 1
  apply Finset.prod_congr rfl
  intro vertex _
  change bernoulliMass (θ ∘ singleIndicatorCoordinate D target t)
      (row (AddIndicator D (target t)) (withIndicator indicator w) (some vertex)) (w vertex) = _
  cases value : w vertex <;>
    simp only [bernoulliMass, Function.comp_apply, original_factor_coordinate]

def withIndicatorCondition (C : Finset V) : Finset (Option V) := insert none (C.image some)

theorem matches_with_indicator (C : Finset V) (c w : Assignment V) (i j : Bool) :
    Matches (withIndicatorCondition C) (withIndicator i c) (withIndicator j w) ↔
      j = i ∧ Matches C c w := by
  constructor
  · intro matching
    constructor
    · exact matching none (Finset.mem_insert_self _ _)
    · intro v member
      exact matching (some v) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v, member, rfl⟩))
  · rintro ⟨same, matching⟩ v member
    rcases Finset.mem_insert.mp member with atRoot | oldMembership
    · subst v
      exact same
    · obtain ⟨oldVertex, oldMember, equation⟩ := Finset.mem_image.mp oldMembership
      subst v
      exact matching oldVertex oldMember

/-- Conditioning on a fixed indicator value and ANY original cylinder,
including the selected event, retains its own regime's exact mass. -/
theorem shared_indicator_cylinder_mass (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (i : Bool) (C : Finset V) (c : Assignment V) :
    cylinderMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
      (withIndicatorCondition C) (withIndicator i c) =
      bernoulliMass θ (.inr (.inr t)) i *
        cylinderMass D (θ ∘ regimeCoordinate D target t i) C c := by
  classical
  unfold cylinderMass
  rw [sum_indicator_assignments]
  have inner : ∀ j : Bool,
      (∑ w : Assignment V,
        if Matches (withIndicatorCondition C) (withIndicator i c) (withIndicator j w) then
          jointMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
            (withIndicator j w) else 0) =
      if j = i then bernoulliMass θ (.inr (.inr t)) j *
        ∑ w : Assignment V, if Matches C c w then jointMass D (θ ∘ regimeCoordinate D target t j) w else 0
      else 0 := by
    intro j
    by_cases same : j = i
    · subst j
      rw [if_pos rfl, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      by_cases matching : Matches C c w
      · rw [if_pos matching, if_pos ((matches_with_indicator C c w i i).mpr ⟨rfl, matching⟩)]
        exact shared_indicator_joint_mass D target t θ i w
      · have notMatch : ¬ Matches (withIndicatorCondition C) (withIndicator i c) (withIndicator i w) :=
          fun h => matching ((matches_with_indicator C c w i i).mp h).2
        rw [if_neg matching, if_neg notMatch, mul_zero]
    · rw [if_neg same]
      apply Finset.sum_eq_zero
      intro w _
      exact if_neg (fun h => same ((matches_with_indicator C c w i j).mp h).1)
  rw [Fintype.sum_bool, inner true, inner false]
  cases i <;> simp

/-- Direct finite-sum conditional-law identity. Selection may reweight
the indicator, but its original Bernoulli factor cancels inside EACH
fixed-indicator conditional ratio. No claim equates that factor with the
conditional indicator probability after selection. -/
theorem shared_indicator_conditional_ratio (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ i, 0 < θ i ∧ θ i < 1)
    (i : Bool) (numeratorCondition denominatorCondition : Finset V) (numeratorValue denominatorValue : Assignment V) :
    cylinderMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
        (withIndicatorCondition numeratorCondition) (withIndicator i numeratorValue) /
      cylinderMass (AddIndicator D (target t)) (θ ∘ singleIndicatorCoordinate D target t)
        (withIndicatorCondition denominatorCondition) (withIndicator i denominatorValue) =
    cylinderMass D (θ ∘ regimeCoordinate D target t i) numeratorCondition numeratorValue /
      cylinderMass D (θ ∘ regimeCoordinate D target t i) denominatorCondition denominatorValue := by
  rw [shared_indicator_cylinder_mass, shared_indicator_cylinder_mass]
  exact mul_div_mul_left _ _ (ne_of_gt (bernoulli_mass_pos θ positive (.inr (.inr t)) i))

theorem regime_cylinder_positive (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ) (positive : ∀ i, 0 < θ i ∧ θ i < 1)
    (i : Bool) (C : Finset V) (c : Assignment V) :
    0 < cylinderMass D (θ ∘ regimeCoordinate D target t i) C c :=
  cylinder_mass_pos D (θ ∘ regimeCoordinate D target t i)
    (fun row => positive (regimeCoordinate D target t i row)) C c

end RestrictedCausal.ProbabilitySource.BinaryCPT
