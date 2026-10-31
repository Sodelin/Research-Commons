import BinarySelectionSinkComplement
import Mathlib.Algebra.MvPolynomial.Rename

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual D4 coordinates for ONE baseline DAG and one replacement table and
one named root probability per target. Each separate single-indicator
augmentation embeds injectively into this SAME registry. No multi-target
indicator experiment or independently chosen baseline mechanism is used.

API read: mathlib 0df444a360eaa60ab8c11dca51a86af692955474,
Algebra/MvPolynomial/Rename.lean blob
7b6c1a1a887fd1f3f9184ec1c2ee57348cea5f5e: rename_injective,
rename_eq_zero_iff_of_injective and eval_rename.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open SelectedWalk CanonicalSelection LatentRoots

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : Type v} [DecidableEq T]

/-- Base CPT coordinates, target-specific replacement coordinates, and
one root probability for each named target. Selection and latent vertex
coordinates are among the unchanged original base coordinates. -/
abbrev SharedCoordinate (D : V → V → Prop) (target : T → V) :=
  Sum (Coordinate D) (Sum ((t : T) × ({p // D p (target t)} → Bool)) T)

def oldParentRow (D : V → V → Prop) (target vertex : V)
    (parents : {p // AddIndicator D target p (some vertex)} → Bool) :
    {p // D p vertex} → Bool :=
  fun p => parents ⟨some p.val, p.property⟩

def extendParentRow (D : V → V → Prop) (target vertex : V)
    (parents : {p // D p vertex} → Bool) (indicator : Bool) :
    {p // AddIndicator D target p (some vertex)} → Bool :=
  fun p => match p with
    | ⟨none, _⟩ => indicator
    | ⟨some old, allowed⟩ => parents ⟨old, allowed⟩

def rootCoordinate (D : V → V → Prop) (target : V) : Coordinate (AddIndicator D target) :=
  ⟨none, fun p => (indicator_no_parent D target p.val p.property).elim⟩

theorem rootCoordinate_unique (D : V → V → Prop) (target : V)
    (parents : {p // AddIndicator D target p none} → Bool) :
    (⟨none, parents⟩ : Coordinate (AddIndicator D target)) = rootCoordinate D target := by
  have emptyRow : parents = (rootCoordinate D target).2 := by
    funext p
    exact (indicator_no_parent D target p.val p.property).elim
  exact congrArg (fun row => (⟨none, row⟩ : Coordinate (AddIndicator D target))) emptyRow

theorem extend_old_target_row (D : V → V → Prop) (target : V)
    (parents : {p // AddIndicator D target p (some target)} → Bool) :
    extendParentRow D target target (oldParentRow D target target parents) (parents ⟨none, rfl⟩) = parents := by
  funext p
  rcases p with ⟨parent, allowed⟩
  cases parent <;> rfl

theorem extend_old_untargeted_row (D : V → V → Prop) (target vertex : V) (different : vertex ≠ target)
    (parents : {p // AddIndicator D target p (some vertex)} → Bool) (indicator : Bool) :
    extendParentRow D target vertex (oldParentRow D target vertex parents) indicator = parents := by
  funext p
  rcases p with ⟨parent, allowed⟩
  cases parent with
  | none => exact (different allowed).elim
  | some old => rfl

noncomputable def singleIndicatorCoordinate (D : V → V → Prop) (target : T → V) (t : T) :
    Coordinate (AddIndicator D (target t)) → SharedCoordinate D target := by
  classical
  intro coordinate
  rcases coordinate with ⟨vertex, parents⟩
  cases vertex with
  | none => exact .inr (.inr t)
  | some vertex =>
      by_cases isTarget : vertex = target t
      · subst vertex
        exact if parents ⟨none, rfl⟩ then
          .inr (.inl ⟨t, oldParentRow D (target t) (target t) parents⟩)
        else .inl ⟨target t, oldParentRow D (target t) (target t) parents⟩
      · exact .inl ⟨vertex, oldParentRow D (target t) vertex parents⟩

/-- A total left inverse, not an asserted injection. Coordinates belonging
to other targets are irrelevant to this slice and map to its root row. -/
noncomputable def recoverSingleCoordinate (D : V → V → Prop) (target : T → V) (t : T) :
    SharedCoordinate D target → Coordinate (AddIndicator D (target t)) := by
  classical
  intro coordinate
  rcases coordinate with ⟨vertex, parents⟩ | (⟨index, parents⟩ | index)
  · exact ⟨some vertex, extendParentRow D (target t) vertex parents false⟩
  · by_cases same : index = t
    · subst index
      exact ⟨some (target t), extendParentRow D (target t) (target t) parents true⟩
    · exact rootCoordinate D (target t)
  · exact rootCoordinate D (target t)

theorem recover_single_coordinate (D : V → V → Prop) (target : T → V) (t : T)
    (coordinate : Coordinate (AddIndicator D (target t))) :
    recoverSingleCoordinate D target t (singleIndicatorCoordinate D target t coordinate) = coordinate := by
  classical
  rcases coordinate with ⟨vertex, parents⟩
  cases vertex with
  | none =>
      exact (rootCoordinate_unique D (target t) parents).symm
  | some vertex =>
      by_cases isTarget : vertex = target t
      · subst vertex
        have rowRecovery := extend_old_target_row D (target t) parents
        cases indicatorValue : parents ⟨none, rfl⟩ with
        | false =>
            simp only [singleIndicatorCoordinate, dif_pos rfl, indicatorValue, Bool.false_eq_true,
              if_false, recoverSingleCoordinate]
            exact congrArg (fun row => (⟨some (target t), row⟩ : Coordinate (AddIndicator D (target t))))
              (by simpa only [indicatorValue] using rowRecovery)
        | true =>
            simp only [singleIndicatorCoordinate, dif_pos rfl, indicatorValue, if_true,
              recoverSingleCoordinate, dif_pos rfl]
            exact congrArg (fun row => (⟨some (target t), row⟩ : Coordinate (AddIndicator D (target t))))
              (by simpa only [indicatorValue] using rowRecovery)
      · simp only [singleIndicatorCoordinate, dif_neg isTarget, recoverSingleCoordinate]
        exact congrArg (fun row => (⟨some vertex, row⟩ : Coordinate (AddIndicator D (target t))))
          (extend_old_untargeted_row D (target t) vertex isTarget parents false)

theorem single_indicator_coordinate_injective (D : V → V → Prop) (target : T → V) (t : T) :
    Function.Injective (singleIndicatorCoordinate D target t) := by
  intro «first» second same
  have recovered := congrArg (recoverSingleCoordinate D target t) same
  simpa only [recover_single_coordinate] using recovered

theorem indicator_root_coordinate (D : V → V → Prop) (target : T → V) (t : T) :
    singleIndicatorCoordinate D target t (rootCoordinate D (target t)) = .inr (.inr t) := rfl

theorem untargeted_coordinate_shared (D : V → V → Prop) (target : T → V) (t : T)
    (vertex : V) (different : vertex ≠ target t) (parents : {p // D p vertex} → Bool)
    (indicator : Bool) :
    singleIndicatorCoordinate D target t
      ⟨some vertex, extendParentRow D (target t) vertex parents indicator⟩ = .inl ⟨vertex, parents⟩ := by
  classical
  simp only [singleIndicatorCoordinate, dif_neg different, oldParentRow, extendParentRow]

theorem targeted_coordinate_control (D : V → V → Prop) (target : T → V) (t : T)
    (parents : {p // D p (target t)} → Bool) :
    singleIndicatorCoordinate D target t
      ⟨some (target t), extendParentRow D (target t) (target t) parents false⟩ =
      .inl ⟨target t, parents⟩ := by
  classical
  simp only [singleIndicatorCoordinate, dif_pos rfl, extendParentRow, Bool.false_eq_true,
    if_false, oldParentRow]

theorem targeted_coordinate_replacement (D : V → V → Prop) (target : T → V) (t : T)
    (parents : {p // D p (target t)} → Bool) :
    singleIndicatorCoordinate D target t
      ⟨some (target t), extendParentRow D (target t) (target t) parents true⟩ =
      .inr (.inl ⟨t, parents⟩) := by
  classical
  simp only [singleIndicatorCoordinate, dif_pos rfl, extendParentRow, if_true, oldParentRow]

def baselineCoordinate (D : V → V → Prop) (target : T → V) : Coordinate D → SharedCoordinate D target :=
  Sum.inl

theorem baseline_coordinate_injective (D : V → V → Prop) (target : T → V) :
    Function.Injective (baselineCoordinate D target) := by
  intro «first» second same
  exact Sum.inl.inj same

theorem shared_baseline_polynomial_nonzero (D : V → V → Prop) (target : T → V)
    (p : MvPolynomial (Coordinate D) ℚ) (nonzero : p ≠ 0) :
    MvPolynomial.rename (baselineCoordinate D target) p ≠ 0 := by
  intro zero
  exact nonzero ((MvPolynomial.rename_eq_zero_iff_of_injective p
    (baseline_coordinate_injective D target)).mp zero)

theorem shared_indicator_polynomial_nonzero (D : V → V → Prop) (target : T → V) (t : T)
    (p : MvPolynomial (Coordinate (AddIndicator D (target t))) ℚ) (nonzero : p ≠ 0) :
    MvPolynomial.rename (singleIndicatorCoordinate D target t) p ≠ 0 := by
  intro zero
  exact nonzero ((MvPolynomial.rename_eq_zero_iff_of_injective p
    (single_indicator_coordinate_injective D target t)).mp zero)

/-- Every experiment evaluates a pullback of ONE theta on the SAME
registry. This equation does not choose a separate baseline for a target. -/
theorem shared_indicator_eval (D : V → V → Prop) (target : T → V) (t : T)
    (θ : SharedCoordinate D target → ℚ)
    (p : MvPolynomial (Coordinate (AddIndicator D (target t))) ℚ) :
    MvPolynomial.eval θ (MvPolynomial.rename (singleIndicatorCoordinate D target t) p) =
      MvPolynomial.eval (θ ∘ singleIndicatorCoordinate D target t) p :=
  MvPolynomial.eval_rename _ _ _

end RestrictedCausal.ProbabilitySource.BinaryCPT
