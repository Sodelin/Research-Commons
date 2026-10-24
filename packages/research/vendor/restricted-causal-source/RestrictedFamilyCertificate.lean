import SharedSeparatorMEC

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Compose the actual HPL-based restricted observed/indicator query families
with the proved shared-separator sufficiency. All named augmentations are
of the SAME two original sources. The family-answer premises are stated
explicitly here; deriving them from a legal bounded history is downstream.
This is not an extra full-signature or equivalence oracle.

Attribution: HPL's marginal ancestor mask/refined separator results and the
classical Richardson--Spirtes / Ali--Richardson--Spirtes MAG machinery.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation HPLTarget DiscriminatingStatus WeakInducing
open IndicatorAncestry FiniteTargetImage CommonObserved VertexActivePaths

universe u v w v' w'

def ObservedFamilyAgreement {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop) : Prop :=
  ∀ x y, x ≠ y → ∀ W : UntargetedOutsidePair T x y → Bool,
    (ActiveConnection (arrowGraph D.arrow) (SelectedCondition (PairCondition T A x y W))
        (Observed x) (Observed y) ↔
      ActiveConnection (arrowGraph E.arrow) (SelectedCondition (PairCondition T A x y W))
        (Observed x) (Observed y))

def IndicatorFamilyAgreement {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop) : Prop :=
  ∀ t, T t → ∀ x, t ≠ x → ∀ W : UntargetedOutsideEndpoint T x → Bool,
    (ActiveConnection (arrowGraph (augmentSource D t).arrow)
        (SelectedCondition (InvarianceCondition (IndicatorCondition T A x W)))
        (Observed none) (Observed (some x)) ↔
      ActiveConnection (arrowGraph (augmentSource E t).arrow)
        (SelectedCondition (InvarianceCondition (IndicatorCondition T A x W)))
        (Observed none) (Observed (some x)))

theorem observed_agreement_skeleton {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop)
    (exactD : AvailableMaskExact D T A) (exactE : AvailableMaskExact E T A)
    (answers : ObservedFamilyAgreement D E T A) :
    ∀ x y, Adjacent (mag D) x y ↔ Adjacent (mag E) x y := by
  intro x y
  by_cases distinct : x ≠ y
  · rw [mag_adjacent_iff_inducing, mag_adjacent_iff_inducing,
      observed_family_complete D T A exactD x y distinct,
      observed_family_complete E T A exactE x y distinct]
    exact ⟨fun h W => (answers x y distinct W).mp (h W),
      fun h W => (answers x y distinct W).mpr (h W)⟩
  · have same : x = y := by by_contra different; exact distinct different
    subst y
    exact ⟨fun ⟨mx, my, edge⟩ => (mag_no_self_edge D x mx my edge).elim,
      fun ⟨mx, my, edge⟩ => (mag_no_self_edge E x mx my edge).elim⟩

theorem observed_agreement_shared {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop)
    (exactD : AvailableMaskExact D T A)
    (answers : ObservedFamilyAgreement D E T A) : SharedSeparators (mag D) (mag E) := by
  classical
  intro x y distinct missing
  have witness : ∃ W : UntargetedOutsidePair T x y → Bool,
      ¬ ActiveConnection (arrowGraph D.arrow) (SelectedCondition (PairCondition T A x y W))
        (Observed x) (Observed y) := by
    by_contra none
    apply missing
    apply (mag_adjacent_iff_inducing D x y).mpr
    apply (observed_family_complete D T A exactD x y distinct).mpr
    intro W
    by_contra separated
    exact none ⟨W, separated⟩
  obtain ⟨W, sepD⟩ := witness
  have sepE := fun connection => sepD ((answers x y distinct W).mpr connection)
  have notX := pair_condition_excludes_left T A x y W
  have notY := pair_condition_excludes_right T A x y W
  exact ⟨PairCondition T A x y W, notX, notY,
    source_separator_is_mag_separator D _ x y notX notY sepD,
    source_separator_is_mag_separator E _ x y notX notY sepE⟩

theorem indicator_agreement_inducing {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop)
    (exactD : AvailableMaskExact D T A) (exactE : AvailableMaskExact E T A)
    (answers : IndicatorFamilyAgreement D E T A) (t : X) (available : T t) (x : X) :
    InducingPath (augmentSource D t) none (some x) ↔
      InducingPath (augmentSource E t) none (some x) := by
  by_cases distinct : t ≠ x
  · rw [indicator_family_complete D T A exactD t x, indicator_family_complete E T A exactE t x]
    exact ⟨fun h W => (answers t available x distinct W).mp (h W),
      fun h W => (answers t available x distinct W).mpr (h W)⟩
  · have same : t = x := by by_contra different; exact distinct different
    subst x
    exact ⟨fun _ => own_target_inducing E t, fun _ => own_target_inducing D t⟩

theorem augmented_agreement_skeleton {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop)
    (exactD : AvailableMaskExact D T A) (exactE : AvailableMaskExact E T A)
    (baseline : ∀ x y, Adjacent (mag D) x y ↔ Adjacent (mag E) x y)
    (answers : IndicatorFamilyAgreement D E T A) (t : X) (available : T t) :
    ∀ x y, Adjacent (mag (augmentSource D t)) x y ↔ Adjacent (mag (augmentSource E t)) x y := by
  intro x y
  rw [mag_adjacent_iff_inducing, mag_adjacent_iff_inducing]
  cases x with
  | none =>
      cases y with
      | none => exact ⟨fun h => (h.1 rfl).elim, fun h => (h.1 rfl).elim⟩
      | some y => exact indicator_agreement_inducing D E T A exactD exactE answers t available y
  | some x =>
      cases y with
      | none =>
          have forward := indicator_agreement_inducing D E T A exactD exactE answers t available x
          exact ⟨fun h => inducing_symm (augmentSource E t)
              (forward.mp (inducing_symm (augmentSource D t) h)),
            fun h => inducing_symm (augmentSource D t)
              (forward.mpr (inducing_symm (augmentSource E t) h))⟩
      | some y =>
          exact (old_inducing_iff D t x y).trans
            (((mag_adjacent_iff_inducing D x y).symm.trans
              ((baseline x y).trans (mag_adjacent_iff_inducing E x y))).trans
                (old_inducing_iff E t x y).symm)

/-- A missing root--observed edge has a genuine common SOURCE separator
from the queried indicator family. The named own-target edge cannot be
missing and therefore requires no additional conditional query. -/
theorem indicator_agreement_source_separator {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop) (exactD : AvailableMaskExact D T A)
    (answers : IndicatorFamilyAgreement D E T A) (t : X) (available : T t) (x : X)
    (missing : ¬ InducingPath (augmentSource D t) none (some x)) :
    ∃ K : Option X → Prop, ¬ K none ∧ ¬ K (some x) ∧
      ¬ ActiveConnection (arrowGraph (augmentSource D t).arrow) (SelectedCondition K)
        (Observed none) (Observed (some x)) ∧
      ¬ ActiveConnection (arrowGraph (augmentSource E t).arrow) (SelectedCondition K)
        (Observed none) (Observed (some x)) := by
  classical
  have distinct : t ≠ x := by intro same; subst x; exact missing (own_target_inducing D t)
  have witness : ∃ W : UntargetedOutsideEndpoint T x → Bool,
      ¬ ActiveConnection (arrowGraph (augmentSource D t).arrow)
        (SelectedCondition (InvarianceCondition (IndicatorCondition T A x W)))
        (Observed none) (Observed (some x)) := by
    by_contra none
    apply missing
    apply (indicator_family_complete D T A exactD t x).mpr
    intro W
    by_contra separated
    exact none ⟨W, separated⟩
  obtain ⟨W, sepD⟩ := witness
  exact ⟨InvarianceCondition (IndicatorCondition T A x W), id,
    indicator_condition_excludes_endpoint T A x W, sepD,
    fun connection => sepD ((answers t available x distinct W).mpr connection)⟩

theorem augmented_agreement_shared {X : Type u} {S : Type v} {L : Type w}
    {S' : Type v'} {L' : Type w'}
    (D : SourceDAG X S L) (E : SourceDAG X S' L')
    (T : X → Prop) (A : X → X → Prop) (exactD : AvailableMaskExact D T A)
    (baseline : SharedSeparators (mag D) (mag E))
    (answers : IndicatorFamilyAgreement D E T A) (t : X) (available : T t) :
    SharedSeparators (mag (augmentSource D t)) (mag (augmentSource E t)) := by
  intro x y distinct missing
  have notInducing := fun h => missing ((mag_adjacent_iff_inducing (augmentSource D t) x y).mpr h)
  cases x with
  | none =>
      cases y with
      | none => exact (distinct rfl).elim
      | some y =>
          obtain ⟨K, notRoot, notY, sepD, sepE⟩ :=
            indicator_agreement_source_separator D E T A exactD answers t available y notInducing
          exact ⟨K, notRoot, notY,
            source_separator_is_mag_separator (augmentSource D t) K none (some y) notRoot notY sepD,
            source_separator_is_mag_separator (augmentSource E t) K none (some y) notRoot notY sepE⟩
  | some x =>
      cases y with
      | none =>
          have reversedMissing : ¬ InducingPath (augmentSource D t) none (some x) :=
            fun h => notInducing (inducing_symm (augmentSource D t) h)
          obtain ⟨K, notRoot, notX, sepD, sepE⟩ :=
            indicator_agreement_source_separator D E T A exactD answers t available x reversedMissing
          have reverseD := fun connection => sepD (active_connection_symm
            (arrowGraph (augmentSource D t).arrow) (original_arrow_mixed_laws (augmentSource D t))
            (SelectedCondition K) connection)
          have reverseE := fun connection => sepE (active_connection_symm
            (arrowGraph (augmentSource E t).arrow) (original_arrow_mixed_laws (augmentSource E t))
            (SelectedCondition K) connection)
          exact ⟨K, notX, notRoot,
            source_separator_is_mag_separator (augmentSource D t) K (some x) none notX notRoot reverseD,
            source_separator_is_mag_separator (augmentSource E t) K (some x) none notX notRoot reverseE⟩
      | some y =>
          have oldDistinct : x ≠ y := fun same => distinct (congrArg some same)
          have oldMissing : ¬ Adjacent (mag D) x y := fun h =>
            notInducing ((old_inducing_iff D t x y).mpr ((mag_adjacent_iff_inducing D x y).mp h))
          obtain ⟨Z, notX, notY, sepD, sepE⟩ := baseline x y oldDistinct oldMissing
          have sourceD := fun connection => sepD ((selected_mag_connection_iff D Z x y notX notY).mp connection)
          have sourceE := fun connection => sepE ((selected_mag_connection_iff E Z x y notX notY).mp connection)
          have augmentedD := fun connection => sourceD ((old_observed_active_iff D t (InvarianceCondition Z) x y).mp connection)
          have augmentedE := fun connection => sourceE ((old_observed_active_iff E t (InvarianceCondition Z) x y).mp connection)
          exact ⟨InvarianceCondition Z, notX, notY,
            source_separator_is_mag_separator (augmentSource D t) _ (some x) (some y) notX notY augmentedD,
            source_separator_is_mag_separator (augmentSource E t) _ (some x) (some y) notX notY augmentedE⟩

/-- Full all-observed elementary signature from precisely the restricted
family answers and available marginal mask. E is ONE original source across
every target, not a separately selected rival for each augmentation. -/
theorem restricted_families_complete {X : Type u}
    (D E : FiniteSource X) (T : X → Prop) (A : X → X → Prop)
    (exactD : AvailableMaskExact D.dag T A) (exactE : AvailableMaskExact E.dag T A)
    (observed : ObservedFamilyAgreement D.dag E.dag T A)
    (indicator : IndicatorFamilyAgreement D.dag E.dag T A) : SameElementarySignature T D E := by
  have baselineSkeleton := observed_agreement_skeleton D.dag E.dag T A exactD exactE observed
  have baselineShared := observed_agreement_shared D.dag E.dag T A exactD observed
  constructor
  · intro Z x y _ notX notY
    exact shared_separators_selected_source_connection_iff D.dag E.dag
      baselineSkeleton baselineShared Z x y notX notY
  · intro t Z x notX
    have skeleton := augmented_agreement_skeleton D.dag E.dag T A exactD exactE
      baselineSkeleton indicator t.val t.property
    have shared := augmented_agreement_shared D.dag E.dag T A exactD baselineShared indicator t.val t.property
    exact shared_separators_selected_source_connection_iff (augmentSource D.dag t.val)
      (augmentSource E.dag t.val) skeleton shared (InvarianceCondition Z) none (some x) id notX

end RestrictedCausal.PartialQueries
