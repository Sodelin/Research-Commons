import HardFamilyOriginalSources

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Whole elementary-action adapter: ALL off-coordinate observations agree,
including invalid encodings fixed false and every named invariance query.
Each admitted query can test at most one rival. One original positive
binary source is fixed for an entire run through physicalSource.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation ProbabilitySource PartialQueries TranscriptDecoder
open FiniteTargetImage FiniteGraphDecision

def Exceptional {k u : Nat} (q : Index u) (C : Labels k u → Prop) (x y : Labels k u) : Prop :=
  ((x = .inr q.first ∧ y = .inr q.second) ∨ (x = .inr q.second ∧ y = .inr q.first)) ∧
    ∀ z, C z ↔ exceptionalCondition q z

theorem raw_separations_agree_off_exception {k u : Nat} (q : Index u)
    (C : Labels k u → Prop) (x y : Labels k u) (different : x ≠ y)
    (xOutside : ¬ C x) (yOutside : ¬ C y) (notExceptional : ¬ Exceptional q C x y) :
    (¬ ActiveConnection (arrowGraph (arrow (some q))) C x y) ↔
      (¬ ActiveConnection (arrowGraph (arrow none)) C x y) := by
  have reverseRival := active_connection_symm (arrowGraph (arrow (k := k) (some q)))
    (raw_arrow_mixed_laws _ (arrow_acyclic (some q))) C
  have reverseBase := active_connection_symm (arrowGraph (arrow (k := k) none))
    (raw_arrow_mixed_laws _ (arrow_acyclic none)) C
  cases x with
  | inl t => cases y with
    | inl s =>
        have ne : t ≠ s := fun same => different (congrArg Sum.inl same)
        rw [roots_separated_iff (some q) C t s ne, roots_separated_iff none C t s ne]
    | inr y => exact ⟨fun h => (h (root_untargeted_active (some q) C t y)).elim,
        fun h => (h (root_untargeted_active none C t y)).elim⟩
  | inr x => cases y with
    | inl s => exact ⟨fun h => (h (reverseRival (root_untargeted_active (some q) C s x))).elim,
        fun h => (h (reverseBase (root_untargeted_active none C s x))).elim⟩
    | inr y =>
        have ne : x ≠ y := fun same => different (congrArg Sum.inr same)
        have base := baseline_untargeted_active C x y ne
        have rival : ActiveConnection (arrowGraph (arrow (some q))) C (.inr x) (.inr y) := by
          by_cases forwardPair : x = q.first ∧ y = q.second
          · rcases forwardPair with ⟨rfl, rfl⟩
            by_contra separated
            exact notExceptional ⟨Or.inl ⟨rfl, rfl⟩,
              (exceptional_pair_separated_iff q C xOutside yOutside).mp separated⟩
          · by_cases reversePair : y = q.first ∧ x = q.second
            · rcases reversePair with ⟨rfl, rfl⟩
              apply reverseRival
              by_contra separated
              exact notExceptional ⟨Or.inr ⟨rfl, rfl⟩,
                (exceptional_pair_separated_iff q C yOutside xOutside).mp separated⟩
            · exact untargeted_adjacent_active (some q) C x y ne (by
                intro other equality
                have same : q = other := Option.some.inj equality
                subst other
                exact ⟨forwardPair, reversePair⟩)
        exact ⟨fun h => (h rival).elim, fun h => (h base).elim⟩

def TestsIndex {k u : Nat} (q : Index u) : ElementaryAction (Labels k u) Available → Prop
  | .ci x y b => Exceptional q (BoolCondition b) x y
  | .invariance _ _ _ => False

theorem tests_index_legal {k u : Nat} (q : Index u)
    (action : ElementaryAction (Labels k u) Available) (tests : TestsIndex q action) : LegalAction Available action := by
  cases action with
  | invariance t x b => exact tests.elim
  | ci x y b =>
      have firstOutside : ¬ BoolCondition b (.inr q.first : Labels k u) := by
        intro member
        have h := (tests.2 (.inr q.first)).mp member
        change q.before q.first = true at h
        rw [q.before_first] at h
        cases h
      have secondOutside : ¬ BoolCondition b (.inr q.second : Labels k u) := by
        intro member
        have h := (tests.2 (.inr q.second)).mp member
        change q.before q.second = true at h
        rw [q.before_second] at h
        cases h
      rcases tests.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨fun h => q.distinct (Sum.inr.inj h), firstOutside, secondOutside⟩
      · exact ⟨fun h => q.distinct (Sum.inr.inj h).symm, secondOutside, firstOutside⟩

theorem positive_answers_agree_off_index {k u : Nat} (q : Index u)
    (action : ElementaryAction (Labels k u) Available) (notTested : ¬ TestsIndex q action) :
    PositiveAnswer (originalSource (some q)) action ↔ PositiveAnswer (originalSource (k := k) none) action := by
  cases action with
  | ci x y b =>
      by_cases legal : x ≠ y ∧ ¬ BoolCondition b x ∧ ¬ BoolCondition b y
      · simp only [PositiveAnswer, if_pos legal]
        rw [original_baseline_connection, original_baseline_connection]
        exact raw_separations_agree_off_exception q (BoolCondition b) x y legal.1 legal.2.1 legal.2.2 notTested
      · simp only [PositiveAnswer, if_neg legal]
  | invariance target x b =>
      by_cases legal : ¬ BoolCondition b x
      · simp only [PositiveAnswer, if_pos legal]
        rcases target with ⟨t, available⟩
        cases t with
        | inr z => exact available.elim
        | inl t =>
            rw [original_indicator_connection, original_indicator_connection]
            exact all_indicator_separations_equal (some q) none t (BoolCondition b) x legal
      · simp only [PositiveAnswer, if_neg legal]

theorem tested_index_answers {k u : Nat} (q : Index u)
    (action : ElementaryAction (Labels k u) Available) (tested : TestsIndex q action) :
    PositiveAnswer (originalSource (some q)) action ∧
      ¬ PositiveAnswer (originalSource (k := k) none) action := by
  have legal := tests_index_legal q action tested
  cases action with
  | invariance t x b => exact tested.elim
  | ci x y b =>
      have condition := tested.2
      simp only [PositiveAnswer, if_pos legal, original_baseline_connection]
      rcases tested.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨(exceptional_pair_separated_iff q _ legal.2.1 legal.2.2).mpr condition,
          fun h => h (baseline_untargeted_active _ q.first q.second q.distinct)⟩
      · have reversed : ActiveConnection (arrowGraph (arrow (k := k) (some q))) (BoolCondition b)
            (.inr q.second) (.inr q.first) →
            ActiveConnection (arrowGraph (arrow (some q))) (BoolCondition b) (.inr q.first) (.inr q.second) :=
          active_connection_symm _ (raw_arrow_mixed_laws _ (arrow_acyclic (some q))) _
        exact ⟨fun h => (exceptional_pair_separated_iff q _ legal.2.2 legal.2.1).mpr condition (reversed h),
          fun h => h (baseline_untargeted_active _ q.second q.first q.distinct.symm)⟩

theorem physical_responses_agree_off_index {k u : Nat} (q : Index u)
    (action : ElementaryAction (Labels k u) Available) (notTested : ¬ TestsIndex q action) :
    PhysicalSource.physicalResponse Available (physicalSource (some q)) action =
      PhysicalSource.physicalResponse Available (physicalSource (k := k) none) action := by
  apply (bool_eq_iff_truth_iff _ _).mpr
  exact (PhysicalSource.physical_response_exact Available (physicalSource (some q)) action).symm.trans
    ((positive_answers_agree_off_index q action notTested).trans
      (PhysicalSource.physical_response_exact Available (physicalSource (k := k) none) action))

theorem physical_tested_index_answers {k u : Nat} (q : Index u)
    (action : ElementaryAction (Labels k u) Available) (tested : TestsIndex q action) :
    PhysicalSource.physicalResponse Available (physicalSource (some q)) action = true ∧
      PhysicalSource.physicalResponse Available (physicalSource (k := k) none) action = false := by
  have answers := tested_index_answers q action tested
  refine ⟨(PhysicalSource.physical_response_exact Available (physicalSource (some q)) action).mp answers.1, ?_⟩
  have notTrue : ¬ PhysicalSource.physicalResponse Available (physicalSource (k := k) none) action = true :=
    fun h => answers.2 ((PhysicalSource.physical_response_exact Available (physicalSource (k := k) none) action).mpr h)
  cases value : PhysicalSource.physicalResponse Available (physicalSource (k := k) none) action with
  | false => rfl
  | true => exact (notTrue value).elim

end RestrictedCausal.HardFamily
