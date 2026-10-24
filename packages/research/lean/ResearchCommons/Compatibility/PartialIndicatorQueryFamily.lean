import RefinedIndicatorSeparator

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The indicator-observed part of the reviewed partial-intervention certificate,
derived from the prior HPL refined separator. Only named available targets
are used by the eventual policy. Counting below is query coordinates, never
samples, interventions or arbitrary binary full-law oracle queries.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation IndicatorAncestry RefinedSeparator RefinedIndicator
open FiniteTargetImage
open SourceSelection (AncestorOf)

universe u v w

def UntargetedOutsideEndpoint {X : Type u} (T : X → Prop) (x : X) :=
  {z : X // ¬ T z ∧ z ≠ x}

/-- Equality on the original one-endpoint subtype comes from the supplied X. -/
instance untargetedOutsideEndpointDecidableEq {X : Type u} [DecidableEq X]
    (T : X → Prop) (x : X) : DecidableEq (UntargetedOutsideEndpoint T x) := by
  change DecidableEq {z : X // ¬ T z ∧ z ≠ x}
  infer_instance

/-- Enumerate the same original untargeted variables; no new query coordinate. -/
instance untargetedOutsideEndpointFintype {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (x : X) : Fintype (UntargetedOutsideEndpoint T x) := by
  change Fintype {z : X // ¬ T z ∧ z ≠ x}
  exact Fintype.subtype (Finset.univ.filter (fun z : X => ¬ T z ∧ z ≠ x))
    (by intro z; simp)

def IndicatorCondition {X : Type u} (T : X → Prop) (A : X → X → Prop) (x : X)
    (W : UntargetedOutsideEndpoint T x → Bool) (z : X) : Prop :=
  z ≠ x ∧ ((T z ∧ A z x) ∨
    ∃ w : UntargetedOutsideEndpoint T x, w.val = z ∧ W w = true)

theorem indicator_condition_excludes_endpoint {X : Type u}
    (T : X → Prop) (A : X → X → Prop) (x : X)
    (W : UntargetedOutsideEndpoint T x → Bool) : ¬ IndicatorCondition T A x W x :=
  fun h => h.1 rfl

theorem indicator_family_contains_refined_separator {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (T : X → Prop) (A : X → X → Prop)
    (exactMask : AvailableMaskExact D T A) (x : X) :
    ∃ W : UntargetedOutsideEndpoint T x → Bool,
      (∀ z, IndicatorCondition T A x W z →
        AncestorOf (arrowGraph D.arrow) (OneEndpointSelection x) (Observed z)) ∧
      (∀ z, z ≠ x → MarginalMask D z x → IndicatorCondition T A x W z) := by
  classical
  let W : UntargetedOutsideEndpoint T x → Bool := fun z => decide (MarginalMask D z.val x)
  refine ⟨W, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨hzx, (⟨ht, hm⟩ | ⟨w, hw, hW⟩)⟩
    · exact mask_ancestor_endpoint_or_selection D ((exactMask z x ht hzx).mp hm)
    · have hm : MarginalMask D w.val x := by simpa only [W, decide_eq_true_eq] using hW
      exact mask_ancestor_endpoint_or_selection D (by simpa only [hw] using hm)
  · intro z hzx hm
    refine ⟨hzx, ?_⟩
    by_cases ht : T z
    · exact Or.inl ⟨ht, (exactMask z x ht hzx).mpr hm⟩
    · right
      refine ⟨⟨z, ht, hzx⟩, rfl, ?_⟩
      simpa only [W, decide_eq_true_eq] using hm

theorem indicator_family_complete {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (T : X → Prop) (A : X → X → Prop)
    (exactMask : AvailableMaskExact D T A) (t x : X) :
    InducingPath (augmentSource D t) none (some x) ↔
      ∀ W : UntargetedOutsideEndpoint T x → Bool,
      ActiveConnection (arrowGraph (augmentSource D t).arrow)
        (SelectedCondition (InvarianceCondition (IndicatorCondition T A x W)))
        (Observed none) (Observed (some x)) := by
  constructor
  · intro hind W
    exact (inducing_implies_inseparable (augmentSource D t) none (some x) hind).2
      (InvarianceCondition (IndicatorCondition T A x W)) (fun h => h.elim)
      (indicator_condition_excludes_endpoint T A x W)
  · intro allConnected
    obtain ⟨W, upper, lower⟩ := indicator_family_contains_refined_separator D T A exactMask x
    exact (refined_indicator_separator D t x (IndicatorCondition T A x W)
      (indicator_condition_excludes_endpoint T A x W) upper lower).mpr (allConnected W)

/-- The named root's own target is always adjacent and costs no separator
queries. Its structural edge is known, even when selection changes a MAG
endpoint mark. No assertion about the latter mark is made here. -/
theorem own_target_inducing {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (t : X) : InducingPath (augmentSource D t) none (some t) := by
  refine ⟨(by intro h; cases h), some .head, [⟨Observed (some t), some .head⟩], ?_, ?_⟩
  · exact .cons ⟨.tail, .head, (indicator_raw_edge D t _ _ _).mpr ⟨rfl, rfl, rfl⟩,
      rfl, trivial⟩ (.nil _)
  · change ([Observed none, Observed (some t)] : List (SourceVertex (Option X) S L)).Nodup
    refine List.Nodup.cons ?_ (List.nodup_singleton _)
    intro h
    have heq : (Observed none : SourceVertex (Option X) S L) = Observed (some t) :=
      List.mem_singleton.mp h
    cases heq

theorem indicator_pair_query_count {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (x : X) :
    Fintype.card (UntargetedOutsideEndpoint T x → Bool) =
      2 ^ Fintype.card (UntargetedOutsideEndpoint T x) := by
  simp only [Fintype.card_fun, Fintype.card_bool]

end RestrictedCausal.PartialQueries
