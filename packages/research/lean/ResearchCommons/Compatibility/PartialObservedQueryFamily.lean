import RefinedObservedSeparator
import Mathlib.Data.Fintype.BigOperators

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. Not elaborated or executed.

Observed-pair part of the fixed partial-intervention query certificate.
HPL Proposition 3 is prior work. The finite family searches only untargeted
conditioning variables, while retaining every observed endpoint and the full
inducing-path skeleton. The indicator-pair certificate, complete MAG MEC,
whole-history policy and full target decoder composition remain downstream.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation IndicatorAncestry RefinedSeparator
open SourceSelection (AncestorOf)

universe u v w

def UntargetedOutsidePair {X : Type u} (T : X → Prop) (x y : X) :=
  {z : X // ¬ T z ∧ z ≠ x ∧ z ≠ y}

/-- The original finite subtype is enumerated using the supplied finite X,
decidable target predicate and equality. No extra source/query is admitted. -/
instance untargetedOutsidePairFintype {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (x y : X) : Fintype (UntargetedOutsidePair T x y) := by
  change Fintype {z : X // ¬ T z ∧ z ≠ x ∧ z ≠ y}
  exact Fintype.subtype (Finset.univ.filter (fun z : X => ¬ T z ∧ z ≠ x ∧ z ≠ y))
    (by intro z; simp)

/-- `A t x` is the reported marginal dependence of I_t and x given selection.
Only entries with available t and t distinct from x or y are consulted.
The family does not query an unavailable intervention or discard an observed
endpoint. Each Boolean W specifies one subset of U minus the two endpoints. -/
def PairCondition {X : Type u} (T : X → Prop) (A : X → X → Prop) (x y : X)
    (W : UntargetedOutsidePair T x y → Bool) (z : X) : Prop :=
  z ≠ x ∧ z ≠ y ∧ ((T z ∧ (A z x ∨ A z y)) ∨
    ∃ w : UntargetedOutsidePair T x y, w.val = z ∧ W w = true)

theorem pair_condition_excludes_left {X : Type u} (T : X → Prop) (A : X → X → Prop)
    (x y : X) (W : UntargetedOutsidePair T x y → Bool) : ¬ PairCondition T A x y W x :=
  fun h => h.1 rfl

theorem pair_condition_excludes_right {X : Type u} (T : X → Prop) (A : X → X → Prop)
    (x y : X) (W : UntargetedOutsidePair T x y → Bool) : ¬ PairCondition T A x y W y :=
  fun h => h.2.1 rfl

/-- Exactness is required only for the physically available, nontrivial
marginal coordinates. This premise will be established from the first phase
of the legal query policy; it is not assumed for untargeted indicators. -/
def AvailableMaskExact {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (T : X → Prop) (A : X → X → Prop) : Prop :=
  ∀ t x, T t → t ≠ x → (A t x ↔ MarginalMask D t x)

theorem mask_pair_ancestor {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y z : X)
    (h : MarginalMask D z x ∨ MarginalMask D z y) : EndpointAncestor D x y (Observed z) := by
  rcases h with hx | hy
  · apply ancestor_mono (C := OneEndpointSelection x) (fun a ha => ?_)
      (mask_ancestor_endpoint_or_selection D hx)
    rcases ha with heq | hs
    · exact Or.inl heq
    · exact Or.inr (Or.inr hs)
  · apply ancestor_mono (C := OneEndpointSelection y) (fun a ha => ?_)
      (mask_ancestor_endpoint_or_selection D hy)
    rcases ha with heq | hs
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr hs)

/-- There is a member of the enumerated family containing exactly the full
two-mask union outside the endpoints. Its untargeted bits are an existence
witness in the proof, not measurements supplied to the policy. -/
theorem pair_family_contains_refined_separator {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (T : X → Prop) (A : X → X → Prop)
    (exactMask : AvailableMaskExact D T A) (x y : X) :
    ∃ W : UntargetedOutsidePair T x y → Bool,
      (∀ z, PairCondition T A x y W z → EndpointAncestor D x y (Observed z)) ∧
      (∀ z, z ≠ x → z ≠ y →
        (MarginalMask D z x ∨ MarginalMask D z y) → PairCondition T A x y W z) := by
  classical
  let W : UntargetedOutsidePair T x y → Bool :=
    fun z => decide (MarginalMask D z.val x ∨ MarginalMask D z.val y)
  refine ⟨W, ?_, ?_⟩
  · intro z hz
    rcases hz with ⟨hzx, hzy, (⟨ht, hm⟩ | ⟨w, hw, hW⟩)⟩
    · apply mask_pair_ancestor D x y z
      exact hm.elim (fun h => Or.inl ((exactMask z x ht hzx).mp h))
        (fun h => Or.inr ((exactMask z y ht hzy).mp h))
    · have hm : MarginalMask D w.val x ∨ MarginalMask D w.val y := by
        simpa only [W, decide_eq_true_eq] using hW
      exact mask_pair_ancestor D x y z (by simpa only [hw] using hm)
  · intro z hzx hzy hm
    refine ⟨hzx, hzy, ?_⟩
    by_cases ht : T z
    · left
      refine ⟨ht, ?_⟩
      exact hm.elim (fun h => Or.inl ((exactMask z x ht hzx).mpr h))
        (fun h => Or.inr ((exactMask z y ht hzy).mpr h))
    · right
      refine ⟨⟨z, ht, hzx, hzy⟩, rfl, ?_⟩
      simpa only [W, decide_eq_true_eq] using hm

/-- Full observed-pair inducing adjacency is exactly the absence of a
separator in this restricted family. This proves the graph obligation behind
the observed-pair phase; it does not identify edge marks or a complete MEC. -/
theorem observed_family_complete {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (T : X → Prop) (A : X → X → Prop)
    (exactMask : AvailableMaskExact D T A) (x y : X) (hne : x ≠ y) :
    InducingPath D x y ↔ ∀ W : UntargetedOutsidePair T x y → Bool,
      ActiveConnection (arrowGraph D.arrow) (SelectedCondition (PairCondition T A x y W))
        (Observed x) (Observed y) := by
  constructor
  · intro hind W
    exact (inducing_implies_inseparable D x y hind).2 (PairCondition T A x y W)
      (pair_condition_excludes_left T A x y W) (pair_condition_excludes_right T A x y W)
  · intro allConnected
    obtain ⟨W, upper, lower⟩ := pair_family_contains_refined_separator D T A exactMask x y
    exact (refined_observed_separator D x y hne (PairCondition T A x y W)
      (pair_condition_excludes_left T A x y W) (pair_condition_excludes_right T A x y W)
      upper lower).mpr (allConnected W)

/-- A direct elementary-CI query for each W suffices. This counts query
coordinates, not physical interventions, observations or statistical samples.
Duplicate conditioning sets may be retained, so no injectivity is needed. -/
theorem observed_pair_query_count {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (x y : X) :
    Fintype.card (UntargetedOutsidePair T x y → Bool) =
      2 ^ Fintype.card (UntargetedOutsidePair T x y) := by
  simp only [Fintype.card_fun, Fintype.card_bool]

end RestrictedCausal.PartialQueries
