import RestrictedHistoryCompleteness
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Sigma

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

An actual finite two-phase transcript construction, for EVERY Boolean
response vector. All first-stage responses precede the mask-dependent second
stage. Complete coverage, legal actions and response-independent length are
proved, then composed with the original common-source marked-TCM decoder.

The generic finite enumeration below uses the explicitly NONCOMPUTABLE
Finset.toList choice. The construction also accepts any supplied concrete
enumerations. No extracted executable query policy or G7 port is claimed.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage FiniteGraphDecision TranscriptDecoder IndicatorAncestry

universe u

abbrev MarginalIndex {X : Type u} (T : X → Prop) :=
  {p : {x : X // T x} × X // p.1.val ≠ p.2}

abbrev ObservedPair (X : Type u) [LT X] := {p : X × X // p.1 < p.2}

abbrev ObservedIndex {X : Type u} [LT X] (T : X → Prop) :=
  Σ p : ObservedPair X, UntargetedOutsidePair T p.val.1 p.val.2 → Bool

abbrev ConditionalIndex {X : Type u} (T : X → Prop) :=
  Σ p : MarginalIndex T, UntargetedOutsideEndpoint T p.val.2 → Bool

structure Enumeration (I : Type u) [Fintype I] where
  items : List I
  complete : ∀ i, i ∈ items
  nodup : items.Nodup
  length : items.length = Fintype.card I

/-- Mathematical enumeration witness, not an executed or extracted routine. -/
noncomputable def finiteEnumeration (I : Type u) [Fintype I] : Enumeration I where
  items := Finset.univ.toList
  complete i := Finset.mem_toList.mpr (Finset.mem_univ i)
  nodup := Finset.nodup_toList _
  length := by rw [Finset.length_toList]; rfl

def maskFromReplies {X : Type u} [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (r : MarginalIndex T → Bool) (t x : X) : Bool :=
  if available : T t then
    if distinct : t ≠ x then !(r ⟨(⟨t, available⟩, x), distinct⟩) else false
  else false

theorem mask_from_replies_complement {X : Type u} [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (r : MarginalIndex T → Bool) (q : MarginalIndex T) :
    !(maskFromReplies T r q.val.1.val q.val.2) = r q := by
  simp only [maskFromReplies, dif_pos q.val.1.property, dif_pos q.property]
  cases r q <;> rfl

def marginalIndexAction {X : Type u} {T : X → Prop} (q : MarginalIndex T) : ElementaryAction X T :=
  marginalAction q.val.1 q.val.2

def observedIndexAction {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (q : ObservedIndex T) :
    ElementaryAction X T := pairAction T m q.1.val.1 q.1.val.2 q.2

def conditionalIndexAction {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (q : ConditionalIndex T) :
    ElementaryAction X T := indicatorAction T m q.1.val.1 q.1.val.2 q.2

def twoPhaseHistory {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool) :
    History X T :=
  (marginals.items.map (fun q => (marginalIndexAction q, r q)) ++
    observed.items.map (fun q => (observedIndexAction T (maskFromReplies T r) q, s q))) ++
    conditional.items.map (fun q => (conditionalIndexAction T (maskFromReplies T r) q, t q))

theorem two_phase_marginal_member {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool)
    (q : MarginalIndex T) :
    (marginalIndexAction q, r q) ∈ twoPhaseHistory T marginals observed conditional r s t := by
  apply List.mem_append.mpr
  left
  exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨q, marginals.complete q, rfl⟩))

theorem two_phase_observed_member {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool)
    (q : ObservedIndex T) :
    (observedIndexAction T (maskFromReplies T r) q, s q) ∈
      twoPhaseHistory T marginals observed conditional r s t := by
  apply List.mem_append.mpr
  left
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q, observed.complete q, rfl⟩))

theorem two_phase_conditional_member {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool)
    (q : ConditionalIndex T) :
    (conditionalIndexAction T (maskFromReplies T r) q, t q) ∈
      twoPhaseHistory T marginals observed conditional r s t := by
  exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨q, conditional.complete q, rfl⟩))

theorem two_phase_recorded {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool) :
    MarginalsRecorded (maskFromReplies T r) (twoPhaseHistory T marginals observed conditional r s t) := by
  intro target x distinct
  let q : MarginalIndex T := ⟨(target, x), distinct⟩
  have member := two_phase_marginal_member T marginals observed conditional r s t q
  change (marginalIndexAction q, !(maskFromReplies T r q.val.1.val q.val.2)) ∈ _
  rw [mask_from_replies_complement]
  exact member

theorem two_phase_covered {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool) :
    RestrictedCoverage T (maskFromReplies T r) (twoPhaseHistory T marginals observed conditional r s t) := by
  constructor
  · intro x y ordered W
    let q : ObservedIndex T := ⟨⟨(x, y), ordered⟩, W⟩
    exact ⟨s q, two_phase_observed_member T marginals observed conditional r s t q⟩
  · intro target x distinct W
    let q : ConditionalIndex T := ⟨⟨(target, x), distinct⟩, W⟩
    exact ⟨t q, two_phase_conditional_member T marginals observed conditional r s t q⟩

/-- Legality holds even on response vectors that no source can realize. -/
theorem two_phase_all_actions_legal {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool) :
    ∀ row ∈ twoPhaseHistory T marginals observed conditional r s t, LegalAction T row.1 := by
  intro row member
  rcases List.mem_append.mp member with firstTwo | third
  · rcases List.mem_append.mp firstTwo with first | second
    · obtain ⟨q, _, same⟩ := List.mem_map.mp first
      subst row
      exact marginal_action_legal q.val.1 q.val.2
    · obtain ⟨q, _, same⟩ := List.mem_map.mp second
      subst row
      exact pair_action_legal T (maskFromReplies T r) q.1.val.1 q.1.val.2 (ne_of_lt q.1.property) q.2
  · obtain ⟨q, _, same⟩ := List.mem_map.mp third
    subst row
    exact indicator_action_legal T (maskFromReplies T r) q.1.val.1 q.1.val.2 q.2

def coordinateBudget {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] : Nat :=
  Fintype.card (MarginalIndex T) + Fintype.card (ObservedIndex T) + Fintype.card (ConditionalIndex T)

theorem two_phase_length {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool) :
    (twoPhaseHistory T marginals observed conditional r s t).length = coordinateBudget T := by
  simp only [twoPhaseHistory, coordinateBudget, List.length_append, List.length_map,
    marginals.length, observed.length, conditional.length]

theorem two_phase_target_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T))
    (r : MarginalIndex T → Bool) (s : ObservedIndex T → Bool) (t : ConditionalIndex T → Bool)
    (D : FiniteSource X)
    (honest : SourceConsistent D (twoPhaseHistory T marginals observed conditional r s t))
    (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ decodeHistory T (twoPhaseHistory T marginals observed conditional r s t), decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G :=
  restricted_history_target_exact T D (maskFromReplies T r)
    (twoPhaseHistory T marginals observed conditional r s t)
    (two_phase_recorded T marginals observed conditional r s t)
    (two_phase_covered T marginals observed conditional r s t) honest G

end RestrictedCausal.PartialQueries
