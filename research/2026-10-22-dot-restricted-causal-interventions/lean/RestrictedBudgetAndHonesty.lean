import TwoPhaseRestrictedHistory

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The exact original indexed B budget, including k(n-1) marginal coordinates,
and honest graphical response instantiation for every ORIGINAL finite source.
Queries are elementary coordinates, not samples or physical interventions.
The oracle evaluation below is a mathematical response specification for
an arbitrary unknown source, not a claim that its arrows are computably known.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage FiniteGraphDecision TranscriptDecoder
open scoped BigOperators

universe u

def marginalIndexEquiv {X : Type u} (T : X → Prop) :
    MarginalIndex T ≃ Σ t : {x : X // T x}, {x : X // t.val ≠ x} where
  toFun q := ⟨q.val.1, q.val.2, q.property⟩
  invFun q := ⟨(q.1, q.2.val), q.2.property⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

theorem marginal_index_card {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] :
    Fintype.card (MarginalIndex T) = Fintype.card {x : X // T x} * (Fintype.card X - 1) := by
  rw [Fintype.card_congr (marginalIndexEquiv T), Fintype.card_sigma]
  have fiber (t : {x : X // T x}) :
      Fintype.card {x : X // t.val ≠ x} = Fintype.card X - 1 := by
    rw [Fintype.card_subtype_compl (fun x => t.val = x), Fintype.card_subtype_eq']
  simp only [fiber, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Exactly the manuscript's indexed B formula. Every observed unordered
pair appears once; every available t and distinct x appears once. The
untargeted-subset sizes exclude their actual endpoints. -/
theorem coordinate_budget_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] :
    coordinateBudget T =
      Fintype.card {x : X // T x} * (Fintype.card X - 1) +
        (∑ p : ObservedPair X, 2 ^ Fintype.card (UntargetedOutsidePair T p.val.1 p.val.2)) +
        (∑ p : MarginalIndex T, 2 ^ Fintype.card (UntargetedOutsideEndpoint T p.val.2)) := by
  unfold coordinateBudget
  rw [marginal_index_card]
  simp only [ObservedIndex, ConditionalIndex, Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool]

noncomputable def graphicalReply {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) (a : ElementaryAction X T) : Bool := by
  classical
  exact decide (PositiveAnswer D a)

theorem graphical_reply_correct {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) (a : ElementaryAction X T) :
    PositiveAnswer D a ↔ graphicalReply D a = true := by
  classical
  simp only [graphicalReply, decide_eq_true_eq]

noncomputable def honestMarginalReplies {X : Type u} [DecidableEq X]
    (T : X → Prop) (D : FiniteSource X) : MarginalIndex T → Bool :=
  fun q => graphicalReply D (marginalIndexAction q)

noncomputable def honestObservedReplies {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) : ObservedIndex T → Bool :=
  fun q => graphicalReply D
    (observedIndexAction T (maskFromReplies T (honestMarginalReplies T D)) q)

noncomputable def honestConditionalReplies {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X) : ConditionalIndex T → Bool :=
  fun q => graphicalReply D
    (conditionalIndexAction T (maskFromReplies T (honestMarginalReplies T D)) q)

theorem honest_two_phase_consistent {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) (D : FiniteSource X) :
    SourceConsistent D (twoPhaseHistory T marginals observed conditional
      (honestMarginalReplies T D) (honestObservedReplies T D) (honestConditionalReplies T D)) := by
  intro row member
  rcases List.mem_append.mp member with firstTwo | third
  · rcases List.mem_append.mp firstTwo with first | second
    · obtain ⟨q, _, same⟩ := List.mem_map.mp first
      subst row
      exact graphical_reply_correct D (marginalIndexAction q)
    · obtain ⟨q, _, same⟩ := List.mem_map.mp second
      subst row
      exact graphical_reply_correct D _
  · obtain ⟨q, _, same⟩ := List.mem_map.mp third
    subst row
    exact graphical_reply_correct D _

/-- For each original source, the explicit two-phase graphical-oracle
transcript is legal, has the exact response-independent coordinate budget,
and its finite decoder returns the full original marked-TCM class.
Probability realization, extracted execution and G7 integration are separate. -/
theorem honest_two_phase_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) (D : FiniteSource X) :
    ∃ h : History X T,
      h.length = coordinateBudget T ∧
      (∀ row ∈ h, LegalAction T row.1) ∧
      SourceConsistent D h ∧ CompleteHistory D h ∧
      ∀ G : MarkedGraph (CombinedVertex X T),
        ((∃ b ∈ decodeHistory T h, decodeTarget b = G) ↔
          ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G) := by
  let r := honestMarginalReplies T D
  let s := honestObservedReplies T D
  let t := honestConditionalReplies T D
  let h := twoPhaseHistory T marginals observed conditional r s t
  have consistent : SourceConsistent D h := honest_two_phase_consistent T marginals observed conditional D
  have recorded := two_phase_recorded T marginals observed conditional r s t
  have covered := two_phase_covered T marginals observed conditional r s t
  exact ⟨h, two_phase_length T marginals observed conditional r s t,
    two_phase_all_actions_legal T marginals observed conditional r s t, consistent,
    restricted_history_complete T D (maskFromReplies T r) h recorded covered consistent,
    two_phase_target_exact T marginals observed conditional r s t D consistent⟩

end RestrictedCausal.PartialQueries
