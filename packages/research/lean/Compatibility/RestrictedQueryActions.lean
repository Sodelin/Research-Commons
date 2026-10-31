import RestrictedFamilyCertificate
import FiniteTranscriptDecoder

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Concrete elementary actions for the restricted families, using Boolean
marginal readouts. Finite decisions encode the actual conditioning sets;
no full-law query, set-valued action or unavailable indicator is added.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage FiniteGraphDecision TranscriptDecoder IndicatorAncestry

universe u

def Mask {X : Type u} (m : X → X → Bool) (t x : X) : Prop := m t x = true

instance maskDecision {X : Type u} (m : X → X → Bool) : DecidableRel (Mask m) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

def pairConditionDecision {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x y : X)
    (W : UntargetedOutsidePair T x y → Bool) : DecidablePred (PairCondition T (Mask m) x y W) :=
  fun z => by unfold PairCondition; infer_instance

def indicatorConditionDecision {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x : X)
    (W : UntargetedOutsideEndpoint T x → Bool) : DecidablePred (IndicatorCondition T (Mask m) x W) :=
  fun z => by unfold IndicatorCondition; infer_instance

def pairBits {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x y : X)
    (W : UntargetedOutsidePair T x y → Bool) : X → Bool :=
  fun z => @decide (PairCondition T (Mask m) x y W z) (pairConditionDecision T m x y W z)

def indicatorBits {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x : X)
    (W : UntargetedOutsideEndpoint T x → Bool) : X → Bool :=
  fun z => @decide (IndicatorCondition T (Mask m) x W z) (indicatorConditionDecision T m x W z)

theorem pairBits_exact {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x y : X)
    (W : UntargetedOutsidePair T x y → Bool) :
    BoolCondition (pairBits T m x y W) = PairCondition T (Mask m) x y W := by
  funext z
  exact propext (by simp only [BoolCondition, pairBits, decide_eq_true_eq])

theorem indicatorBits_exact {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x : X)
    (W : UntargetedOutsideEndpoint T x → Bool) :
    BoolCondition (indicatorBits T m x W) = IndicatorCondition T (Mask m) x W := by
  funext z
  exact propext (by simp only [BoolCondition, indicatorBits, decide_eq_true_eq])

def marginalAction {X : Type u} {T : X → Prop} (t : {x : X // T x}) (x : X) :
    ElementaryAction X T := .invariance t x (fun _ => false)

def pairAction {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x y : X)
    (W : UntargetedOutsidePair T x y → Bool) : ElementaryAction X T :=
  .ci x y (pairBits T m x y W)

def indicatorAction {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool)
    (t : {x : X // T x}) (x : X) (W : UntargetedOutsideEndpoint T x → Bool) :
    ElementaryAction X T := .invariance t x (indicatorBits T m x W)

theorem marginal_action_legal {X : Type u} {T : X → Prop}
    (t : {x : X // T x}) (x : X) : LegalAction T (marginalAction t x) := by
  change ¬ (false = true)
  decide

theorem pair_action_legal {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (x y : X)
    (distinct : x ≠ y) (W : UntargetedOutsidePair T x y → Bool) :
    LegalAction T (pairAction T m x y W) := by
  change x ≠ y ∧ ¬ BoolCondition (pairBits T m x y W) x ∧ ¬ BoolCondition (pairBits T m x y W) y
  rw [pairBits_exact]
  exact ⟨distinct, pair_condition_excludes_left T (Mask m) x y W,
    pair_condition_excludes_right T (Mask m) x y W⟩

theorem indicator_action_legal {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool)
    (t : {x : X // T x}) (x : X) (W : UntargetedOutsideEndpoint T x → Bool) :
    LegalAction T (indicatorAction T m t x W) := by
  change ¬ BoolCondition (indicatorBits T m x W) x
  rw [indicatorBits_exact]
  exact indicator_condition_excludes_endpoint T (Mask m) x W

theorem pair_answer_exact {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (D : FiniteSource X)
    (x y : X) (distinct : x ≠ y) (W : UntargetedOutsidePair T x y → Bool) :
    PositiveAnswer D (pairAction T m x y W) ↔
      ¬ ActiveConnection (arrowGraph D.dag.arrow) (SelectedCondition (PairCondition T (Mask m) x y W))
        (Observed x) (Observed y) := by
  have legal := pair_action_legal T m x y distinct W
  change (if x ≠ y ∧ ¬ BoolCondition (pairBits T m x y W) x ∧
      ¬ BoolCondition (pairBits T m x y W) y then _ else False) ↔ _
  change x ≠ y ∧ ¬ BoolCondition (pairBits T m x y W) x ∧ ¬ BoolCondition (pairBits T m x y W) y at legal
  rw [if_pos legal, pairBits_exact]

theorem indicator_answer_exact {X : Type u} [Fintype X] [DecidableEq X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (D : FiniteSource X)
    (t : {x : X // T x}) (x : X) (W : UntargetedOutsideEndpoint T x → Bool) :
    PositiveAnswer D (indicatorAction T m t x W) ↔
      ¬ ActiveConnection (arrowGraph (augmentSource D.dag t.val).arrow)
        (SelectedCondition (InvarianceCondition (IndicatorCondition T (Mask m) x W)))
        (Observed none) (Observed (some x)) := by
  have legal := indicator_action_legal T m t x W
  change (if ¬ BoolCondition (indicatorBits T m x W) x then _ else False) ↔ _
  change ¬ BoolCondition (indicatorBits T m x W) x at legal
  rw [if_pos legal, indicatorBits_exact]

theorem zero_condition_is_selected {X S L : Type u} :
    (SelectedCondition (InvarianceCondition (BoolCondition (fun _ : X => false))) :
      SourceVertex (Option X) S L → Prop) = Selected := by
  funext z
  rcases z with (((_ | x) | s) | l) <;> exact propext (by simp [SelectedCondition,
    retainedCondition, SourceSelection.Condition, InvarianceCondition, BoolCondition, Selected])

theorem marginal_answer_exact {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) (t : {x : X // T x}) (x : X) (distinct : t.val ≠ x) :
    PositiveAnswer D (marginalAction t x) ↔ ¬ MarginalMask D.dag t.val x := by
  have legal := marginal_action_legal t x
  change (if ¬ BoolCondition (fun _ : X => false) x then _ else False) ↔ _
  change ¬ BoolCondition (fun _ : X => false) x at legal
  simp only [if_pos legal, zero_condition_is_selected]
  simp [MarginalMask, distinct]

end RestrictedCausal.PartialQueries
