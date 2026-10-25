import FiniteGraphDecisions

/-!
Author: dot (OpenAI), 2026-10-22.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual finite-source selected connection, inducing-path, literal MAG and TCM
decision definitions. The input supplies finite enumerations and decidable DAG
arrows. No statistical samples, numerical faithfulness test or hard-intervention
semantics is substituted. Explicit profile-code decoding and the B-query policy
remain separate from these graph decisions.
-/

namespace RestrictedCausal.FiniteGraphDecision

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation HPLTarget

universe u v w

def arrowGraphDecision {V : Type u} (R : V → V → Prop) [DecidableRel R]
    (a b : V) (ma mb : Mark) : Decidable ((arrowGraph R).edge a b ma mb) := by
  unfold arrowGraph
  infer_instance

def selectedConditionDecision {X : Type u} {S : Type v} {L : Type w}
    (Z : X → Prop) [DecidablePred Z] (a : SourceVertex X S L) : Decidable (SelectedCondition Z a) := by
  rcases a with ((x | s) | l)
  · exact inferInstanceAs (Decidable (Z x))
  · exact isTrue trivial
  · exact isFalse id

def selectedConnectionDecision {X : Type u} {S : Type v} {L : Type w}
    [Fintype X] [Fintype S] [Fintype L] [DecidableEq X] [DecidableEq S] [DecidableEq L]
    (D : SourceDAG X S L) [DecidableRel D.arrow] (Z : X → Prop) [DecidablePred Z] (x y : X) :
    Decidable (ActiveConnection (arrowGraph D.arrow) (SelectedCondition Z) (Observed x) (Observed y)) :=
  activeDecision (arrowGraph D.arrow) (original_arrow_mixed_laws D) (arrowGraphDecision D.arrow)
    (SelectedCondition Z) (selectedConditionDecision Z) (Observed x) (Observed y)

def BoolCondition {X : Type u} (b : X → Bool) : X → Prop := fun x => b x = true

instance boolConditionDecision {X : Type u} (b : X → Bool) : DecidablePred (BoolCondition b) :=
  fun x => inferInstanceAs (Decidable (b x = true))

def FiniteInseparableTest {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : Prop :=
  x ≠ y ∧ ∀ b : X → Bool, ¬ BoolCondition b x → ¬ BoolCondition b y →
    ActiveConnection (arrowGraph D.arrow) (SelectedCondition (BoolCondition b)) (Observed x) (Observed y)

theorem finite_inseparable_iff {X : Type u} {S : Type v} {L : Type w}
    (D : SourceDAG X S L) (x y : X) : FiniteInseparableTest D x y ↔ Inseparable D x y := by
  classical
  constructor
  · rintro ⟨hne, hp⟩
    refine ⟨hne, ?_⟩
    intro Z hx hy
    let b : X → Bool := fun z => decide (Z z)
    have heq : BoolCondition b = Z := funext fun z => propext (by simp [BoolCondition, b])
    have hb := hp b (by simpa only [heq] using hx) (by simpa only [heq] using hy)
    simpa only [heq] using hb
  · rintro ⟨hne, hp⟩
    exact ⟨hne, fun b => hp (BoolCondition b)⟩

/-- A finite Boolean-conditioning search decides actual inducing paths by
the proved classical inducing/separator equivalence, not by assuming that
the inseparability graph is the requested target. -/
def inducingDecision {X : Type u} {S : Type v} {L : Type w}
    [Fintype X] [Fintype S] [Fintype L] [DecidableEq X] [DecidableEq S] [DecidableEq L]
    (D : SourceDAG X S L) [DecidableRel D.arrow] (x y : X) : Decidable (InducingPath D x y) := by
  letI : ∀ b : X → Bool, Decidable (ActiveConnection (arrowGraph D.arrow)
      (SelectedCondition (BoolCondition b)) (Observed x) (Observed y)) :=
    fun b => selectedConnectionDecision D (BoolCondition b) x y
  have test : Decidable (FiniteInseparableTest D x y) := by
    unfold FiniteInseparableTest
    infer_instance
  have correct : FiniteInseparableTest D x y ↔ InducingPath D x y :=
    (finite_inseparable_iff D x y).trans (inducing_iff_inseparable D x y).symm
  exact match test with
    | .isTrue h => .isTrue (correct.mp h)
    | .isFalse h => .isFalse (fun hp => h (correct.mpr hp))

def tailFlagDecision {X : Type u} {S : Type v} {L : Type w}
    [Fintype X] [Fintype S] [Fintype L] [DecidableEq X] [DecidableEq S] [DecidableEq L]
    (D : SourceDAG X S L) [DecidableRel D.arrow] (x y : X) : Decidable (TailFlag D x y) := by
  letI : DecidableRel (Reach (arrowGraph D.arrow)) :=
    reachDecision (arrowGraph D.arrow) (arrowGraphDecision D.arrow)
  unfold TailFlag SelectionAncestor
  infer_instance

def magEdgeDecision {X : Type u} {S : Type v} {L : Type w}
    [Fintype X] [Fintype S] [Fintype L] [DecidableEq X] [DecidableEq S] [DecidableEq L]
    (D : SourceDAG X S L) [DecidableRel D.arrow] (x y : X) (mx my : Mark) :
    Decidable ((mag D).edge x y mx my) := by
  letI : Decidable (InducingPath D x y) := inducingDecision D x y
  letI : Decidable (TailFlag D x y) := tailFlagDecision D x y
  letI : Decidable (TailFlag D y x) := tailFlagDecision D y x
  unfold mag EndpointMark
  infer_instance

def augmentedArrowDecision {X : Type u} {S : Type v} {L : Type w}
    [DecidableEq X] [DecidableEq S] [DecidableEq L]
    (D : SourceDAG X S L) [DecidableRel D.arrow] (target : X)
    (a b : SourceVertex (Option X) S L) : Decidable ((augmentSource D target).arrow a b) := by
  change Decidable (AddIndicator D.arrow (Observed target) (sourceIndicatorEquiv a) (sourceIndicatorEquiv b))
  cases sourceIndicatorEquiv a <;> cases sourceIndicatorEquiv b <;> unfold AddIndicator <;> infer_instance

/-- This computes only the precise graph target on a supplied finite DAG.
It does not enumerate arbitrary independently realizable augmented MAGs. -/
def tcmEdgeDecision {X : Type u} {S : Type v} {L : Type w}
    [Fintype X] [Fintype S] [Fintype L] [DecidableEq X] [DecidableEq S] [DecidableEq L]
    (D : SourceDAG X S L) [DecidableRel D.arrow] (T : X → Prop) [DecidablePred T]
    (a b : CombinedVertex X T) (ma mb : Mark) : Decidable ((tcm D T).edge a b ma mb) := by
  letI : ∀ (t : {x : X // T x}) (x y : Option X),
      Decidable ((mag (augmentSource D t.val)).edge x y ma mb) := by
    intro t x y
    letI : DecidableRel (augmentSource D t.val).arrow := augmentedArrowDecision D t.val
    exact magEdgeDecision (augmentSource D t.val) x y ma mb
  unfold tcm OwnTargetPair
  infer_instance

end RestrictedCausal.FiniteGraphDecision
