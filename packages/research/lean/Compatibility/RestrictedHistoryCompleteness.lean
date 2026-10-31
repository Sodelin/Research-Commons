import OrderedFamilyAgreement

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Derive the graph-family premises from actual WHOLE-HISTORY consistency and
explicit query coverage. Marginal bits are recorded response complements,
not an assumed ancestry oracle. One orientation per observed pair and only
available distinct-target indicator pairs are required. Extra history rows
are retained and must also fit the same original rival source.
-/

namespace RestrictedCausal.PartialQueries

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open HPLTarget FiniteTargetImage FiniteGraphDecision TranscriptDecoder IndicatorAncestry

universe u

def CoversAction {X : Type u} {T : X → Prop} (h : History X T) (a : ElementaryAction X T) : Prop :=
  ∃ response : Bool, (a, response) ∈ h

def MarginalsRecorded {X : Type u} {T : X → Prop}
    (m : X → X → Bool) (h : History X T) : Prop :=
  ∀ (t : {x : X // T x}) (x : X), t.val ≠ x →
    (marginalAction t x, !(m t.val x)) ∈ h

structure RestrictedCoverage {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool) (h : History X T) : Prop where
  observed : ∀ x y, x < y → ∀ W : UntargetedOutsidePair T x y → Bool,
    CoversAction h (pairAction T m x y W)
  indicator : ∀ (t : {x : X // T x}) (x : X), t.val ≠ x →
    ∀ W : UntargetedOutsideEndpoint T x → Bool, CoversAction h (indicatorAction T m t x W)

theorem consistent_answers_agree {X : Type u} [DecidableEq X] {T : X → Prop}
    (D E : FiniteSource X) (h : History X T)
    (honestD : SourceConsistent D h) (honestE : SourceConsistent E h)
    (a : ElementaryAction X T) (covered : CoversAction h a) :
    PositiveAnswer D a ↔ PositiveAnswer E a := by
  obtain ⟨response, member⟩ := covered
  exact (honestD (a, response) member).trans (honestE (a, response) member).symm

theorem recorded_mask_exact {X : Type u} [DecidableEq X] {T : X → Prop}
    (D : FiniteSource X) (m : X → X → Bool) (h : History X T)
    (recorded : MarginalsRecorded m h) (honest : SourceConsistent D h) :
    AvailableMaskExact D.dag T (Mask m) := by
  classical
  intro t x available distinct
  let target : {x : X // T x} := ⟨t, available⟩
  have row := honest (marginalAction target x, !(m t x)) (recorded target x distinct)
  have step := (not_congr row).symm.trans
    (not_congr (marginal_answer_exact D target x distinct))
  have doubleNegated : Mask m t x ↔ ¬ ¬ MarginalMask D.dag t x := by
    simpa [Mask] using step
  constructor
  · intro present
    by_contra absent
    exact (doubleNegated.mp present) absent
  · intro present
    exact doubleNegated.mpr (fun absent => absent present)

theorem connection_agreement_of_separation {P Q : Prop} (separations : (¬ P) ↔ ¬ Q) : P ↔ Q := by
  classical
  constructor
  · intro connected
    by_contra separated
    exact (separations.mpr separated) connected
  · intro connected
    by_contra separated
    exact (separations.mp separated) connected

theorem covered_observed_agreement {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool)
    (D E : FiniteSource X) (h : History X T)
    (honestD : SourceConsistent D h) (honestE : SourceConsistent E h)
    (covered : RestrictedCoverage T m h) : ObservedFamilyAgreement D.dag E.dag T (Mask m) := by
  apply ordered_observed_agreement D.dag E.dag T (Mask m)
  intro x y ordered W
  have distinct := ne_of_lt ordered
  have answers := consistent_answers_agree D E h honestD honestE
    (pairAction T m x y W) (covered.observed x y ordered W)
  exact connection_agreement_of_separation
    ((pair_answer_exact T m D x y distinct W).symm.trans
      (answers.trans (pair_answer_exact T m E x y distinct W)))

theorem covered_indicator_agreement {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (m : X → X → Bool)
    (D E : FiniteSource X) (h : History X T)
    (honestD : SourceConsistent D h) (honestE : SourceConsistent E h)
    (covered : RestrictedCoverage T m h) : IndicatorFamilyAgreement D.dag E.dag T (Mask m) := by
  intro t available x distinct W
  let target : {x : X // T x} := ⟨t, available⟩
  have answers := consistent_answers_agree D E h honestD honestE
    (indicatorAction T m target x W) (covered.indicator target x distinct W)
  exact connection_agreement_of_separation
    ((indicator_answer_exact T m D target x W).symm.trans
      (answers.trans (indicator_answer_exact T m E target x W)))

/-- This discharges the previously outstanding `CompleteHistory` predicate
from explicit finite-coordinate coverage and an honest source transcript.
The original structural rival is quantified before any target is considered. -/
theorem restricted_history_complete {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X)
    (m : X → X → Bool) (h : History X T)
    (recorded : MarginalsRecorded m h) (covered : RestrictedCoverage T m h)
    (honest : SourceConsistent D h) : CompleteHistory D h := by
  intro E
  constructor
  · intro consistent
    exact (restricted_families_complete D E T (Mask m)
      (recorded_mask_exact D m h recorded honest)
      (recorded_mask_exact E m h recorded consistent)
      (covered_observed_agreement T m D E h honest consistent covered)
      (covered_indicator_agreement T m D E h honest consistent covered)).setwise
  · intro equivalent
    exact (consistent_preserved equivalent.elementary h).mp honest

/-- The unchanged exact marked-TCM CLASS, not one graph and not a product
of separate indicator equivalence classes. The canonical registry's common
source and target-preservation proofs enter through decode_complete_history. -/
theorem restricted_history_target_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T] (D : FiniteSource X)
    (m : X → X → Bool) (h : History X T)
    (recorded : MarginalsRecorded m h) (covered : RestrictedCoverage T m h)
    (honest : SourceConsistent D h) (G : MarkedGraph (CombinedVertex X T)) :
    (∃ b ∈ decodeHistory T h, decodeTarget b = G) ↔
      ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G :=
  decode_complete_history T D h (restricted_history_complete T D m h recorded covered honest) G

end RestrictedCausal.PartialQueries
