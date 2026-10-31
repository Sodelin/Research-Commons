import HardFamilyIndicatorSignature

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

Literal original-source and physical-source adapters for the hard family.
Both nuisance carriers are empty, not unknown variables dropped from the
target. The physical witness reuses the proposed common positive binary
faithfulness construction on ONE original source, not independent slice
distributions. Its entire transitive proof chain remains unelaborated.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation FiniteTargetImage GraphEquivalence
open ProbabilitySource PartialQueries TranscriptDecoder

universe v

abbrev EmptyVertex (X : Type v) := SourceVertex X (PEmpty : Type v) (PEmpty : Type v)

def eraseEmpty {X : Type v} : EmptyVertex X → X
  | .inl (.inl x) => x
  | .inl (.inr «impossible») => «impossible».elim
  | .inr «impossible» => «impossible».elim

def emptyVertexEquiv (X : Type v) : EmptyVertex X ≃ X where
  toFun := eraseEmpty
  invFun := Observed
  left_inv vertex := by
    rcases vertex with ((x | «impossible») | «impossible»)
    · rfl
    · exact «impossible».elim
    · exact «impossible».elim
  right_inv _ := rfl

def emptyNuisanceSource {X : Type v} (D : X → X → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) : FiniteSource X where
  selections := PEmpty
  latents := PEmpty
  selectionFintype := inferInstance
  latentFintype := inferInstance
  dag := {
    arrow := fun a b => D (eraseEmpty a) (eraseEmpty b)
    acyclic := by
      intro a xs route
      have mapped := route.map eraseEmpty (fun _ _ h => h)
      have empty := acyclic (eraseEmpty a) (xs.map eraseEmpty) mapped
      cases xs with
      | nil => rfl
      | cons «next» rest => cases empty
    selection_sink := by intro «impossible»; exact «impossible».elim }

def emptySourceEquiv {X : Type v} (D : X → X → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) :
    MarkedEquiv (arrowGraph (emptyNuisanceSource D acyclic).dag.arrow) (arrowGraph D) where
  toEquiv := emptyVertexEquiv X
  edge _ _ _ _ := Iff.rfl

theorem empty_selection_condition {X : Type v} (C : X → Prop) (vertex : EmptyVertex X) :
    SelectedCondition C vertex ↔ C (eraseEmpty vertex) := by
  rcases vertex with ((x | «impossible») | «impossible»)
  · exact Iff.rfl
  · exact «impossible».elim
  · exact «impossible».elim

theorem empty_source_connection {X : Type v} (D : X → X → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : X → Prop) (x y : X) :
    ActiveConnection (arrowGraph (emptyNuisanceSource D acyclic).dag.arrow)
      (SelectedCondition C) (Observed x) (Observed y) ↔ ActiveConnection (arrowGraph D) C x y :=
  (emptySourceEquiv D acyclic).active_iff (empty_selection_condition C) _ _

def emptyAugmentedSourceEquiv {X : Type v} (D : X → X → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (target : X) :
    MarkedEquiv (arrowGraph (augmentSource (emptyNuisanceSource D acyclic).dag target).arrow)
      (arrowGraph (AddIndicator D target)) where
  toEquiv := emptyVertexEquiv (Option X)
  edge a b ma mb := by
    rcases a with ((a | «impossible») | «impossible»)
    · rcases b with ((b | «impossible») | «impossible»)
      · cases a with
        | none =>
            cases b with
            | none => exact Iff.rfl
            | some value =>
                change (((Observed value : EmptyVertex X) = Observed target ∧ ma = .tail ∧ mb = .head) ∨
                  (False ∧ ma = .head ∧ mb = .tail)) ↔
                  ((value = target ∧ ma = .tail ∧ mb = .head) ∨ (False ∧ ma = .head ∧ mb = .tail))
                simp only [Observed, Sum.inl.injEq]
        | some value =>
            cases b with
            | none =>
                change ((False ∧ ma = .tail ∧ mb = .head) ∨
                  ((Observed value : EmptyVertex X) = Observed target ∧ ma = .head ∧ mb = .tail)) ↔
                  ((False ∧ ma = .tail ∧ mb = .head) ∨ (value = target ∧ ma = .head ∧ mb = .tail))
                simp only [Observed, Sum.inl.injEq]
            | some other => exact Iff.rfl
      · exact «impossible».elim
      · exact «impossible».elim
    · exact «impossible».elim
    · exact «impossible».elim

theorem empty_augmented_connection {X : Type v} (D : X → X → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (target : X) (C : X → Prop) (x : X) :
    ActiveConnection (arrowGraph (augmentSource (emptyNuisanceSource D acyclic).dag target).arrow)
      (SelectedCondition (InvarianceCondition C)) (Observed none) (Observed (some x)) ↔
      ActiveConnection (arrowGraph (AddIndicator D target)) (InvarianceCondition C) none (some x) :=
  (emptyAugmentedSourceEquiv D acyclic target).active_iff
    (empty_selection_condition (InvarianceCondition C)) _ _

def originalSource {k u : Nat} (source : Option (Index u)) : FiniteSource (Labels k u) :=
  emptyNuisanceSource (arrow source) (arrow_acyclic source)

instance availableDecision {k u : Nat} : DecidablePred (@Available k u) := by
  intro v
  cases v <;> unfold Available <;> infer_instance

def labelCode {k u : Nat} : Labels k u → Nat
  | .inl t => t.val
  | .inr x => k + x.val

theorem labelCode_injective {k u : Nat} : Function.Injective (@labelCode k u) := by
  intro a b same
  cases a with
  | inl t => cases b with
    | inl s => exact congrArg Sum.inl (Fin.ext same)
    | inr x => have «bound» := t.isLt; change t.val = k + x.val at same; omega
  | inr x => cases b with
    | inl t => have «bound» := t.isLt; change k + x.val = t.val at same; omega
    | inr y =>
        have value : x.val = y.val := by change k + x.val = k + y.val at same; omega
        exact congrArg Sum.inr (Fin.ext value)

def labelOrder (k u : Nat) : LinearOrder (Labels k u) :=
  LinearOrder.lift' labelCode labelCode_injective

noncomputable def physicalSource {k u : Nat} (source : Option (Index u)) :
    PhysicalSource.PhysicalSource (@Available k u) :=
  PhysicalSource.realize Available (originalSource source)

theorem physical_source_graph {k u : Nat} (source : Option (Index u)) :
    (physicalSource (k := k) source).graph = originalSource source := rfl

theorem original_baseline_connection {k u : Nat} (source : Option (Index u))
    (C : Labels k u → Prop) (x y : Labels k u) :
    ActiveConnection (arrowGraph (originalSource source).dag.arrow) (SelectedCondition C)
      (Observed x) (Observed y) ↔ ActiveConnection (arrowGraph (arrow source)) C x y :=
  empty_source_connection (arrow source) (arrow_acyclic source) C x y

theorem original_indicator_connection {k u : Nat} (source : Option (Index u)) (t : Fin k)
    (C : Labels k u → Prop) (x : Labels k u) :
    ActiveConnection (arrowGraph (augmentSource (originalSource source).dag (.inl t)).arrow)
      (SelectedCondition (InvarianceCondition C)) (Observed none) (Observed (some x)) ↔
      ActiveConnection (arrowGraph (augmented source t)) (augmentedCondition C) none (some x) :=
  by
    have hc : InvarianceCondition C = augmentedCondition C := by
      funext v
      cases v <;> rfl
    simpa only [originalSource, augmented, hc] using
      empty_augmented_connection (arrow source) (arrow_acyclic source) (.inl t) C x

end RestrictedCausal.HardFamily
