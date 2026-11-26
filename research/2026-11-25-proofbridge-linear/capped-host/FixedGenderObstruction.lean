import FixedGender
import PaddingObstructionConsumer

namespace ResearchCommons.FixedGenderObstruction
open PopulationCounting CappedLabeledGrid CappedPaddingLanguage CappedConnectedBags
open FixedGender PaddingObstructionConsumer

/-- Equality of infinite-word languages and failure of a cell-injective
edge-preserving map now hold for the same fixed-gender padding. This claim
does not equip either source or target with actual dates. -/
theorem fixed_invisible_but_not_mappable {V : Type} {k side : Nat}
    (p : InfiniteLabeledPopulation k k) (large : k * fullRootCount p + 1 < side)
    (base : V → V → Option Nat) :
    (∀ w, Realizes (joined base (@fixedEdge side k)) w ↔ Realizes base w) ∧
      (∀ map : Sum V (Vertex side k) → Nat,
        (∀ a b : Cell side, map (.inr (.inr a)) = map (.inr (.inr b)) → a = b) →
        (∀ a b l, joined base (@fixedEdge side k) a b = some l →
          p.edge (map a) (map b) = some l) → False) := by
  constructor
  · intro w
    exact fixed_preserves_words base side k w
  · intro map inj keep
    let m : Cell side → Nat := fun a => map (.inr (.inr a))
    have hadj (a b : Cell side) (h : east a b ∨ north a b) : Adj p (m a) (m b) :=
      Or.inl (by
        change (p.edge (map (.inr (.inr a))) (map (.inr (.inr b)))).isSome = true
        rw [keep (.inr (.inr a)) (.inr (.inr b)) _ (grid_edge a b h)]
        rfl)
    exact no_cell_grid_map p large m inj
      (fun a b h => hadj a b (.inl h)) (fun a b h => hadj a b (.inr h))

#print axioms fixed_invisible_but_not_mappable
end ResearchCommons.FixedGenderObstruction
