import CappedLabeledGrid
import CappedGridObstruction

namespace ResearchCommons.PaddingObstructionConsumer
open PopulationCounting CappedLabeledGrid CappedPaddingLanguage
open CappedConnectedBags CappedGridObstruction

/-- The obstruction needs only images of cells and preservation of the two
adjacencies, independent of how gender or private parents are represented. -/
theorem no_cell_grid_map {k side : Nat}
    (p : InfiniteLabeledPopulation k k)
    (large : k * fullRootCount p + 1 < side)
    (map : Cell side → Nat)
    (inj : ∀ a b, map a = map b → a = b)
    (hEast : ∀ a b, east a b → Adj p (map a) (map b))
    (hNorth : ∀ a b, north a b → Adj p (map a) (map b)) :
    False := by
  let f : Nat → Nat → Nat := fun r c =>
    if hr : r < side then
      if hc : c < side then map (⟨r,hr⟩,⟨c,hc⟩) else 0
    else 0
  apply no_large_grid p side large f
  · intro r c hr hc
    have hc' : c < side := by omega
    simpa only [f, dif_pos hr, dif_pos hc, dif_pos hc'] using
      hEast (⟨r,hr⟩,⟨c,hc'⟩) (⟨r,hr⟩,⟨c+1,hc⟩) ⟨rfl,rfl⟩
  · intro r c hr hc
    have hr' : r < side := by omega
    simpa only [f, dif_pos hr, dif_pos hr', dif_pos hc] using
      hNorth (⟨r,hr'⟩,⟨c,hc⟩) (⟨r+1,hr⟩,⟨c,hc⟩) ⟨rfl,rfl⟩
  · intro ⟨r,c⟩ ⟨r',c'⟩ ⟨hr,hc⟩ ⟨hr',hc'⟩ h
    simp only [f, dif_pos hr, dif_pos hc, dif_pos hr', dif_pos hc'] at h
    exact congrArg (fun q : Cell side => (q.1.val,q.2.val)) (inj _ _ h)

/-- Even a non-induced map of the padded graph preserving its labelled edges
cannot land in the chronological host. It suffices for the cell images to
be injective; neither private-root injectivity nor label reflection is used. -/
theorem no_label_preserving_padding_map {k side : Nat}
    (p : InfiniteLabeledPopulation k k)
    (large : k * fullRootCount p + 1 < side)
    (map : Vertex side k → Nat)
    (inj : ∀ a b : Cell side, map (.inr a) = map (.inr b) → a = b)
    (preserves : ∀ a b l, edge a b = some l → p.edge (map a) (map b) = some l) :
    False := by
  apply no_cell_grid_map p large (fun a => map (.inr a)) inj
  · intro a b h
    exact Or.inl (by rw [preserves _ _ _ (grid_east_edge a b h)]; rfl)
  · intro a b h
    exact Or.inl (by rw [preserves _ _ _ (grid_north_edge a b h)]; rfl)

/-- The same concrete extension that preserves the base's realized words
cannot be mapped into this finite-root capped chronological host. -/
theorem invisible_but_not_mappable {V : Type} {side k : Nat}
    (p : InfiniteLabeledPopulation k k) (large : k * fullRootCount p + 1 < side)
    (base : V → V → Option Nat) :
    (∀ word, Realizes (joined base (@edge side k)) word ↔ Realizes base word) ∧
      (∀ map : Sum V (Vertex side k) → Nat,
        (∀ a b : Cell side, map (.inr (.inr a)) = map (.inr (.inr b)) → a = b) →
        (∀ a b l, joined base (@edge side k) a b = some l →
          p.edge (map a) (map b) = some l) → False) := by
  constructor
  · intro word
    exact preserves_words base side k word
  · intro map inj preserves
    exact no_label_preserving_padding_map p large (fun a => map (.inr a))
      inj (fun a b l h => preserves (.inr a) (.inr b) l h)

#print axioms invisible_but_not_mappable
end ResearchCommons.PaddingObstructionConsumer
