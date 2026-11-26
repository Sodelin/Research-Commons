import CappedLabeledGrid
import CappedGridObstruction

namespace ResearchCommons.CappedGridGlue

open PopulationCounting InfiniteConservation
open ResearchCommons.CappedLabeledGrid ResearchCommons.CappedConnectedBags
open ResearchCommons.CappedGridObstruction ResearchCommons.CappedPaddingLanguage

/-- The actual finite labelled pad already defeats every sufficiently narrow natural
host, even if an embedding can discard labels, directions, and the private roots. -/
theorem no_large_pad_map {k d n : Nat} (p : InfiniteLabeledPopulation k k)
    (large : k * fullRootCount p + 1 < n)
    (f : Vertex n d → Nat)
    (cellInj : Function.Injective (fun a : Cell n => f (.inr a)))
    (mapAdj : ∀ a b : Cell n, ∀ l,
      @edge n d (.inr a) (.inr b) = some l → Adj p (f (.inr a)) (f (.inr b))) : False := by
  let atNat (r c : Nat) : Nat :=
    if h : r < n ∧ c < n then f (.inr (⟨r,h.1⟩,⟨c,h.2⟩)) else 0
  apply no_large_grid p n large atNat
  · intro r c hr hc
    have hc0 : c < n := by omega
    simpa only [atNat, dif_pos (And.intro hr hc0), dif_pos (And.intro hr hc)] using
      mapAdj (⟨r,hr⟩,⟨c,hc0⟩) (⟨r,hr⟩,⟨c+1,hc⟩) 0 (grid_east_edge _ _ ⟨rfl,rfl⟩)
  · intro r c hr hc
    have hr0 : r < n := by omega
    simpa only [atNat, dif_pos (And.intro hr0 hc), dif_pos (And.intro hr hc)] using
      mapAdj (⟨r,hr0⟩,⟨c,hc⟩) (⟨r+1,hr⟩,⟨c,hc⟩) 1 (grid_north_edge _ _ ⟨rfl,rfl⟩)
  · rintro ⟨r,c⟩ ⟨s,t⟩ hx hy h
    simp only [atNat, dif_pos hx, dif_pos hy] at h
    have he := cellInj h
    exact Prod.ext (congrArg (fun a : Cell n => a.1.val) he)
      (congrArg (fun a : Cell n => a.2.val) he)

/-- Choosing a pad side from the host's root bound leaves no numeric premise for
a consumer. The source label count is intentionally independent of the host. -/
theorem exists_pad_rejecting_host {k : Nat} (p : InfiniteLabeledPopulation k k) (d : Nat) :
    ∃ n, ¬ ∃ f : Vertex n d → Nat, Function.Injective f ∧
      (∀ a b : Vertex n d, ∀ l, edge a b = some l → Adj p (f a) (f b)) := by
  refine ⟨k * fullRootCount p + 2, ?_⟩
  rintro ⟨f,inj,mapAdj⟩
  apply no_large_pad_map p (by omega) f
  · intro a b h
    exact Sum.inr.inj (inj h)
  · intro a b l h
    exact mapAdj _ _ l h

/-- A single witness defeats the host and preserves every infinite word of an
arbitrary base edge system. This is a graph join, not a real-date population
construction: the latter must still discharge its own eligibility hypotheses. -/
theorem exists_word_preserving_nonembed {V : Type} {k : Nat}
    (p : InfiniteLabeledPopulation k k) (base : V → V → Option Nat) (d : Nat) :
    ∃ n,
      (∀ word, Realizes (joined base (@edge n d)) word ↔ Realizes base word) ∧
      ¬ ∃ f : Sum V (Vertex n d) → Nat, Function.Injective f ∧
        (∀ a b : Sum V (Vertex n d), ∀ l,
          joined base (@edge n d) a b = some l → Adj p (f a) (f b)) := by
  obtain ⟨n, rejects⟩ := exists_pad_rejecting_host p d
  refine ⟨n, preserves_words base n d, ?_⟩
  rintro ⟨f, inj, mapAdj⟩
  apply rejects
  refine ⟨fun a => f (.inr a), ?_, ?_⟩
  · intro a b h
    exact Sum.inr.inj (inj h)
  · intro a b l h
    exact mapAdj (.inr a) (.inr b) l h

#print axioms no_large_pad_map
#print axioms exists_pad_rejecting_host
#print axioms exists_word_preserving_nonembed
end ResearchCommons.CappedGridGlue
