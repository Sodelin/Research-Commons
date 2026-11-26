import CappedGridGlue

open PopulationCounting
open ResearchCommons.CappedLabeledGrid ResearchCommons.CappedPaddingLanguage
open ResearchCommons.CappedGridGlue

-- Integration consumer: literal directed label preservation implies the
-- deliberately weaker adjacency preservation excluded by the provider.
example {V : Type} {k : Nat} (p : InfiniteLabeledPopulation k k)
    (base : V → V → Option Nat) :
    ∃ n, (∀ w, Realizes (joined base (@edge n 2)) w ↔ Realizes base w) ∧
      ¬ ∃ f : Sum V (Vertex n 2) → Nat, Function.Injective f ∧
        (∀ a b : Sum V (Vertex n 2), ∀ l,
          joined base (@edge n 2) a b = some l → p.edge (f a) (f b) = some l) := by
  obtain ⟨n, lang, noMap⟩ := exists_word_preserving_nonembed p base 2
  refine ⟨n, lang, ?_⟩
  rintro ⟨f, inj, maps⟩
  apply noMap
  refine ⟨f,inj,?_⟩
  intro a b l h
  exact Or.inl (by rw [maps a b l h]; rfl)
