import SourceLabelledForest
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
Selected-label visible-pair bijection for the actual labelled source state.

Current ancestors need not be selected original representatives. They are kept
exactly when their genealogy contains a selected original label. The validity
theorem makes their nonempty selected blocks injective, so pair rates transfer
without multiplicities. Ordered pairs receive rate 1/2, hence each unordered
visible pair receives rate 1.

This is the actual-state combinatorial generator ingredient. It does not yet
prove matrix-exponential kernel intertwining, holding-time projectivity,
four-taxon pruning, or the all-copy G4 normal form.
-/

namespace GProgram.SourceForestKingmanProjection

open GProgram.SourceForest

section FinitePairBijection

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def pairMap (f : α → β) (p : α × α) : β × β := (f p.1, f p.2)

theorem image_offDiag_eq (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) :
    s.offDiag.image (pairMap f) = (s.image f).offDiag := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨⟨a, b⟩, hab, heq⟩
    rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, hne⟩
    have hx : f a = x := congrArg Prod.fst heq
    have hy : f b = y := congrArg Prod.snd heq
    refine Finset.mem_offDiag.mpr ⟨Finset.mem_image.mpr ⟨a, ha, hx⟩,
      Finset.mem_image.mpr ⟨b, hb, hy⟩, ?_⟩
    intro hxy
    exact hne (hf a ha b hb (hx.trans (hxy.trans hy.symm)))
  · intro h
    rcases Finset.mem_offDiag.mp h with ⟨hx, hy, hne⟩
    rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, hby⟩
    refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, ?_⟩, ?_⟩
    · intro hab
      exact hne (hax.symm.trans ((congrArg f hab).trans hby))
    · apply Prod.ext
      · exact hax
      · exact hby

theorem pairMap_injective_on_offDiag (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    {p q : α × α} (hp : p ∈ s.offDiag) (hq : q ∈ s.offDiag)
    (heq : pairMap f p = pairMap f q) : p = q := by
  rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
  rcases Finset.mem_offDiag.mp hq with ⟨hq1, hq2, _⟩
  apply Prod.ext
  · exact hf p.1 hp1 q.1 hq1 (congrArg Prod.fst heq)
  · exact hf p.2 hp2 q.2 hq2 (congrArg Prod.snd heq)

theorem each_projected_pair_has_unique_original (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    (p : β × β) (hp : p ∈ (s.image f).offDiag) :
    ∃! q : α × α, q ∈ s.offDiag ∧ pairMap f q = p := by
  have hmem : p ∈ s.offDiag.image (pairMap f) := by
    rw [image_offDiag_eq s f hf]
    exact hp
  rcases Finset.mem_image.mp hmem with ⟨q, hq, heq⟩
  refine ⟨q, ⟨hq, heq⟩, ?_⟩
  intro r hr
  exact pairMap_injective_on_offDiag s f hf hr.1 hq (hr.2.trans heq.symm)

theorem projected_pair_sum (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    (w : β × β → ℝ) :
    (∑ p ∈ s.offDiag, w (pairMap f p)) =
      ∑ q ∈ (s.image f).offDiag, w q := by
  rw [← image_offDiag_eq s f hf]
  rw [Finset.sum_image]
  exact fun p hp q hq h => pairMap_injective_on_offDiag s f hf hp hq h

end FinitePairBijection

section ActualSource

variable {V E Copy : Type*} [DecidableEq V] [DecidableEq E]
  [Fintype V] [Fintype E] [DecidableEq Copy] [Fintype Copy]

def visibleActiveRoots (s : State V E Copy) (keep active : Finset Copy) : Finset Copy :=
  active.filter (fun a => (selectedBlock s keep a).Nonempty)

def selectedActiveBlocks (s : State V E Copy) (keep active : Finset Copy) : Finset (Finset Copy) :=
  (visibleActiveRoots s keep active).image (selectedBlock s keep)

theorem selectedBlock_injective_on_visibleActive
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) :
    ∀ a ∈ visibleActiveRoots s keep active,
      ∀ b ∈ visibleActiveRoots s keep active,
        selectedBlock s keep a = selectedBlock s keep b → a = b := by
  intro a ha b hb heq
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hav : a ∈ visibleAncestors s keep := by
    rw [mem_visibleAncestors]
    exact ⟨hactive ha'.1, ha'.2⟩
  have hbv : b ∈ visibleAncestors s keep := by
    rw [mem_visibleAncestors]
    exact ⟨hactive hb'.1, hb'.2⟩
  exact selectedBlock_injective_on_visible s hs keep hav hbv heq

theorem source_visible_pair_image
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) :
    (visibleActiveRoots s keep active).offDiag.image (pairMap (selectedBlock s keep)) =
      (selectedActiveBlocks s keep active).offDiag := by
  exact image_offDiag_eq (visibleActiveRoots s keep active) (selectedBlock s keep)
    (selectedBlock_injective_on_visibleActive s hs keep active hactive)

theorem source_visible_pair_unique_preimage
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep active).offDiag) :
    ∃! q : Copy × Copy, q ∈ (visibleActiveRoots s keep active).offDiag ∧
      pairMap (selectedBlock s keep) q = p := by
  exact each_projected_pair_has_unique_original (visibleActiveRoots s keep active)
    (selectedBlock s keep)
    (selectedBlock_injective_on_visibleActive s hs keep active hactive) p hp

noncomputable def visiblePairGenerator
    (s : State V E Copy) (keep active : Finset Copy)
    (increment : Finset Copy × Finset Copy → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ (visibleActiveRoots s keep active).offDiag,
    increment (pairMap (selectedBlock s keep) p)

noncomputable def projectedPairGenerator
    (s : State V E Copy) (keep active : Finset Copy)
    (increment : Finset Copy × Finset Copy → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ (selectedActiveBlocks s keep active).offDiag, increment p

theorem actual_source_visible_generator_identity
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) (increment : Finset Copy × Finset Copy → ℝ) :
    visiblePairGenerator s keep active increment =
      projectedPairGenerator s keep active increment := by
  unfold visiblePairGenerator projectedPairGenerator selectedActiveBlocks
  rw [projected_pair_sum (visibleActiveRoots s keep active) (selectedBlock s keep)
    (selectedBlock_injective_on_visibleActive s hs keep active hactive) increment]

end ActualSource

end GProgram.SourceForestKingmanProjection

#print axioms GProgram.SourceForestKingmanProjection.source_visible_pair_unique_preimage
#print axioms GProgram.SourceForestKingmanProjection.actual_source_visible_generator_identity
