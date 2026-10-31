import GraphCut
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem path_without_of_not_descendant (G : EdgeGraph V E) (cut : E)
    {a x : V} (h : G.DReach a x) (hx : ¬ G.DReach (G.target cut) x) :
    G.ReachWithout cut a x := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨g, hgs, hgt⟩ := hs
    have hv : ¬ G.DReach (G.target cut) v := by
      intro hd; exact hx (hd.tail ⟨g,hgs,hgt⟩)
    have hg : g ≠ cut := by
      intro heq; subst g
      apply hx
      rw [← hgt]
      exact .refl
    exact (ih hv).tail ⟨g,hg,Or.inl ⟨hgs,hgt⟩⟩

/-- Exact complementary component for the original edge ID. -/
theorem source_cut_iff (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    (cut : E) (x : V) :
    G.ReachWithout cut (G.source cut) x ↔ ¬ G.DReach (G.target cut) x := by
  constructor
  · intro h hx
    exact no_edge_return G ha cut ((descendant_constant_without G hui cut h).mpr hx)
  · intro hx
    have hs := path_without_of_not_descendant G cut (hr (G.source cut))
      (no_edge_return G ha cut)
    have ht := path_without_of_not_descendant G cut (hr x) hx
    exact (G.ureach_symm hs).trans ht

/-- Both sides are exact actual source ReachWithout predicates. -/
theorem actual_edge_partition (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    (cut : E) (x : V) :
    (G.ReachWithout cut (G.source cut) x ↔ ¬ G.DReach (G.target cut) x) ∧
    (G.ReachWithout cut (G.target cut) x ↔ G.DReach (G.target cut) x) :=
  ⟨source_cut_iff G ha hui root hr cut x, target_cut_iff G ha hui cut x⟩

#print axioms actual_edge_partition
end Nanuq.GraphSyntax
