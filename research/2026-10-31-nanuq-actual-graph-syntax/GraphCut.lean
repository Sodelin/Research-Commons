import GraphNoDup
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem descendant_step_iff (G : EdgeGraph V E) (hui : Function.Injective G.target)
    (cut g : E) (hne : g ≠ cut) :
    G.DReach (G.target cut) (G.source g) ↔ G.DReach (G.target cut) (G.target g) := by
  constructor
  · intro h; exact h.tail ⟨g, rfl, rfl⟩
  · intro h
    rcases h.cases_tail with heq | ⟨v, hv, f, hfs, hft⟩
    · exact False.elim (hne (hui heq))
    · have hfg : f = g := hui hft
      subst f
      simpa only [EdgeGraph.DReach, ← hfs] using hv

theorem descendant_constant_without (G : EdgeGraph V E) (hui : Function.Injective G.target)
    (cut : E) {a b : V} (h : G.ReachWithout cut a b) :
    G.DReach (G.target cut) a ↔ G.DReach (G.target cut) b := by
  induction h with
  | refl => rfl
  | @tail v w hp hs ih =>
    obtain ⟨g, hg, hinc⟩ := hs
    have he := descendant_step_iff G hui cut g hg
    rcases hinc with ⟨hgs, hgt⟩ | ⟨hgs, hgt⟩
    · exact ih.trans (by simpa only [hgs, hgt] using he)
    · exact ih.trans (by simpa only [hgs, hgt] using he.symm)

theorem descendant_path_without (G : EdgeGraph V E) (ha : G.Acyclic)
    (cut : E) {x : V} (h : G.DReach (G.target cut) x) :
    G.ReachWithout cut (G.target cut) x := by
  induction h with
  | refl => exact .refl
  | @tail v w hp hs ih =>
    obtain ⟨g, hgs, hgt⟩ := hs
    have hne : g ≠ cut := by
      intro heq; subst g
      exact no_edge_return G ha cut (by simpa only [EdgeGraph.DReach, hgs] using hp)
    exact ih.tail ⟨g, hne, Or.inl ⟨hgs,hgt⟩⟩

/-- Exact original edge-deletion target component, not merely path support. -/
theorem target_cut_iff (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (cut : E) (x : V) :
    G.ReachWithout cut (G.target cut) x ↔ G.DReach (G.target cut) x := by
  constructor
  · intro h
    exact (descendant_constant_without G hui cut h).mp .refl
  · exact descendant_path_without G ha cut

#print axioms target_cut_iff
end Nanuq.GraphSyntax
