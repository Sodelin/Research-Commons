import GraphReach
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem no_edge_return (G : EdgeGraph V E) (ha : G.Acyclic) (e : E) :
    ¬ G.DReach (G.target e) (G.source e) := by
  intro h
  exact ha _ (Relation.TransGen.head' ⟨e, rfl, rfl⟩ h)

/-- Sibling expansions cannot share any descendant in the actual unique-incoming
acyclic graph. Original edge IDs are not quotiented by endpoints. -/
theorem first_edge_unique (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (e f : E)
    (hs : G.source e = G.source f) {x : V}
    (he : G.DReach (G.target e) x) (hf : G.DReach (G.target f) x) : e = f := by
  induction he with
  | refl =>
    rcases hf.cases_tail with hx | ⟨y, hy, g, hgs, hgt⟩
    · exact hui hx
    · have hg : g = e := hui hgt
      subst g
      exact False.elim (no_edge_return G ha f (by simpa only [EdgeGraph.DReach, ← hgs, hs] using hy))
  | @tail y z hp hstep ih =>
    obtain ⟨g, hgs, hgt⟩ := hstep
    rcases hf.cases_tail with hz | ⟨w, hw, k, hks, hkt⟩
    · have hg : g = f := hui (hgt.trans hz)
      subst g
      exact False.elim (no_edge_return G ha e (by simpa only [EdgeGraph.DReach, ← hgs, ← hs] using hp))
    · have hgk : g = k := hui (hgt.trans hkt.symm)
      subst k
      have hyw : y = w := hgs.symm.trans hks
      exact ih (by simpa only [EdgeGraph.DReach, ← hyw] using hw)

#print axioms first_edge_unique
end Nanuq.GraphSyntax
