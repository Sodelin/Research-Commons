import GraphSourceCut
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

inductive Below : BinarySyntax V → BinarySyntax V → Prop where
  | left (v) (l r) : Below (.fork v l r) l
  | right (v) (l r) : Below (.fork v l r) r
  | inLeft (v) (l r u) : Below l u → Below (.fork v l r) u
  | inRight (v) (l r u) : Below r u → Below (.fork v l r) u

theorem edge_has_subtree {G : EdgeGraph V E} {t : BinarySyntax V} {v : V}
    (h : Represents G t v) (e : E) (he : G.source e ∈ t.nodes) :
    ∃ u, Below t u ∧ Represents G u (G.target e) := by
  induction h with
  | tip v hv =>
    have hes : G.source e = v := by simpa [BinarySyntax.nodes] using he
    have hz : Finset.univ.filter (fun e => G.source e = v) = ∅ := Finset.card_eq_zero.mp hv
    have hm : e ∈ Finset.univ.filter (fun e => G.source e = v) := by simp [hes]
    rw [hz] at hm
    exact False.elim (Finset.notMem_empty e hm)
  | @fork v f g hne hf hg hall l r hl hr il ir =>
    simp only [BinarySyntax.nodes,List.mem_cons,List.mem_append] at he
    rcases he with hes | hes | hes
    · rcases hall e hes with heq | heq
      · subst e; exact ⟨l,.left v l r,hl⟩
      · subst e; exact ⟨r,.right v l r,hr⟩
    · obtain ⟨u,hu,hrep⟩ := il hes
      exact ⟨u,.inLeft v l r u hu,hrep⟩
    · obtain ⟨u,hu,hrep⟩ := ir hes
      exact ⟨u,.inRight v l r u hu,hrep⟩

theorem subtree_has_edge {G : EdgeGraph V E} {t : BinarySyntax V} {v : V}
    (h : Represents G t v) {u : BinarySyntax V} (hu : Below t u) :
    ∃ e, Represents G u (G.target e) := by
  induction h generalizing u with
  | tip v hv => cases hu
  | @fork v e f hne he hf hall l r hl hr il ir =>
    cases hu with
    | left => exact ⟨e,hl⟩
    | right => exact ⟨f,hr⟩
    | inLeft _ _ _ _ hsub => exact il hsub
    | inRight _ _ _ _ hsub => exact ir hsub

/-- Exact graph-edge to syntax-subtree partition, simultaneously for all vertices. -/
theorem edge_syntax_partition {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t : BinarySyntax V} (ht : Represents G t root) (e : E) :
    ∃ u, Below t u ∧ ∀ x,
      (G.ReachWithout e (G.target e) x ↔ x ∈ u.nodes) ∧
      (G.ReachWithout e (G.source e) x ↔ x ∉ u.nodes) := by
  obtain ⟨u,hu,hrep⟩ := edge_has_subtree ht e ((ht.mem_nodes_iff _).mpr (hr _))
  refine ⟨u,hu,fun x => ⟨?_,?_⟩⟩
  · exact (target_cut_iff G ha hui e x).trans (hrep.mem_nodes_iff x).symm
  · exact (source_cut_iff G ha hui root hr e x).trans (not_congr (hrep.mem_nodes_iff x).symm)

/-- Conversely no syntax-subtree cut is spurious. -/
theorem syntax_edge_partition {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t u : BinarySyntax V} (ht : Represents G t root) (hu : Below t u) :
    ∃ e, ∀ x,
      (G.ReachWithout e (G.target e) x ↔ x ∈ u.nodes) ∧
      (G.ReachWithout e (G.source e) x ↔ x ∉ u.nodes) := by
  obtain ⟨e,hrep⟩ := subtree_has_edge ht hu
  refine ⟨e,fun x => ⟨?_,?_⟩⟩
  · exact (target_cut_iff G ha hui e x).trans (hrep.mem_nodes_iff x).symm
  · exact (source_cut_iff G ha hui root hr e x).trans (not_congr (hrep.mem_nodes_iff x).symm)

#print axioms edge_syntax_partition
#print axioms syntax_edge_partition
end Nanuq.GraphSyntax
