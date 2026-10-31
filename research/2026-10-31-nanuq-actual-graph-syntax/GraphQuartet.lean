import GraphSubtree
import SourceQuartetRelation
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

theorem all_edges_bridge (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (e : E) : G.IsBridge e := by
  intro h
  exact no_edge_return G ha e ((descendant_constant_without G hui e h).mpr .refl)

def SyntaxQuartet (t : BinarySyntax V) (a b c d : V) : Prop :=
  ∃ u, Below t u ∧
    ((a ∉ u.nodes ∧ b ∉ u.nodes ∧ c ∈ u.nodes ∧ d ∈ u.nodes) ∨
     (c ∉ u.nodes ∧ d ∉ u.nodes ∧ a ∈ u.nodes ∧ b ∈ u.nodes))

/-- The actual original HasQuartet predicate, including bridge guard, exactly
matches subtree cuts on the constructed syntax. No assumed witness equivalence. -/
theorem actual_quartet_iff {G : EdgeGraph V E} (ha : G.Acyclic)
    (hui : Function.Injective G.target) (root : V) (hr : ∀ x, G.DReach root x)
    {t : BinarySyntax V} (ht : Represents G t root) (a b c d : V) :
    G.HasQuartet a b c d ↔ SyntaxQuartet t a b c d := by
  constructor
  · rintro ⟨e, _, he⟩
    obtain ⟨u,hu,hp⟩ := edge_syntax_partition ha hui root hr ht e
    refine ⟨u,hu,?_⟩
    rcases he with h | h
    · exact Or.inl ⟨(hp a).2.mp h.1,(hp b).2.mp h.2.1,
        (hp c).1.mp h.2.2.1,(hp d).1.mp h.2.2.2⟩
    · exact Or.inr ⟨(hp c).2.mp h.1,(hp d).2.mp h.2.1,
        (hp a).1.mp h.2.2.1,(hp b).1.mp h.2.2.2⟩
  · rintro ⟨u,hu,h⟩
    obtain ⟨e,hp⟩ := syntax_edge_partition ha hui root hr ht hu
    refine ⟨e,all_edges_bridge G ha hui e,?_⟩
    rcases h with h | h
    · exact Or.inl ⟨(hp a).2.mpr h.1,(hp b).2.mpr h.2.1,
        (hp c).1.mpr h.2.2.1,(hp d).1.mpr h.2.2.2⟩
    · exact Or.inr ⟨(hp c).2.mpr h.1,(hp d).2.mpr h.2.1,
        (hp a).1.mpr h.2.2.1,(hp b).1.mpr h.2.2.2⟩

/-- One syntax works for every quartet simultaneously. -/
theorem actual_graph_syntax_provider (G : EdgeGraph V E) (ha : G.Acyclic)
    (hui : Function.Injective G.target) (hb : ∀ v, G.outDegree v = 0 ∨ G.outDegree v = 2)
    (root : V) (hr : ∀ x, G.DReach root x) :
    ∃ t, Represents G t root ∧ t.nodes.Nodup ∧ (∀ x, x ∈ t.nodes) ∧
      ∀ a b c d, G.HasQuartet a b c d ↔ SyntaxQuartet t a b c d := by
  obtain ⟨t,ht,hn,hall⟩ := rooted_exact_enumeration G ha hui hb root hr
  exact ⟨t,ht,hn,hall,actual_quartet_iff ha hui root hr ht⟩

#print axioms actual_graph_syntax_provider
end Nanuq.GraphSyntax
