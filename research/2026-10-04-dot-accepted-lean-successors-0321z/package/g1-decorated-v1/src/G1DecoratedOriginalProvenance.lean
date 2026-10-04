import G1OriginalDecoratedSpan

/-! Physical original-source provenance for decorated core edges.
Contributor: dot, 2026-10-03. Labels contain original words, never fitted rates
or assumed output laws. Nonbridge populations retain actual original IDs. -/
namespace G1DecoratedOriginalProvenance
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1CutChildPorts
open G1ActualTwoPortBlob G1NonrootBigonKernel
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

inductive Recipe (O : Source.{u,v,w} X)
  | raw (edge : O.Edge)
  | span (a b : O.Vertex) (word : OriginalSpan O.network a b)

def Recipe.input {O : Source X} : Recipe O → O.Vertex
  | .raw e => O.network.graph.target e
  | .span a _ _ => a

def Recipe.output {O : Source X} : Recipe O → O.Vertex
  | .raw e => O.network.graph.source e
  | .span _ b _ => b

/-- Provenance is physical graph/program data only. No desired kernel/law
identity or free macro kernel is admitted in this structure. -/
structure Decoration (O S : Source.{u,v,w} X) where
  vertex : S.Vertex ↪ O.Vertex
  root : vertex S.network.root = O.network.root
  taxa : ∀ x, vertex (S.network.leaf x) = O.network.leaf x
  calendar : ∀ x, S.calendar.age x = O.calendar.age (vertex x)
  indegree : ∀ x, S.network.graph.inDegree x = O.network.graph.inDegree (vertex x)
  outdegree : ∀ x, S.network.graph.outDegree x = O.network.graph.outDegree (vertex x)
  sameBlob : ∀ x y, S.network.graph.SameBlob x y ↔ O.network.graph.SameBlob (vertex x) (vertex y)
  rootBlob_surjective : ∀ v, O.network.graph.SameBlob O.network.root v →
    ∃ x, S.network.graph.SameBlob S.network.root x ∧ vertex x = v
  recipe : S.Edge → Recipe O
  endpoints : ∀ e, (recipe e).input = vertex (S.network.graph.target e) ∧
    (recipe e).output = vertex (S.network.graph.source e)
  raw_nonbridge : ∀ e, ¬ S.network.graph.IsBridge e → ∃ f, recipe e = .raw f
  raw_bridge : ∀ e f, recipe e = .raw f →
    (S.network.graph.IsBridge e ↔ O.network.graph.IsBridge f)
  raw_injective : ∀ e f a, recipe e = .raw a → recipe f = .raw a → e = f

noncomputable def initialDecoration (O : Source.{u,v,w} X) : Decoration O O where
  vertex := Function.Embedding.refl _
  root := rfl
  taxa _ := rfl
  calendar _ := rfl
  indegree _ := rfl
  outdegree _ := rfl
  sameBlob _ _ := Iff.rfl
  rootBlob_surjective v hv := ⟨v,hv,rfl⟩
  recipe := Recipe.raw
  endpoints _ := ⟨rfl,rfl⟩
  raw_nonbridge e _ := ⟨e,rfl⟩
  raw_bridge e f h := by cases h; rfl
  raw_injective e f a he hf := by cases he; cases hf; rfl

lemma actual_decoration_hybrid_iff (O S : Source X) (D : Decoration O S) (x : S.Vertex) :
    S.network.graph.IsHybrid x ↔ O.network.graph.IsHybrid (D.vertex x) := by
  simp only [EdgeGraph.IsHybrid,D.indegree,D.outdegree]

lemma actual_original_bridge_target_ordinary (O : Source X) (e : O.Edge)
    (he : O.network.graph.IsBridge e) : O.network.graph.inDegree (O.network.graph.target e) = 1 := by
  apply O.network.indegree_one_of_nonroot_nonhybrid (O.network.edge_target_ne_root e)
  intro hh
  exact actual_hybrid_parent_nonbridge O.network e hh he

/-- Any physical current bridge has an actual finite ORIGINAL source span;
raw original bridges are interpreted with their proved original indegree. -/
noncomputable def bridgeSpan (O S : Source X) (D : Decoration O S) (e : S.Edge)
    (he : S.network.graph.IsBridge e) :
    OriginalSpan O.network (D.vertex (S.network.graph.target e)) (D.vertex (S.network.graph.source e)) := by
  have hep := D.endpoints e
  cases hr : D.recipe e with
  | raw f =>
      rw [hr] at hep
      have ho := (D.raw_bridge e f hr).mp he
      simp only [Recipe.input,Recipe.output] at hep
      rw [← hep.1,← hep.2]
      exact OriginalSpan.edge f (actual_original_bridge_target_ordinary O f ho)
  | span a b word =>
      rw [hr] at hep
      simp only [Recipe.input,Recipe.output] at hep
      rw [← hep.1,← hep.2]
      exact word

end G1DecoratedOriginalProvenance
