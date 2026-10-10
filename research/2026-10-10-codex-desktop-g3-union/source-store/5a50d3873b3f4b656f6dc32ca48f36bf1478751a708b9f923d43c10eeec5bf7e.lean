import G5FairNormalizedCutQuartetIdentification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Two actual admitted fair positive quartet-tree sources
Contributor: dot / OpenAI, 2026-10-03.
These are concrete original edge-indexed rooted LSA binary trees, with four
contemporaneous original tips. The two leaf embeddings differ. Every edge
has strict positive duration and constant rate one; the ancestral rate is one.
No target property or observation law is part of the source admission.
-/
namespace GProgram.G5.Sharpness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw

abbrev Vertex := Fin 7
abbrev Edge := Fin 6
abbrev Taxon := Fin 4

def treeGraph : EdgeGraph Vertex Edge where
  source := ![0,0,1,1,2,2]
  target := ![1,2,3,4,5,6]

def age : Vertex → ℝ := ![2,1,1,0,0,0,0]

def treeCalendar : Calendar treeGraph where
  age := age
  edge_older := by
    intro e; fin_cases e
    all_goals first | (change (1 : ℝ) < 2; norm_num) | (change (0 : ℝ) < 1; norm_num)

lemma graph_acyclic : treeGraph.Acyclic := by
  have hh : ∀ a b : Vertex, Relation.TransGen treeGraph.DStep a b → age b < age a := by
    intro a b h
    induction h with
    | single h =>
        obtain ⟨e,rfl,rfl⟩ := h
        exact treeCalendar.edge_older e
    | tail h hstep ih =>
        obtain ⟨e,rfl,rfl⟩ := hstep
        exact (treeCalendar.edge_older e).trans ih
  intro a h
  exact (lt_irrefl (age a)) (hh a a h)

lemma root_to_vertex (v : Vertex) : treeGraph.DReach 0 v := by
  have h1 : treeGraph.DReach 0 1 := Relation.ReflTransGen.single ⟨0,rfl,rfl⟩
  have h2 : treeGraph.DReach 0 2 := Relation.ReflTransGen.single ⟨1,rfl,rfl⟩
  fin_cases v
  · exact .refl
  · exact h1
  · exact h2
  · exact h1.tail ⟨2,rfl,rfl⟩
  · exact h1.tail ⟨3,rfl,rfl⟩
  · exact h2.tail ⟨4,rfl,rfl⟩
  · exact h2.tail ⟨5,rfl,rfl⟩

lemma no_hybrid (v : Vertex) : ¬ treeGraph.IsHybrid v := by
  unfold EdgeGraph.IsHybrid
  fin_cases v <;> decide

def leafA : Taxon ↪ Vertex := ⟨![3,4,5,6],by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
def leafB : Taxon ↪ Vertex := ⟨![3,5,4,6],by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

lemma root_degree : treeGraph.inDegree 0 = 0 ∧ treeGraph.outDegree 0 = 2 := by decide
lemma leaf_degree (v : Vertex) (hv : 3 ≤ v.val) :
    treeGraph.inDegree v = 1 ∧ treeGraph.outDegree v = 0 := by
  fin_cases v <;> norm_num at hv
  all_goals decide
lemma internal_degree (v : Vertex) (hv : v = 1 ∨ v = 2) :
    treeGraph.inDegree v = 1 ∧ treeGraph.outDegree v = 2 := by
  rcases hv with rfl | rfl <;> decide

lemma avoid_left_tip (v : Vertex) (hv : v ≠ 0) (h3 : v ≠ 1) (ht : v ≠ 3) :
    treeGraph.AvoidReach v 0 3 := by
  refine ⟨hv.symm,ht.symm,?_⟩
  exact (Relation.ReflTransGen.single ⟨⟨0,rfl,rfl⟩,hv.symm,h3.symm⟩).tail
    ⟨⟨2,rfl,rfl⟩,h3.symm,ht.symm⟩
lemma avoid_right_tip (v : Vertex) (hv : v ≠ 0) (h2 : v ≠ 2) (ht : v ≠ 5) :
    treeGraph.AvoidReach v 0 5 := by
  refine ⟨hv.symm,ht.symm,?_⟩
  exact (Relation.ReflTransGen.single ⟨⟨1,rfl,rfl⟩,hv.symm,h2.symm⟩).tail
    ⟨⟨4,rfl,rfl⟩,h2.symm,ht.symm⟩

lemma graph_least_stable (L : Taxon ↪ Vertex) (hl : (∃ x, L x = 3) ∧ (∃ x, L x = 5))
    (v : Vertex) (hv : ∀ x, treeGraph.Dominates 0 v (L x)) : v = 0 := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := hl
  have h3 : treeGraph.Dominates 0 v 3 := ha ▸ hv a
  have h5 : treeGraph.Dominates 0 v 5 := hb ▸ hv b
  fin_cases v
  · rfl
  · exact False.elim (h5 (avoid_right_tip 1 (by decide) (by decide) (by decide)))
  · exact False.elim (h3 (avoid_left_tip 2 (by decide) (by decide) (by decide)))
  · exact False.elim (h5 (avoid_right_tip 3 (by decide) (by decide) (by decide)))
  · exact False.elim (h3 (avoid_left_tip 4 (by decide) (by decide) (by decide)))
  · exact False.elim (h3 (avoid_left_tip 5 (by decide) (by decide) (by decide)))
  · exact False.elim (h3 (avoid_left_tip 6 (by decide) (by decide) (by decide)))

def sourceA : RootedBinary Vertex Edge Taxon where
  graph := treeGraph
  root := 0
  leaf := leafA
  at_least_two_taxa := by decide
  root_degrees := root_degree
  leaf_degrees := by intro x; apply leaf_degree; fin_cases x <;> decide
  internal_degrees := by
    intro v hr hl; left; apply internal_degree
    fin_cases v
    · exact False.elim (hr rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hl 0 rfl)
    · exact False.elim (hl 1 rfl)
    · exact False.elim (hl 2 rfl)
    · exact False.elim (hl 3 rfl)
  acyclic := graph_acyclic
  rooted := root_to_vertex
  least_stable := graph_least_stable leafA ⟨⟨0,rfl⟩,⟨2,rfl⟩⟩

def sourceB : RootedBinary Vertex Edge Taxon where
  graph := treeGraph
  root := 0
  leaf := leafB
  at_least_two_taxa := by decide
  root_degrees := root_degree
  leaf_degrees := by intro x; apply leaf_degree; fin_cases x <;> decide
  internal_degrees := by
    intro v hr hl; left; apply internal_degree
    fin_cases v
    · exact False.elim (hr rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hl 0 rfl)
    · exact False.elim (hl 2 rfl)
    · exact False.elim (hl 1 rfl)
    · exact False.elim (hl 3 rfl)
  acyclic := graph_acyclic
  rooted := root_to_vertex
  least_stable := graph_least_stable leafB ⟨⟨0,rfl⟩,⟨1,rfl⟩⟩

def rates : PositivePairRates Edge where
  edge := fun _ => 1
  edge_pos := fun _ => by norm_num
  ancestral := 1
  ancestral_pos := by norm_num

noncomputable def registryA : OriginalParentRegistry sourceA := canonicalParentRegistry sourceA
noncomputable def registryB : OriginalParentRegistry sourceB := canonicalParentRegistry sourceB

lemma cut_childA : ∀ e, sourceA.graph.IsHybrid (sourceA.graph.source e) → sourceA.graph.IsBridge e := by
  intro e he; exact False.elim (no_hybrid _ he)
lemma cut_childB : ∀ e, sourceB.graph.IsHybrid (sourceB.graph.source e) → sourceB.graph.IsBridge e := by
  intro e he; exact False.elim (no_hybrid _ he)
lemma tipsA : ∀ x, treeCalendar.age (sourceA.leaf x) = 0 := by
  intro x; fin_cases x <;> rfl
lemma tipsB : ∀ x, treeCalendar.age (sourceB.leaf x) = 0 := by
  intro x; fin_cases x <;> rfl

#print axioms sourceA
#print axioms sourceB
#print axioms cut_childA
#print axioms tipsA
end GProgram.G5.Sharpness
