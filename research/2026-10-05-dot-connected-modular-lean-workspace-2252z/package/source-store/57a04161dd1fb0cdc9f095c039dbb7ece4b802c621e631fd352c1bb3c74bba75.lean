import G5OriginalSwitchingPruning

/-!
# Actual original switching pruning/unary evaluation preserves every cluster
Contributor: dot / OpenAI, 2026-10-03.
Every nonempty original descendant cluster appears in the evaluated rooted
binary tree, and every output cluster comes from an actual original vertex.
Empty twigs and duplicate unary-path clusters are removed by the actual
joinPruned computation. No desired cluster equality is a structure field.
-/
namespace GProgram.G5.Normalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

noncomputable def treeClusters : Genealogy X → Finset (Finset X)
  | .leaf x => {{x}}
  | .graft a b => insert (a.leaves ∪ b.leaves) (treeClusters a ∪ treeClusters b)

noncomputable def optionTreeClusters : Option (Genealogy X) → Finset (Finset X)
  | none => ∅
  | some t => treeClusters t

lemma tree_leaves_nonempty (t : Genealogy X) : t.leaves.Nonempty := by
  induction t with
  | leaf x => simp [Genealogy.leaves]
  | graft a b ha hb => exact ha.mono Finset.subset_union_left

lemma tree_root_cluster_mem (t : Genealogy X) : t.leaves ∈ treeClusters t := by
  cases t <;> simp [Genealogy.leaves,treeClusters]

lemma option_root_cluster_mem (T : Option (Genealogy X)) {D : Finset X}
    (hD : D.Nonempty) (he : Genealogy.optionLeaves T = D) : D ∈ optionTreeClusters T := by
  cases T with
  | none => rw [←he] at hD; exact False.elim (Finset.not_nonempty_empty hD)
  | some t => rw [←he]; exact tree_root_cluster_mem t

lemma option_clusters_left_join (a b : Option (Genealogy X)) :
    optionTreeClusters a ⊆ optionTreeClusters (Genealogy.joinPruned a b) := by
  intro D hD
  cases a <;> cases b <;> simp_all [Genealogy.joinPruned,optionTreeClusters,treeClusters]

lemma option_clusters_right_join (a b : Option (Genealogy X)) :
    optionTreeClusters b ⊆ optionTreeClusters (Genealogy.joinPruned a b) := by
  intro D hD
  cases a <;> cases b <;> simp_all [Genealogy.joinPruned,optionTreeClusters,treeClusters]

lemma mem_option_clusters_join (a b : Option (Genealogy X)) (D : Finset X) :
    D ∈ optionTreeClusters (Genealogy.joinPruned a b) ↔
      D ∈ optionTreeClusters a ∨ D ∈ optionTreeClusters b ∨
        (D.Nonempty ∧ Genealogy.optionLeaves a ∪ Genealogy.optionLeaves b = D) := by
  constructor
  · intro h
    cases a with
    | none => exact Or.inr (Or.inl h)
    | some a =>
      cases b with
      | none => exact Or.inl h
      | some b =>
        change D ∈ insert (a.leaves ∪ b.leaves) (treeClusters a ∪ treeClusters b) at h
        rcases Finset.mem_insert.mp h with hr | hc
        · exact Or.inr (Or.inr ⟨hr ▸ (tree_leaves_nonempty a).mono Finset.subset_union_left,hr.symm⟩)
        · exact (Finset.mem_union.mp hc).elim Or.inl (fun h => Or.inr (Or.inl h))
  · rintro (ha | hb | ⟨hD,he⟩)
    · exact option_clusters_left_join a b ha
    · exact option_clusters_right_join a b hb
    · apply option_root_cluster_mem _ hD
      rw [Genealogy.joinPruned_leaves]
      exact he

/-- All actual nonempty original vertex-descendant clusters below v. -/
def VertexClusterBelow (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    (v : V) (D : Finset X) : Prop :=
  D.Nonempty ∧ ∃ w : V, S.graph.DReach v w ∧ sampledDescendants N S A w = D

lemma vertexClusterBelow_children (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    (v : V) (D : Finset X) :
    VertexClusterBelow N S A v D ↔
      (D.Nonempty ∧ sampledDescendants N S A v = D) ∨
        ∃ e ∈ outgoing N S v, VertexClusterBelow N S A (S.graph.target e) D := by
  constructor
  · rintro ⟨hD,w,hw,he⟩
    rcases Relation.ReflTransGen.cases_head hw with hr | ⟨z,hs,hz⟩
    · exact Or.inl ⟨hD,hr.symm ▸ he⟩
    · obtain ⟨e,hs,ht⟩ := hs
      exact Or.inr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,hD,w,ht.symm ▸ hz,he⟩
  · rintro (⟨hD,he⟩ | ⟨e,he,hD,w,hw,hcluster⟩)
    · exact ⟨hD,v,.refl,he⟩
    · have hs := (Finset.mem_filter.mp he).2
      exact ⟨hD,w,(Relation.ReflTransGen.single ⟨e,hs,rfl⟩).trans hw,hcluster⟩

/-- Assumption-free cluster preservation for EVERY result of the actual
pruning/unary evaluation on EVERY original switching and finite selected set. -/
theorem prunedAt_exact_original_clusters (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    {v : V} {T : Option (Genealogy X)} (eval : PrunedAt N S A v T) :
    ∀ D : Finset X, D ∈ optionTreeClusters T ↔ VertexClusterBelow N S A v D := by
  classical
  induction eval with
  | taxon x =>
    intro D
    have hout : outgoing N S (N.leaf x) = ∅ := Finset.card_eq_zero.mp (S.selected_leaf_degrees x).2
    rw [vertexClusterBelow_children,hout]
    simp only [Finset.notMem_empty,false_and,exists_false,or_false]
    rw [sampledDescendants_taxon]
    by_cases hx : x ∈ A
    · simp only [if_pos hx,optionTreeClusters,treeClusters,Finset.mem_singleton]
      constructor
      · intro he; subst D; exact ⟨Finset.singleton_nonempty _,rfl⟩
      · rintro ⟨_,he⟩; exact he.symm
    · simp only [if_neg hx,optionTreeClusters,Finset.notMem_empty]
      constructor
      · intro h; exact False.elim h
      · rintro ⟨hD,he⟩; rw [←he] at hD; exact Finset.not_nonempty_empty hD
  | dead v hn hout =>
    intro D
    rw [vertexClusterBelow_children,hout]
    simp only [Finset.notMem_empty,false_and,exists_false,or_false]
    rw [sampledDescendants_children N S A v hn,hout]
    simp only [Finset.biUnion_empty,optionTreeClusters,Finset.notMem_empty]
    constructor
    · intro h; exact False.elim h
    · rintro ⟨hD,he⟩; rw [←he] at hD; exact Finset.not_nonempty_empty hD
  | @unary v hn e hout a child ih =>
    intro D
    rw [vertexClusterBelow_children,hout]
    simp only [Finset.mem_singleton,exists_eq_left]
    rw [sampledDescendants_children N S A v hn,hout]
    rw [Finset.singleton_biUnion]
    rw [←prunedAt_exact_leaves N S A child,←ih D]
    constructor
    · intro h; exact Or.inr h
    · rintro (⟨hD,he⟩ | h)
      · exact option_root_cluster_mem a hD he
      · exact h
  | @binary v hn e f hef hout a b left right ihl ihr =>
    intro D
    rw [mem_option_clusters_join,vertexClusterBelow_children,hout]
    simp only [Finset.mem_insert,Finset.mem_singleton,or_and_right,exists_or,exists_eq_left]
    rw [sampledDescendants_children N S A v hn,hout]
    rw [Finset.biUnion_insert,Finset.singleton_biUnion]
    rw [←prunedAt_exact_leaves N S A left,←prunedAt_exact_leaves N S A right,←ihl D,←ihr D]
    tauto

/-- At the actual root, there is no extra ancestry input: all original vertices
are reachable in the switching, so the evaluated tree has exactly all original
nonempty selected clusters, including all unary/root reductions. -/
theorem root_pruning_exact_original_clusters (N : RootedBinary V E X) (C : Calendar N.graph)
    (S : N.Switching) (A : Finset X) :
    ∃ T : Option (Genealogy X), PrunedAt N S A N.root T ∧
      ∀ D : Finset X, D ∈ optionTreeClusters T ↔ D.Nonempty ∧ ∃ v : V, sampledDescendants N S A v = D := by
  obtain ⟨T,hT⟩ := original_switching_pruning_exists N C S A N.root
  refine ⟨T,hT,?_⟩
  intro D
  rw [prunedAt_exact_original_clusters N S A hT D]
  constructor
  · rintro ⟨hD,v,_,he⟩; exact ⟨hD,v,he⟩
  · rintro ⟨hD,v,he⟩; exact ⟨hD,v,S.selected_rooted v,he⟩

#print axioms prunedAt_exact_original_clusters
#print axioms root_pruning_exact_original_clusters
end GProgram.G5.Normalization
