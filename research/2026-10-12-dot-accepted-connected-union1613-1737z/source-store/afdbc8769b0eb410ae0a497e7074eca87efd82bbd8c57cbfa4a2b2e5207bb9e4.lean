import G5NormalizedSwitchingQuartetCompatibility

/-!
# Explicit edge-split encoding after suppressing the normalized binary root
Contributor: dot / OpenAI, 2026-10-03.
A proper rooted node cluster gives the unordered edge cut {C, L\C}. The full
root cluster is removed, and complementary root-child cuts become one cut.
This is an explicit finite split encoding of binary-root suppression; it is
not an adjacency-graph renderer or a semidirected-network convention.
The original hand contract's quartet target is precisely these edge-induced
unordered splits, tested on an original quartet embedding.
-/
namespace GProgram.G5.Normalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open scoped Classical
variable {X : Type*} [Fintype X]

lemma tree_cluster_subset_leaves (T : Genealogy X) {D : Finset X} (hD : D ∈ treeClusters T) : D ⊆ T.leaves := by
  induction T with
  | leaf x =>
    have he : D = {x} := by simpa only [treeClusters,Finset.mem_singleton] using hD
    subst D
    exact Finset.Subset.refl _
  | graft a b ha hb =>
    rcases Finset.mem_insert.mp hD with hr | hchild
    · exact hr ▸ Finset.Subset.refl _
    · rcases Finset.mem_union.mp hchild with h | h
      · exact (ha h).trans Finset.subset_union_left
      · exact (hb h).trans Finset.subset_union_right

/-- Proper rooted tree edges become unordered cuts. Inserting complementary
clusters creates no second cut, so the two binary-root edges are suppressed to
one unrooted edge. Root/full-cluster and empty sides are explicitly removed. -/
noncomputable def rootSuppressedCuts (T : Genealogy X) : Finset (Finset (Finset X)) :=
  ((treeClusters T).filter (fun D => D ⊆ T.leaves ∧ D.Nonempty ∧ (T.leaves \ D).Nonempty)).image
    (fun D => {D,T.leaves \ D})

def cutDisplaysFirst (cut : Finset (Finset X)) (q : Fin 4 ↪ X) : Prop :=
  ∃ D ∈ cut, q 0 ∈ D ∧ q 1 ∈ D ∧ q 2 ∉ D ∧ q 3 ∉ D

def rootSuppressedTreeQuartet (T : Genealogy X) (q : Fin 4 ↪ X) : Prop :=
  ∃ cut ∈ rootSuppressedCuts T, cutDisplaysFirst cut q

/-- The two actual child edges of a normalized binary root encode the SAME
unordered cut, under the proved original well-labeling/disjointness contract. -/
theorem binary_root_child_cuts_identified (a b : Genealogy X) (hd : Disjoint a.leaves b.leaves) :
    ({a.leaves,(Genealogy.graft a b).leaves \ a.leaves} : Finset (Finset X)) =
      {b.leaves,(Genealogy.graft a b).leaves \ b.leaves} := by
  have hleft : (a.leaves ∪ b.leaves) \ a.leaves = b.leaves := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨ha | hb,hn⟩
      · exact False.elim (hn ha)
      · exact hb
    · intro hb
      exact ⟨Or.inr hb,fun ha => Finset.disjoint_left.mp hd ha hb⟩
  have hright : (a.leaves ∪ b.leaves) \ b.leaves = a.leaves := by
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨ha | hb,hn⟩
      · exact ha
      · exact False.elim (hn hb)
    · intro ha
      exact ⟨Or.inl ha,fun hb => Finset.disjoint_left.mp hd ha hb⟩
  simp only [Genealogy.leaves,hleft,hright]
  exact Finset.pair_comm _ _

/-- Explicit binary-root suppression preserves EVERY original quartet cut.
The original four labels are retained in the actual normalized tree. -/
theorem root_suppressed_cut_quartet_iff_cluster_quartet (T : Genealogy X) (q : Fin 4 ↪ X)
    (hq : ∀ i, q i ∈ T.leaves) : rootSuppressedTreeQuartet T q ↔ treeHasQuartet T q := by
  constructor
  · rintro ⟨cut,hcut,C,hC,hside⟩
    obtain ⟨D,hD,hcutEq⟩ := Finset.mem_image.mp hcut
    obtain ⟨hcluster,hsub,hnD,hnComp⟩ := Finset.mem_filter.mp hD
    rw [←hcutEq] at hC
    rcases Finset.mem_insert.mp hC with hCD | hCD
    · subst C
      exact ⟨D,hcluster,Or.inl hside⟩
    · have heC : C = T.leaves \ D := Finset.mem_singleton.mp hCD
      rw [heC] at hside
      have h2 : q 2 ∈ D := by
        by_contra hn
        exact hside.2.2.1 (Finset.mem_sdiff.mpr ⟨hq 2,hn⟩)
      have h3 : q 3 ∈ D := by
        by_contra hn
        exact hside.2.2.2 (Finset.mem_sdiff.mpr ⟨hq 3,hn⟩)
      exact ⟨D,hcluster,Or.inr ⟨h2,h3,(Finset.mem_sdiff.mp hside.1).2,(Finset.mem_sdiff.mp hside.2.1).2⟩⟩
  · rintro ⟨D,hcluster,hside⟩
    have hsub := tree_cluster_subset_leaves T hcluster
    have hnD : D.Nonempty := by
      rcases hside with h | h
      · exact ⟨q 0,h.1⟩
      · exact ⟨q 2,h.1⟩
    have hnComp : (T.leaves \ D).Nonempty := by
      rcases hside with h | h
      · exact ⟨q 2,Finset.mem_sdiff.mpr ⟨hq 2,h.2.2.1⟩⟩
      · exact ⟨q 0,Finset.mem_sdiff.mpr ⟨hq 0,h.2.2.1⟩⟩
    refine ⟨{D,T.leaves \ D},Finset.mem_image.mpr ⟨D,Finset.mem_filter.mpr ⟨hcluster,hsub,hnD,hnComp⟩,rfl⟩,?_⟩
    rcases hside with h | h
    · exact ⟨D,Finset.mem_insert_self _ _,h⟩
    · refine ⟨T.leaves \ D,Finset.mem_insert_of_mem (Finset.mem_singleton_self _),?_,?_,?_,?_⟩
      · exact Finset.mem_sdiff.mpr ⟨hq 0,h.2.2.1⟩
      · exact Finset.mem_sdiff.mpr ⟨hq 1,h.2.2.2⟩
      · intro hm; exact (Finset.mem_sdiff.mp hm).2 h.1
      · intro hm; exact (Finset.mem_sdiff.mp hm).2 h.2.1

/-- The binary-root edge identification is instantiated on an ACTUAL output
of original-switching pruning, with disjointness derived rather than supplied. -/
theorem actual_pruned_binary_root_child_cuts
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (N : RootedBinary V E X) (S : N.Switching) (A : Finset X)
    {a b : Genealogy X} (eval : PrunedAt N S A N.root (some (.graft a b))) :
    ({a.leaves,(Genealogy.graft a b).leaves \ a.leaves} : Finset (Finset X)) =
      {b.leaves,(Genealogy.graft a b).leaves \ b.leaves} := by
  exact binary_root_child_cuts_identified a b (prunedAt_wellLabelled N S A eval).2.2

#print axioms actual_pruned_binary_root_child_cuts
#print axioms binary_root_child_cuts_identified
#print axioms root_suppressed_cut_quartet_iff_cluster_quartet
end GProgram.G5.Normalization
