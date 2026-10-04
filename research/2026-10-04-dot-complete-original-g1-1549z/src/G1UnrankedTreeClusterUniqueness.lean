import G5BinaryRootSuppressedCutEncoding
import UnifiedLean.Source.UnrankedGenealogyObservation

/-! A complete well-labelled rooted binary hierarchy determines the ACTUAL
unranked tree modulo child swaps. This standard uniqueness bridge keeps the
entire tree family stronger than its union of cluster/split observations. -/
namespace G1UnrankedTreeClusterUniqueness
set_option backward.isDefEq.respectTransparency false
open GProgram.SourceForest GProgram.G5.Normalization
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical
variable {X : Type*} [Fintype X]

lemma cluster_nonempty (t : Genealogy X) {C : Finset X} (hc : C ∈ treeClusters t) : C.Nonempty := by
  induction t with
  | leaf x =>
    have he : C = {x} := by simpa [treeClusters] using hc
    exact he ▸ Finset.singleton_nonempty x
  | graft a b ha hb =>
    rcases Finset.mem_insert.mp hc with he | hc
    · exact he ▸ (tree_leaves_nonempty a).mono Finset.subset_union_left
    · exact (Finset.mem_union.mp hc).elim ha hb

lemma clusters_equal_leaves {a b : Genealogy X} (h : treeClusters a = treeClusters b) : a.leaves = b.leaves :=
  Finset.Subset.antisymm (tree_cluster_subset_leaves b (h ▸ tree_root_cluster_mem a))
    (tree_cluster_subset_leaves a (h.symm ▸ tree_root_cluster_mem b))

lemma disjoint_union_ne_left (A B : Finset X) (hd : Disjoint A B) (hb : B.Nonempty) : A ∪ B ≠ A := by
  intro he
  obtain ⟨x,hx⟩ := hb
  exact Finset.disjoint_left.mp hd (he ▸ Finset.mem_union_right A hx) hx

lemma proper_cluster_in_child (a b : Genealogy X) {C : Finset X}
    (hc : C ∈ treeClusters (.graft a b)) (hne : C ≠ a.leaves ∪ b.leaves) :
    C ⊆ a.leaves ∨ C ⊆ b.leaves := by
  rcases Finset.mem_insert.mp hc with he | hc
  · exact False.elim (hne he)
  · exact (Finset.mem_union.mp hc).elim
      (fun h => Or.inl (tree_cluster_subset_leaves a h)) (fun h => Or.inr (tree_cluster_subset_leaves b h))

lemma two_child_alignment (A B C D : Finset X)
    (ha : A.Nonempty) (hb : B.Nonempty) (hc : C.Nonempty) (hd : D.Nonempty)
    (hab : Disjoint A B) (hcd : Disjoint C D) (he : A ∪ B = C ∪ D)
    (hA : A ⊆ C ∨ A ⊆ D) (hB : B ⊆ C ∨ B ⊆ D) :
    (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  have matchSides (hAC : A ⊆ C) (hBD : B ⊆ D) : A = C ∧ B = D := by
    constructor
    · apply Finset.Subset.antisymm hAC
      intro x hx
      have hm : x ∈ A ∪ B := he.symm ▸ Finset.mem_union_left D hx
      rcases Finset.mem_union.mp hm with hxA | hxB
      · exact hxA
      · exact False.elim (Finset.disjoint_left.mp hcd hx (hBD hxB))
    · apply Finset.Subset.antisymm hBD
      intro x hx
      have hm : x ∈ A ∪ B := he.symm ▸ Finset.mem_union_right C hx
      rcases Finset.mem_union.mp hm with hxA | hxB
      · exact False.elim (Finset.disjoint_left.mp hcd (hAC hxA) hx)
      · exact hxB
  rcases hA with hAC | hAD <;> rcases hB with hBC | hBD
  · obtain ⟨x,hx⟩ := hd
    have hm : x ∈ A ∪ B := he.symm ▸ Finset.mem_union_right C hx
    exact False.elim ((Finset.mem_union.mp hm).elim
      (fun h => Finset.disjoint_left.mp hcd (hAC h) hx)
      (fun h => Finset.disjoint_left.mp hcd (hBC h) hx))
  · exact Or.inl (matchSides hAC hBD)
  · right
    constructor
    · apply Finset.Subset.antisymm hAD
      intro x hx
      have hm : x ∈ A ∪ B := he.symm ▸ Finset.mem_union_right C hx
      exact (Finset.mem_union.mp hm).elim id
        (fun h => False.elim (Finset.disjoint_left.mp hcd (hBC h) hx))
    · apply Finset.Subset.antisymm hBC
      intro x hx
      have hm : x ∈ A ∪ B := he.symm ▸ Finset.mem_union_left D hx
      exact (Finset.mem_union.mp hm).elim
        (fun h => False.elim (Finset.disjoint_left.mp hcd hx (hAD h))) id
  · obtain ⟨x,hx⟩ := hc
    have hm : x ∈ A ∪ B := he.symm ▸ Finset.mem_union_left D hx
    exact False.elim ((Finset.mem_union.mp hm).elim
      (fun h => Finset.disjoint_left.mp hcd hx (hAD h))
      (fun h => Finset.disjoint_left.mp hcd hx (hBD h)))

lemma child_clusters_filter (a b : Genealogy X) (hd : Disjoint a.leaves b.leaves) :
    (treeClusters (.graft a b)).filter (fun C => C ⊆ a.leaves) = treeClusters a := by
  ext C
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hc,hsub⟩
    rcases Finset.mem_insert.mp hc with he | hc
    · obtain ⟨x,hx⟩ := tree_leaves_nonempty b
      have hm : x ∈ C := he.symm ▸ Finset.mem_union_right a.leaves hx
      exact False.elim (Finset.disjoint_left.mp hd (hsub hm) hx)
    · rcases Finset.mem_union.mp hc with ha | hb
      · exact ha
      · obtain ⟨x,hx⟩ := cluster_nonempty b hb
        exact False.elim (Finset.disjoint_left.mp hd (hsub hx) (tree_cluster_subset_leaves b hb hx))
  · intro hc
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ hc),tree_cluster_subset_leaves a hc⟩

lemma binary_leaves_not_singleton (a b : Genealogy X) (hd : Disjoint a.leaves b.leaves) (x : X) :
    a.leaves ∪ b.leaves ≠ {x} := by
  intro he
  obtain ⟨y,hy⟩ := tree_leaves_nonempty a
  obtain ⟨z,hz⟩ := tree_leaves_nonempty b
  have hyx : y = x := Finset.mem_singleton.mp (he ▸ Finset.mem_union_left b.leaves hy)
  have hzx : z = x := Finset.mem_singleton.mp (he ▸ Finset.mem_union_right a.leaves hz)
  exact Finset.disjoint_left.mp hd (hyx ▸ hy) (hzx ▸ hz)

/-- Every complete well-labelled hierarchy corresponds to exactly one
rooted unranked binary tree. No cluster equality is confused with union
clusters across multiple displayed trees. -/
theorem actual_tree_clusters_determine_unranked (a b : Genealogy X)
    (ha : a.WellLabelled) (hb : b.WellLabelled) (h : treeClusters a = treeClusters b) :
    toUnranked a = toUnranked b := by
  apply (toUnranked_eq_iff a b).mpr
  induction a generalizing b with
  | leaf x =>
    cases b with
    | leaf y =>
      have he : ({x} : Finset X) = {y} := clusters_equal_leaves h
      have hxy : x = y := Finset.mem_singleton.mp (he ▸ Finset.mem_singleton_self x)
      subst y
      exact UnorderedEquiv.refl _
    | graft c d =>
      exact False.elim (binary_leaves_not_singleton c d hb.2.2 x (clusters_equal_leaves h).symm)
  | graft a c iha ihc =>
    cases b with
    | leaf y =>
      exact False.elim (binary_leaves_not_singleton a c ha.2.2 y (clusters_equal_leaves h))
    | graft b d =>
      have he : a.leaves ∪ c.leaves = b.leaves ∪ d.leaves := clusters_equal_leaves h
      have hA : a.leaves ⊆ b.leaves ∨ a.leaves ⊆ d.leaves := by
        apply proper_cluster_in_child b d (h ▸ Finset.mem_insert_of_mem (Finset.mem_union_left _ (tree_root_cluster_mem a)))
        rw [←he]
        exact (disjoint_union_ne_left a.leaves c.leaves ha.2.2 (tree_leaves_nonempty c)).symm
      have hC : c.leaves ⊆ b.leaves ∨ c.leaves ⊆ d.leaves := by
        apply proper_cluster_in_child b d (h ▸ Finset.mem_insert_of_mem (Finset.mem_union_right _ (tree_root_cluster_mem c)))
        rw [←he,Finset.union_comm]
        exact (disjoint_union_ne_left c.leaves a.leaves ha.2.2.symm (tree_leaves_nonempty a)).symm
      rcases two_child_alignment a.leaves c.leaves b.leaves d.leaves (tree_leaves_nonempty a)
        (tree_leaves_nonempty c) (tree_leaves_nonempty b) (tree_leaves_nonempty d) ha.2.2 hb.2.2 he hA hC with hmatch | hswap
      · have hab : treeClusters a = treeClusters b := by
          rw [←child_clusters_filter a c ha.2.2,←child_clusters_filter b d hb.2.2,h,hmatch.1]
        have hcd : treeClusters c = treeClusters d := by
          have haSwap : treeClusters (.graft a c) = treeClusters (.graft c a) := by simp [treeClusters,Finset.union_comm]
          have hbSwap : treeClusters (.graft b d) = treeClusters (.graft d b) := by simp [treeClusters,Finset.union_comm]
          rw [←child_clusters_filter c a ha.2.2.symm,←child_clusters_filter d b hb.2.2.symm,←haSwap,h,hbSwap,hmatch.2]
        exact UnorderedEquiv.graft (iha b ha.1 hb.1 hab) (ihc d ha.2.1 hb.2.1 hcd)
      · have hab : treeClusters a = treeClusters d := by
          have hbSwap : treeClusters (.graft b d) = treeClusters (.graft d b) := by simp [treeClusters,Finset.union_comm]
          rw [←child_clusters_filter a c ha.2.2,←child_clusters_filter d b hb.2.2.symm,h,hbSwap,hswap.1]
        have hcd : treeClusters c = treeClusters b := by
          have haSwap : treeClusters (.graft a c) = treeClusters (.graft c a) := by simp [treeClusters,Finset.union_comm]
          rw [←child_clusters_filter c a ha.2.2.symm,←child_clusters_filter b d hb.2.2,←haSwap,h,hswap.2]
        exact (UnorderedEquiv.graft (iha d ha.1 hb.2.1 hab) (ihc b ha.2.1 hb.1 hcd)).trans
          (UnorderedEquiv.swap d b)

#print axioms actual_tree_clusters_determine_unranked
end G1UnrankedTreeClusterUniqueness
