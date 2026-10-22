/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/kernel/runtime/certificate.

Independent CELL-clade representation. Clades do not identify cells by type.
The complete standard-refinement/frontier hand proof is in the companion note.
This source is a continuation, not a certificate for the final complexity claim.
-/
import PolytomyBlockRealization

namespace PolytomyReductionModel

noncomputable section
universe u

def cellSet {A : Type u} [DecidableEq A] (t : BTree A) : Finset A := observed id t

inductive CellClade {A : Type u} [DecidableEq A] : Finset A → BTree A → Prop where
  | root (t : BTree A) : CellClade (cellSet t) t
  | left {C : Finset A} {l r : BTree A} : CellClade C l → CellClade C (.node l r)
  | right {C : Finset A} {l r : BTree A} : CellClade C r → CellClade C (.node l r)

def CellRefines {A : Type u} [DecidableEq A] (R T : BTree A) : Prop :=
  ∀ C, CellClade C R → CellClade C T

theorem cellSet_nonempty {A : Type u} [DecidableEq A] (t : BTree A) :
    (cellSet t).Nonempty := by
  induction t with
  | leaf a => exact ⟨a, Finset.mem_singleton_self a⟩
  | node l r ihl ihr =>
      obtain ⟨a, ha⟩ := ihl
      exact ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩

theorem mem_cellSet {A : Type u} [DecidableEq A] (a : A) (t : BTree A) :
    a ∈ cellSet t ↔ a ∈ leaves t := by
  simp only [cellSet, observed_eq_leaves_image, List.map_id, List.mem_toFinset]

theorem CellClade.subset {A : Type u} [DecidableEq A] {C : Finset A}
    {t : BTree A} (h : CellClade C t) : C ⊆ cellSet t := by
  induction h with
  | root t => exact Finset.Subset.refl _
  | left h ih => exact ih.trans Finset.subset_union_left
  | right h ih => exact ih.trans Finset.subset_union_right

theorem CellClade.nonempty {A : Type u} [DecidableEq A] {C : Finset A}
    {t : BTree A} (h : CellClade C t) : C.Nonempty := by
  induction h with
  | root t => exact cellSet_nonempty t
  | left h ih => exact ih
  | right h ih => exact ih

theorem cellClade_node_iff {A : Type u} [DecidableEq A] (C : Finset A)
    (l r : BTree A) : CellClade C (.node l r) ↔
      C = cellSet (.node l r) ∨ CellClade C l ∨ CellClade C r := by
  constructor
  · intro h
    cases h with
    | root => exact Or.inl rfl
    | left h => exact Or.inr (Or.inl h)
    | right h => exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · rw [h]; exact .root _
    · exact .left h
    · exact .right h

theorem node_cellSets_disjoint {A : Type u} [DecidableEq A] (l r : BTree A)
    (hn : (leaves (.node l r)).Nodup) : Disjoint (cellSet l) (cellSet r) := by
  apply Finset.disjoint_left.mpr
  intro a hal har
  exact (List.disjoint_of_nodup_append hn) ((mem_cellSet a l).mp hal)
    ((mem_cellSet a r).mp har)

theorem cellClade_left_of_subset {A : Type u} [DecidableEq A] {C : Finset A}
    {l r : BTree A} (hn : (leaves (.node l r)).Nodup)
    (hc : CellClade C (.node l r)) (hs : C ⊆ cellSet l) : CellClade C l := by
  have hd := Finset.disjoint_left.mp (node_cellSets_disjoint l r hn)
  rcases (cellClade_node_iff C l r).mp hc with he | hl | hr
  · obtain ⟨a, ha⟩ := cellSet_nonempty r
    have hac : a ∈ C := by rw [he]; exact Finset.mem_union.mpr (Or.inr ha)
    exact (hd (hs hac) ha).elim
  · exact hl
  · obtain ⟨a, ha⟩ := CellClade.nonempty hr
    exact (hd (hs ha) (CellClade.subset hr ha)).elim

theorem cellClade_right_of_subset {A : Type u} [DecidableEq A] {C : Finset A}
    {l r : BTree A} (hn : (leaves (.node l r)).Nodup)
    (hc : CellClade C (.node l r)) (hs : C ⊆ cellSet r) : CellClade C r := by
  have hd := Finset.disjoint_left.mp (node_cellSets_disjoint l r hn)
  rcases (cellClade_node_iff C l r).mp hc with he | hl | hr
  · obtain ⟨a, ha⟩ := cellSet_nonempty l
    have hac : a ∈ C := by rw [he]; exact Finset.mem_union.mpr (Or.inl ha)
    exact (hd ha (hs hac)).elim
  · obtain ⟨a, ha⟩ := CellClade.nonempty hl
    exact (hd (CellClade.subset hl ha) (hs ha)).elim
  · exact hr

theorem disjoint_left_ne_union {A : Type u} [DecidableEq A] {B C : Finset A}
    (hd : Disjoint B C) (hne : C.Nonempty) : B ≠ B ∪ C := by
  intro he
  obtain ⟨a, ha⟩ := hne
  have hb : a ∈ B := by rw [he]; exact Finset.mem_union.mpr (Or.inr ha)
  exact Finset.disjoint_left.mp hd hb ha

theorem partition_eq_of_subsets {A : Type u} [DecidableEq A] {B C D E : Finset A}
    (hB : B ⊆ D) (hC : C ⊆ E) (hu : B ∪ C = D ∪ E) (hd : Disjoint D E) :
    B = D ∧ C = E := by
  have hdis := Finset.disjoint_left.mp hd
  constructor
  · apply Finset.Subset.antisymm hB
    intro a ha
    have hmem : a ∈ B ∪ C := by rw [hu]; exact Finset.mem_union.mpr (Or.inl ha)
    rcases Finset.mem_union.mp hmem with hb | hc
    · exact hb
    · exact (hdis ha (hC hc)).elim
  · apply Finset.Subset.antisymm hC
    intro a ha
    have hmem : a ∈ B ∪ C := by rw [hu]; exact Finset.mem_union.mpr (Or.inr ha)
    rcases Finset.mem_union.mp hmem with hb | hc
    · exact (hdis (hB hb) ha).elim
    · exact hc

theorem two_parts_not_one_side {A : Type u} [DecidableEq A] {B C D E : Finset A}
    (hB : B ⊆ D) (hC : C ⊆ D) (hu : B ∪ C = D ∪ E)
    (hd : Disjoint D E) (hne : E.Nonempty) : False := by
  obtain ⟨a, ha⟩ := hne
  have hmem : a ∈ B ∪ C := by rw [hu]; exact Finset.mem_union.mpr (Or.inr ha)
  exact Finset.disjoint_left.mp hd ((Finset.union_subset hB hC) hmem) ha

theorem binary_clade_root_partition {A : Type u} [DecidableEq A]
    {B C : Finset A} (l r : BTree A) (hn : (leaves (.node l r)).Nodup)
    (hB : CellClade B (.node l r)) (hC : CellClade C (.node l r))
    (hBn : B ≠ cellSet (.node l r)) (hCn : C ≠ cellSet (.node l r))
    (hu : B ∪ C = cellSet (.node l r)) :
    (B = cellSet l ∧ C = cellSet r) ∨ (B = cellSet r ∧ C = cellSet l) := by
  have hd := node_cellSets_disjoint l r hn
  have hb : CellClade B l ∨ CellClade B r := by
    rcases (cellClade_node_iff B l r).mp hB with he | hl | hr
    · exact (hBn he).elim
    · exact Or.inl hl
    · exact Or.inr hr
  have hc : CellClade C l ∨ CellClade C r := by
    rcases (cellClade_node_iff C l r).mp hC with he | hl | hr
    · exact (hCn he).elim
    · exact Or.inl hl
    · exact Or.inr hr
  have hu' : B ∪ C = cellSet r ∪ cellSet l :=
    hu.trans (Finset.union_comm _ _)
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · exact (two_parts_not_one_side (CellClade.subset hb) (CellClade.subset hc)
      hu hd (cellSet_nonempty r)).elim
  · exact Or.inl (partition_eq_of_subsets (CellClade.subset hb) (CellClade.subset hc) hu hd)
  · exact Or.inr (partition_eq_of_subsets (CellClade.subset hb) (CellClade.subset hc) hu' hd.symm)
  · exact (two_parts_not_one_side (CellClade.subset hb) (CellClade.subset hc)
      hu' hd.symm (cellSet_nonempty l)).elim

theorem tree_eq_leaf_of_singleton {A : Type u} [DecidableEq A]
    (T : BTree A) (a : A) (hn : (leaves T).Nodup) (hs : cellSet T = {a}) :
    T = .leaf a := by
  cases T with
  | leaf b =>
      have hb : b ∈ ({a} : Finset A) := by rw [← hs]; exact Finset.mem_singleton_self b
      have he := Finset.mem_singleton.mp hb
      rw [he]
  | node l r =>
      have hm := allInternalMixed_of_nodup id (.node l r) (by simpa using hn)
      have hc : (cellSet (.node l r)).card = 1 := by rw [hs]; exact Finset.card_singleton a
      have htwo : 2 ≤ (cellSet (.node l r)).card := hm.1
      omega

/-- Full binary same-cell refinement has no extra topology to resolve. -/
theorem binary_cellRefines_iso {A : Type u} [DecidableEq A] (R T : BTree A)
    (hnR : (leaves R).Nodup) (hnT : (leaves T).Nodup)
    (hs : cellSet R = cellSet T) (href : CellRefines R T) : TreeIso R T := by
  revert hnR hnT hs href
  induction R generalizing T with
  | leaf a =>
      intro hnR hnT hs href
      have ht := tree_eq_leaf_of_singleton T a hnT hs.symm
      rw [ht]
      exact .refl _
  | node l r ihl ihr =>
      intro hnR hnT hs href
      cases T with
      | leaf a =>
          have ht := tree_eq_leaf_of_singleton (.node l r) a hnR hs
          cases ht
      | node l' r' =>
          have hdR := node_cellSets_disjoint l r hnR
          have hlne : cellSet l ≠ cellSet (.node l' r') := by
            intro he
            exact disjoint_left_ne_union hdR (cellSet_nonempty r) (he.trans hs.symm)
          have hrne : cellSet r ≠ cellSet (.node l' r') := by
            intro he
            apply disjoint_left_ne_union hdR.symm (cellSet_nonempty l)
            exact (he.trans hs.symm).trans (Finset.union_comm _ _)
          have hp := binary_clade_root_partition l' r' hnT
            (href _ (.left (.root l))) (href _ (.right (.root r))) hlne hrne hs
          rcases hp with ⟨hl, hr⟩ | ⟨hl, hr⟩
          · have hfl : CellRefines l l' := by
              intro C hc
              apply cellClade_left_of_subset hnT (href _ (.left hc))
              rw [← hl]
              exact CellClade.subset hc
            have hfr : CellRefines r r' := by
              intro C hc
              apply cellClade_right_of_subset hnT (href _ (.right hc))
              rw [← hr]
              exact CellClade.subset hc
            exact .node (ihl (T := l') hnR.of_append_left hnT.of_append_left hl hfl)
              (ihr (T := r') hnR.of_append_right hnT.of_append_right hr hfr)
          · have hfl : CellRefines l r' := by
              intro C hc
              apply cellClade_right_of_subset hnT (href _ (.left hc))
              rw [← hl]
              exact CellClade.subset hc
            have hfr : CellRefines r l' := by
              intro C hc
              apply cellClade_left_of_subset hnT (href _ (.right hc))
              rw [← hr]
              exact CellClade.subset hc
            exact .trans
              (.node (ihl (T := r') hnR.of_append_left hnT.of_append_right hl hfl)
                (ihr (T := l') hnR.of_append_right hnT.of_append_left hr hfr))
              (.swap r' l')

theorem TreeIso.leaves_perm {A : Type u} {T U : BTree A} (h : TreeIso T U) :
    (leaves T).Perm (leaves U) := by
  induction h with
  | refl t => exact List.Perm.refl _
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | node hl hr ihl ihr => exact ihl.append ihr
  | swap l r => exact List.perm_append_comm

theorem TreeIso.cellClade_iff {A : Type u} [DecidableEq A] {T U : BTree A}
    (h : TreeIso T U) (C : Finset A) : CellClade C T ↔ CellClade C U := by
  induction h with
  | refl t => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | node hl hr ihl ihr =>
      simp only [cellClade_node_iff, cellSet, observed, ihl, ihr,
        TreeIso.observed_eq id hl, TreeIso.observed_eq id hr]
  | swap l r =>
      simp only [cellClade_node_iff, cellSet, observed,
        Finset.union_comm (observed id l) (observed id r)]
      tauto

inductive CellSubtree {A : Type u} : BTree A → BTree A → Prop where
  | root (t : BTree A) : CellSubtree t t
  | left {U l r : BTree A} : CellSubtree U l → CellSubtree U (.node l r)
  | right {U l r : BTree A} : CellSubtree U r → CellSubtree U (.node l r)

theorem CellSubtree.subset {A : Type u} [DecidableEq A] {U T : BTree A}
    (h : CellSubtree U T) : cellSet U ⊆ cellSet T := by
  induction h with
  | root t => exact Finset.Subset.refl _
  | left h ih => exact ih.trans Finset.subset_union_left
  | right h ih => exact ih.trans Finset.subset_union_right

theorem CellSubtree.nodup {A : Type u} {U T : BTree A}
    (h : CellSubtree U T) (hn : (leaves T).Nodup) : (leaves U).Nodup := by
  revert hn
  induction h with
  | root t => exact id
  | left h ih => intro hn; exact ih hn.of_append_left
  | right h ih => intro hn; exact ih hn.of_append_right

theorem CellClade.has_subtree {A : Type u} [DecidableEq A] {C : Finset A}
    {T : BTree A} (h : CellClade C T) :
    ∃ U : BTree A, CellSubtree U T ∧ cellSet U = C := by
  induction h with
  | root t => exact ⟨t, .root t, rfl⟩
  | left h ih =>
      obtain ⟨U, hs, he⟩ := ih
      exact ⟨U, .left hs, he⟩
  | right h ih =>
      obtain ⟨U, hs, he⟩ := ih
      exact ⟨U, .right hs, he⟩

theorem cellClade_in_subtree {A : Type u} [DecidableEq A] {C : Finset A}
    {U T : BTree A} (hu : CellSubtree U T) (hn : (leaves T).Nodup)
    (hc : CellClade C T) (hs : C ⊆ cellSet U) : CellClade C U := by
  revert hn hc
  induction hu with
  | root t => intro hn hc; exact hc
  | left hu ih =>
      intro hn hc
      exact ih hn.of_append_left
        (cellClade_left_of_subset hn hc (hs.trans (CellSubtree.subset hu)))
  | right hu ih =>
      intro hn hc
      exact ih hn.of_append_right
        (cellClade_right_of_subset hn hc (hs.trans (CellSubtree.subset hu)))

def CoveredByBlocks {I : Type*} {A : Type u} [DecidableEq A]
    (blocks : I → BTree A) (T : BTree A) : Prop :=
  ∀ a ∈ cellSet T, ∃ i U, CellSubtree U T ∧ TreeIso U (blocks i) ∧ a ∈ cellSet U

/-- A whole-block subtree cover yields an actual frontier, not merely
    a collection of clades that could leave some root-to-leaf paths uncovered. -/
theorem coveredByBlocks_has_frontier {I : Type*} {A : Type u} [DecidableEq A]
    (blocks : I → BTree A) (T : BTree A) (hn : (leaves T).Nodup)
    (hc : CoveredByBlocks blocks T) : ∃ xs, BlockFrontier blocks T xs := by
  classical
  revert hn hc
  induction T with
  | leaf a =>
      intro hn hc
      obtain ⟨i, U, hu, hi, ha⟩ := hc a (Finset.mem_singleton_self a)
      cases hu with
      | root => exact ⟨[i], .iso hi (.block i)⟩
  | node l r ihl ihr =>
      intro hn hc
      by_cases hroot : ∃ i, TreeIso (.node l r) (blocks i)
      · obtain ⟨i, hi⟩ := hroot
        exact ⟨[i], .iso hi (.block i)⟩
      · have hd := Finset.disjoint_left.mp (node_cellSets_disjoint l r hn)
        have hcl : CoveredByBlocks blocks l := by
          intro a ha
          obtain ⟨i, U, hu, hi, haU⟩ := hc a (Finset.mem_union.mpr (Or.inl ha))
          cases hu with
          | root => exact (hroot ⟨i, hi⟩).elim
          | left hu => exact ⟨i, U, hu, hi, haU⟩
          | right hu => exact (hd ha (CellSubtree.subset hu haU)).elim
        have hcr : CoveredByBlocks blocks r := by
          intro a ha
          obtain ⟨i, U, hu, hi, haU⟩ := hc a (Finset.mem_union.mpr (Or.inr ha))
          cases hu with
          | root => exact (hroot ⟨i, hi⟩).elim
          | left hu => exact (hd (CellSubtree.subset hu haU) ha).elim
          | right hu => exact ⟨i, U, hu, hi, haU⟩
        obtain ⟨xs, hxs⟩ := ihl hn.of_append_left hcl
        obtain ⟨ys, hys⟩ := ihr hn.of_append_right hcr
        exact ⟨xs ++ ys, .join hxs hys⟩

theorem BlockFrontier.member_cellSet_subset {I : Type*} {A : Type u} [DecidableEq A]
    {blocks : I → BTree A} {T : BTree A} {xs : List I}
    (h : BlockFrontier blocks T xs) {i : I} (hi : i ∈ xs) :
    cellSet (blocks i) ⊆ cellSet T := by
  revert hi
  induction h with
  | block b => intro hi; simpa only [List.mem_singleton.mp hi] using (Finset.Subset.refl (cellSet (blocks b)))
  | join hl hr ihl ihr =>
      intro hi
      rcases List.mem_append.mp hi with hi | hi
      · exact (ihl hi).trans Finset.subset_union_left
      · exact (ihr hi).trans Finset.subset_union_right
  | iso he hf ih =>
      intro hi
      change cellSet (blocks i) ⊆ observed id _
      rw [TreeIso.observed_eq id he]
      exact ih hi

theorem BlockFrontier.cell_membership {I : Type*} {A : Type u} [DecidableEq A]
    {blocks : I → BTree A} {T : BTree A} {xs : List I}
    (h : BlockFrontier blocks T xs) (a : A) :
    a ∈ cellSet T ↔ ∃ i ∈ xs, a ∈ cellSet (blocks i) := by
  induction h with
  | block b => simp
  | join hl hr ihl ihr =>
      change a ∈ cellSet _ ∪ cellSet _ ↔ _
      simp only [Finset.mem_union, ihl, ihr, List.mem_append]
      aesop
  | iso he hf ih =>
      change a ∈ observed id _ ↔ _
      rw [TreeIso.observed_eq id he]
      exact ih

theorem BlockFrontier.nodup_indices {I : Type*} {A : Type u} [DecidableEq A]
    {blocks : I → BTree A} {T : BTree A} {xs : List I}
    (h : BlockFrontier blocks T xs) (hn : (leaves T).Nodup) : xs.Nodup := by
  revert hn
  induction h with
  | block b => intro hn; simp
  | join hl hr ihl ihr =>
      intro hn
      apply List.Nodup.append (ihl hn.of_append_left) (ihr hn.of_append_right)
      intro i hi hj
      obtain ⟨a, ha⟩ := cellSet_nonempty (blocks i)
      exact Finset.disjoint_left.mp (node_cellSets_disjoint _ _ hn)
        (BlockFrontier.member_cellSet_subset hl hi ha)
        (BlockFrontier.member_cellSet_subset hr hj ha)
  | iso he hf ih =>
      intro hn
      exact ih ((TreeIso.leaves_perm he).nodup_iff.mp hn)

theorem BlockFrontier.member_refines {I : Type*} {A : Type u} [DecidableEq A]
    {blocks : I → BTree A} {T : BTree A} {xs : List I}
    (h : BlockFrontier blocks T xs) {i : I} (hi : i ∈ xs) : CellRefines (blocks i) T := by
  revert hi
  induction h with
  | block b =>
      intro hi C hc
      have he : i = b := List.mem_singleton.mp hi
      simpa only [he] using hc
  | join hl hr ihl ihr =>
      intro hi C hc
      rcases List.mem_append.mp hi with hi | hi
      · exact .left (ihl hi C hc)
      · exact .right (ihr hi C hc)
  | iso he hf ih =>
      intro hi C hc
      exact (TreeIso.cellClade_iff he C).mpr (ih hi C hc)

/-- Independent standard clade-preservation predicate on a distinct-cell
    binary candidate. This is not defined by existence of a graft. -/
def StandardBlockRefinement {I : Type*} [Fintype I] [DecidableEq I]
    {A : Type u} [DecidableEq A] (blocks : I → BTree A) (T : BTree A) : Prop :=
  (leaves T).Nodup ∧
  cellSet T = Finset.univ.biUnion (fun i => cellSet (blocks i)) ∧
  ∀ i, CellRefines (blocks i) T

theorem standardBlockRefinement_has_frontier {I : Type*} [Fintype I] [DecidableEq I]
    {A : Type u} [DecidableEq A] (blocks : I → BTree A)
    (hnb : ∀ i, (leaves (blocks i)).Nodup)
    (hdb : ∀ i j, i ≠ j → Disjoint (cellSet (blocks i)) (cellSet (blocks j)))
    (T : BTree A) (hT : StandardBlockRefinement blocks T) :
    ∃ xs, xs.Perm (Finset.univ : Finset I).toList ∧ BlockFrontier blocks T xs := by
  classical
  obtain ⟨hn, hs, href⟩ := hT
  have hcover : CoveredByBlocks blocks T := by
    intro a ha
    rw [hs] at ha
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨U, hu, he⟩ := CellClade.has_subtree (href i _ (.root (blocks i)))
    have hrf : CellRefines (blocks i) U := by
      intro C hc
      apply cellClade_in_subtree hu hn (href i C hc)
      rw [he]
      exact CellClade.subset hc
    have hiso := binary_cellRefines_iso (blocks i) U (hnb i)
      (CellSubtree.nodup hu hn) he.symm hrf
    refine ⟨i, U, hu, .symm hiso, ?_⟩
    rwa [he]
  obtain ⟨xs, hxs⟩ := coveredByBlocks_has_frontier blocks T hn hcover
  have hnodup := BlockFrontier.nodup_indices hxs hn
  have hall : ∀ i : I, i ∈ xs := by
    intro i
    obtain ⟨a, ha⟩ := cellSet_nonempty (blocks i)
    have haT : a ∈ cellSet T := by
      rw [hs]
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ha⟩
    obtain ⟨j, hj, haj⟩ := (BlockFrontier.cell_membership hxs a).mp haT
    have he : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp (hdb i j hij) ha haj
    simpa only [he] using hj
  refine ⟨xs, ?_, hxs⟩
  apply List.perm_of_nodup_nodup_toFinset_eq hnodup Finset.univ.nodup_toList
  ext i
  simp [hall i]

theorem canonicalBlock_cellSets_disjoint {N m : ℕ} (D : MSSCInstance N m)
    (b c : Block m) (hbc : b ≠ c) :
    Disjoint (cellSet (canonicalBlockTree D b)) (cellSet (canonicalBlockTree D c)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hxl := (mem_cellSet x _).mp hx
  have hyl := (mem_cellSet x _).mp hy
  rw [leaves_canonicalBlockTree] at hxl hyl
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hxl
  obtain ⟨z, hz, he⟩ := List.mem_map.mp hyl
  exact hbc (congrArg Prod.fst he).symm

theorem standardCanonicalRefinement_iff_frontier {N m : ℕ}
    (D : MSSCInstance N m) (T : BTree (Cell N m)) :
    StandardBlockRefinement (canonicalBlockTree D) T ↔
      ∃ xs, xs.Perm (Finset.univ : Finset (Block m)).toList ∧
        BlockFrontier (canonicalBlockTree D) T xs := by
  constructor
  · exact standardBlockRefinement_has_frontier (canonicalBlockTree D)
      (canonicalBlockTree_cells_nodup D) (canonicalBlock_cellSets_disjoint D) T
  · rintro ⟨xs, hp, hf⟩
    obtain ⟨t, ht, hi⟩ := BlockFrontier.has_skeleton (canonicalBlockTree D) hf
    have hv : ValidJoiningTree t := by simpa only [ValidJoiningTree, ht] using hp
    have hn : (leaves T).Nodup :=
      (TreeIso.leaves_perm hi).nodup_iff.mpr (valid_canonical_graft_cells_nodup D t hv)
    have hall : ∀ b : Block m, b ∈ xs := by
      intro b
      exact hp.mem_iff.mpr (by simp)
    refine ⟨hn, ?_, ?_⟩
    · ext a
      rw [BlockFrontier.cell_membership hf a]
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨b, hb, ha⟩; exact ⟨b, ha⟩
      · rintro ⟨b, ha⟩; exact ⟨b, hall b, ha⟩
    · intro b
      exact BlockFrontier.member_refines hf (hall b)

def StandardCanonicalCartaDecision {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) : Prop :=
  ∃ L : StarLabeledTree (Cell N m) (Terminal N m),
    StandardBlockRefinement (canonicalBlockTree D) (eraseStar L) ∧
    StarFeasible Prod.snd L ∧ cartaStarScore Prod.snd lambda L ≤
      (realizedFixedCost (canonicalBlockTree D) + K - N : ℕ)

theorem standardCanonicalCartaDecision_iff_frontier {N m : ℕ}
    (D : MSSCInstance N m) (lambda : ℝ) (K : ℕ) :
    StandardCanonicalCartaDecision D lambda K ↔
      RealizedFrontierCartaDecision (canonicalBlockTree D) lambda K := by
  simp only [StandardCanonicalCartaDecision, RealizedFrontierCartaDecision,
    standardCanonicalRefinement_iff_frontier]

/-- The complete finite actual-D_lambda reduction for independently defined
    CELL-clade-preserving binary refinements of canonical fixed blocks. -/
theorem full_standard_canonical_carta_reduction {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) (hN : 0 < N) (hm : 2 ≤ m)
    (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔ StandardCanonicalCartaDecision D lambda K := by
  rw [standardCanonicalCartaDecision_iff_frontier]
  exact full_canonical_frontier_carta_reduction D lambda K hN hm hNK hKmN

/- The independent predicate above is standard cell-cluster preservation on
full binary trees. A separate graph-edge-contraction datatype and certified
machine-time/encoding interface are still not supplied. Every declaration in
this file and every imported proposal remains UNELABORATED. -/

end
end PolytomyReductionModel
