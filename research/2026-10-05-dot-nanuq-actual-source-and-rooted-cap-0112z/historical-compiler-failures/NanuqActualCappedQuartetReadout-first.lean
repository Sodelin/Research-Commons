import NanuqActualCappedBlobCutReadout
import Mathlib.Tactic.FinCases

/-! Literal capped quartet readout, with actual original cut admission. -/
namespace Nanuq.Source.RootedBinary.Switching
open scoped Classical
open Nanuq.Quartet
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable {N : RootedBinary V E X} (S : N.Switching)

theorem target_card_two_of_oriented_quartet (q : Fin 4 ↪ X) (f : S.Edge)
    (hf : S.graph.IsBridge f) (i j k l : Fin 4) (hkl : k ≠ l)
    (hcover : ∀ t : Fin 4, t = i ∨ t = j ∨ t = k ∨ t = l)
    (h : S.graph.OrientedQuartet f (N.leaf (q i)) (N.leaf (q j))
      (N.leaf (q k)) (N.leaf (q l))) :
    (S.quartetSide q f (S.graph.target f)).card = 2 := by
  have hset : S.quartetSide q f (S.graph.target f) = {k,l} := by
    ext t
    constructor
    · intro ht
      have ht0 := (S.mem_quartetSide q f _ t).mp ht
      rcases hcover t with rfl | rfl | rfl | rfl
      · exact False.elim (S.graph.bridge_sides_disjoint hf h.1 ht0)
      · exact False.elim (S.graph.bridge_sides_disjoint hf h.2.1 ht0)
      · simp
      · simp
    · intro ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact (S.mem_quartetSide q f _ k).mpr h.2.2.1
      · have ht0 := Finset.mem_singleton.mp ht
        subst t
        exact (S.mem_quartetSide q f _ l).mpr h.2.2.2
  rw [hset]
  simp [hkl]

theorem capped_oriented_quartet_iff_original (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b) (f : S.InternalBlobEdge b)
    (i j k l : Fin 4) :
    (S.actualCappedBlobGraph b).OrientedQuartet (Sum.inl f)
      (Sum.inr (N.blobProjection b hb (q i))) (Sum.inr (N.blobProjection b hb (q j)))
      (Sum.inr (N.blobProjection b hb (q k))) (Sum.inr (N.blobProjection b hb (q l))) ↔
      S.graph.OrientedQuartet f.val (N.leaf (q i)) (N.leaf (q j))
        (N.leaf (q k)) (N.leaf (q l)) := by
  simp only [EdgeGraph.OrientedQuartet]
  rw [S.actual_capped_cut_source_taxon_side_iff b hb f _ (q i) rfl,
    S.actual_capped_cut_source_taxon_side_iff b hb f _ (q j) rfl,
    S.actual_capped_cut_target_taxon_side_iff b hb f _ (q k) rfl,
    S.actual_capped_cut_target_taxon_side_iff b hb f _ (q l) rfl]

theorem original_oriented_quartet_caps (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (f : S.Edge) (hf : S.graph.IsBridge f) (i j k l : Fin 4) (hkl : k ≠ l)
    (hcover : ∀ t : Fin 4, t = i ∨ t = j ∨ t = k ∨ t = l)
    (h : S.graph.OrientedQuartet f (N.leaf (q i)) (N.leaf (q j))
      (N.leaf (q k)) (N.leaf (q l))) :
    ∃ g : S.InternalBlobEdge b, g.val = f ∧
      (S.actualCappedBlobGraph b).IsBridge (Sum.inl g) ∧
      (S.actualCappedBlobGraph b).OrientedQuartet (Sum.inl g)
        (Sum.inr (N.blobProjection b hb (q i))) (Sum.inr (N.blobProjection b hb (q j)))
        (Sum.inr (N.blobProjection b hb (q k))) (Sum.inr (N.blobProjection b hb (q l))) := by
  have hcut := S.target_card_two_of_oriented_quartet q f hf i j k l hkl hcover h
  have hi := S.original_two_two_cut_internal_to_blob q b hb hinj f hcut
  exact ⟨⟨f,hi⟩,rfl,S.capped_internal_edge_is_bridge b ⟨f,hi⟩,
    (S.capped_oriented_quartet_iff_original q b hb ⟨f,hi⟩ i j k l).mpr h⟩

theorem actual_capped_resolves_of_original (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (r : Resolution) (h : S.graph.Resolves (fun i => N.leaf (q i)) r) :
    (S.actualCappedBlobGraph b).Resolves
      (fun i => Sum.inr (N.blobProjection b hb (q i))) r := by
  cases r
  · obtain ⟨f,hf,h | h⟩ := h
    · obtain ⟨g,_,hg,hgq⟩ := S.original_oriented_quartet_caps q b hb hinj
        f hf 0 1 2 3 (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨Sum.inl g,hg,Or.inl hgq⟩
    · obtain ⟨g,_,hg,hgq⟩ := S.original_oriented_quartet_caps q b hb hinj
        f hf 2 3 0 1 (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨Sum.inl g,hg,Or.inr hgq⟩
  · obtain ⟨f,hf,h | h⟩ := h
    · obtain ⟨g,_,hg,hgq⟩ := S.original_oriented_quartet_caps q b hb hinj
        f hf 0 2 1 3 (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨Sum.inl g,hg,Or.inl hgq⟩
    · obtain ⟨g,_,hg,hgq⟩ := S.original_oriented_quartet_caps q b hb hinj
        f hf 1 3 0 2 (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨Sum.inl g,hg,Or.inr hgq⟩
  · obtain ⟨f,hf,h | h⟩ := h
    · obtain ⟨g,_,hg,hgq⟩ := S.original_oriented_quartet_caps q b hb hinj
        f hf 0 3 1 2 (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨Sum.inl g,hg,Or.inl hgq⟩
    · obtain ⟨g,_,hg,hgq⟩ := S.original_oriented_quartet_caps q b hb hinj
        f hf 1 2 0 3 (by decide) (by intro t; fin_cases t <;> simp) h
      exact ⟨Sum.inl g,hg,Or.inr hgq⟩

theorem capped_port_target_walk_constant (b : N.graph.Blob) (p : N.BlobPort b)
    {v : N.CappedBlobVertex b}
    (h : (S.actualCappedBlobGraph b).ReachWithout (Sum.inr p) (Sum.inr p) v) :
    v = Sum.inr p := by
  induction h with
  | refl => rfl
  | @tail v w hp hstep ih =>
    obtain ⟨g,hg,hinc⟩ := hstep
    cases g with
    | inl f =>
      rcases hinc with ⟨hs,_⟩ | ⟨_,ht⟩
      · rw [ih] at hs
        cases hs
      · rw [ih] at ht
        cases ht
    | inr q =>
      rcases hinc with ⟨hs,_⟩ | ⟨_,ht⟩
      · rw [ih] at hs
        cases hs
      · have hqp : q = p := Sum.inr.inj (ht.trans ih)
        exact False.elim (hg (congrArg Sum.inr hqp))

theorem capped_port_oriented_quartet_false (b : N.graph.Blob)
    (p a c d e : N.BlobPort b) (hde : d ≠ e)
    (h : (S.actualCappedBlobGraph b).OrientedQuartet (Sum.inr p)
      (Sum.inr a) (Sum.inr c) (Sum.inr d) (Sum.inr e)) : False := by
  have hd := S.capped_port_target_walk_constant b p h.2.2.1
  have he := S.capped_port_target_walk_constant b p h.2.2.2
  exact hde (Sum.inr.inj (hd.trans he.symm))

theorem actual_original_resolves_of_cap (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i)))
    (r : Resolution) (h : (S.actualCappedBlobGraph b).Resolves
      (fun i => Sum.inr (N.blobProjection b hb (q i))) r) :
    S.graph.Resolves (fun i => N.leaf (q i)) r := by
  cases r
  · obtain ⟨g,_,h | h⟩ := h
    · cases g with
      | inl f =>
        exact ⟨f.val,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val,
          Or.inl ((S.capped_oriented_quartet_iff_original q b hb f 0 1 2 3).mp h)⟩
      | inr p =>
        exact False.elim (S.capped_port_oriented_quartet_false b p _ _ _ _
          (fun heq => (by decide : (2 : Fin 4) ≠ 3) (hinj heq)) h)
    · cases g with
      | inl f =>
        exact ⟨f.val,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val,
          Or.inr ((S.capped_oriented_quartet_iff_original q b hb f 2 3 0 1).mp h)⟩
      | inr p =>
        exact False.elim (S.capped_port_oriented_quartet_false b p _ _ _ _
          (fun heq => (by decide : (0 : Fin 4) ≠ 1) (hinj heq)) h)
  · obtain ⟨g,_,h | h⟩ := h
    · cases g with
      | inl f =>
        exact ⟨f.val,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val,
          Or.inl ((S.capped_oriented_quartet_iff_original q b hb f 0 2 1 3).mp h)⟩
      | inr p =>
        exact False.elim (S.capped_port_oriented_quartet_false b p _ _ _ _
          (fun heq => (by decide : (1 : Fin 4) ≠ 3) (hinj heq)) h)
    · cases g with
      | inl f =>
        exact ⟨f.val,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val,
          Or.inr ((S.capped_oriented_quartet_iff_original q b hb f 1 3 0 2).mp h)⟩
      | inr p =>
        exact False.elim (S.capped_port_oriented_quartet_false b p _ _ _ _
          (fun heq => (by decide : (0 : Fin 4) ≠ 2) (hinj heq)) h)
  · obtain ⟨g,_,h | h⟩ := h
    · cases g with
      | inl f =>
        exact ⟨f.val,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val,
          Or.inl ((S.capped_oriented_quartet_iff_original q b hb f 0 3 1 2).mp h)⟩
      | inr p =>
        exact False.elim (S.capped_port_oriented_quartet_false b p _ _ _ _
          (fun heq => (by decide : (1 : Fin 4) ≠ 2) (hinj heq)) h)
    · cases g with
      | inl f =>
        exact ⟨f.val,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f.val,
          Or.inr ((S.capped_oriented_quartet_iff_original q b hb f 1 2 0 3).mp h)⟩
      | inr p =>
        exact False.elim (S.capped_port_oriented_quartet_false b p _ _ _ _
          (fun heq => (by decide : (0 : Fin 4) ≠ 3) (hinj heq)) h)

theorem actual_capped_quartet_resolution_iff (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hinj : Function.Injective (fun i => N.blobProjection b hb (q i))) (r : Resolution) :
    (S.actualCappedBlobGraph b).Resolves
      (fun i => Sum.inr (N.blobProjection b hb (q i))) r ↔ r = S.resolve q := by
  rw [← S.resolves_iff_eq_resolve q r]
  exact ⟨S.actual_original_resolves_of_cap q b hb hinj r,
    S.actual_capped_resolves_of_original q b hb hinj r⟩
end Nanuq.Source.RootedBinary.Switching

#print axioms Nanuq.Source.RootedBinary.Switching.actual_capped_quartet_resolution_iff
