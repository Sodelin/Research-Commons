import BinaryBlob
namespace Nanuq.SmallBlob
open Nanuq.Source Nanuq.RawBlock
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Singleton original blobs have no original internal edge, by the actual DAG premise. -/
theorem singleton_no_edges (N : RootedBinary V E X) (b : N.graph.Blob)
    (v : BlobVertex N.graph b) (hall : ∀ w : BlobVertex N.graph b, w = v) :
    IsEmpty (BlobEdge N.graph b) := by
  refine ⟨fun e => ?_⟩
  have hst := (hall ((originalBlob N.graph b).source e)).trans
    (hall ((originalBlob N.graph b).target e)).symm
  exact N.graph.acyclic_no_loop N.acyclic e.val (congrArg Subtype.val hst)

theorem outdegree_le_two (N : RootedBinary V E X) (v : V) : N.graph.outDegree v ≤ 2 := by
  by_cases hr : v = N.root
  · subst v
    rw [N.root_degrees.2]
  by_cases hl : ∃ x, N.leaf x = v
  · obtain ⟨x,rfl⟩ := hl
    rw [(N.leaf_degrees x).2]
    omega
  rcases N.internal_degrees v hr (fun x hx => hl ⟨x,hx⟩) with ⟨_,ho⟩ | ⟨_,ho⟩ <;>
    rw [ho] <;> omega

theorem no_reverse (N : RootedBinary V E X) (e f : E)
    (hs : N.graph.source f = N.graph.target e)
    (ht : N.graph.target f = N.graph.source e) : False := by
  have h₁ : N.graph.DReach (N.graph.source e) (N.graph.target e) :=
    .single ⟨e,rfl,rfl⟩
  have h₂ : N.graph.DReach (N.graph.target e) (N.graph.source e) :=
    .single ⟨f,hs,ht⟩
  exact N.graph.acyclic_no_loop N.acyclic e (N.graph.dreach_antisymm N.acyclic h₁ h₂)

theorem two_vertex_orientation (N : RootedBinary V E X) (b : N.graph.Blob)
    (u v : BlobVertex N.graph b) (huv : u ≠ v)
    (hall : ∀ w : BlobVertex N.graph b, w = u ∨ w = v)
    (e f : BlobEdge N.graph b) :
    N.graph.source f.val = N.graph.source e.val ∧
      N.graph.target f.val = N.graph.target e.val := by
  let B := originalBlob N.graph b
  have hends (g : BlobEdge N.graph b) :
      (B.source g = u ∧ B.target g = v) ∨ (B.source g = v ∧ B.target g = u) := by
    have hne : B.source g ≠ B.target g := fun h =>
      N.graph.acyclic_no_loop N.acyclic g.val (congrArg Subtype.val h)
    rcases hall (B.source g) with hs | hs <;>
      rcases hall (B.target g) with ht | ht
    · exact False.elim (hne (hs.trans ht.symm))
    · exact Or.inl ⟨hs,ht⟩
    · exact Or.inr ⟨hs,ht⟩
    · exact False.elim (hne (hs.trans ht.symm))
  rcases hends e with ⟨hes,het⟩ | ⟨hes,het⟩ <;>
    rcases hends f with ⟨hfs,hft⟩ | ⟨hfs,hft⟩
  · exact ⟨congrArg Subtype.val (hfs.trans hes.symm),congrArg Subtype.val (hft.trans het.symm)⟩
  · exact False.elim (no_reverse N e.val f.val
      (congrArg Subtype.val (hfs.trans het.symm)) (congrArg Subtype.val (hft.trans hes.symm)))
  · exact False.elim (no_reverse N e.val f.val
      (congrArg Subtype.val (hfs.trans het.symm)) (congrArg Subtype.val (hft.trans hes.symm)))
  · exact ⟨congrArg Subtype.val (hfs.trans hes.symm),congrArg Subtype.val (hft.trans het.symm)⟩

/-- Exactly two ORIGINAL parallel IDs, not one simplegraph adjacency. -/
theorem two_vertex_exact_bigon (N : RootedBinary V E X) (b : N.graph.Blob)
    (u v : BlobVertex N.graph b) (huv : u ≠ v)
    (hall : ∀ w : BlobVertex N.graph b, w = u ∨ w = v) :
    ∃ e f : BlobEdge N.graph b, e ≠ f ∧
      (∀ g : BlobEdge N.graph b, g = e ∨ g = f) ∧
      N.graph.source f.val = N.graph.source e.val ∧
      N.graph.target f.val = N.graph.target e.val ∧
      N.graph.source e.val ≠ N.graph.target e.val := by
  classical
  let B := originalBlob N.graph b
  obtain ⟨e⟩ : Nonempty (BlobEdge N.graph b) := by
    rcases Relation.ReflTransGen.cases_head (original_blob_connected N.graph b u v) with heq | ⟨w,hs,_⟩
    · exact False.elim (huv heq)
    · obtain ⟨e,_,_⟩ := hs
      exact ⟨e⟩
  have hne : B.source e ≠ B.target e := fun h =>
    N.graph.acyclic_no_loop N.acyclic e.val (congrArg Subtype.val h)
  have hcross : Crosses B (fun z => z = B.source e) e := by
    intro h
    exact hne ((h.mp rfl).symm)
  obtain ⟨f,hfe,_⟩ := second_crossing B (original_blob_bridgeless N.graph b) hcross
  have hef : e ≠ f := Ne.symm hfe
  have hevf : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  have hcover : ∀ g : BlobEdge N.graph b, g = e ∨ g = f := by
    intro g
    by_contra hh
    push_neg at hh
    have hge : g.val ≠ e.val := fun h => hh.1 (Subtype.ext h)
    have hgf : g.val ≠ f.val := fun h => hh.2 (Subtype.ext h)
    let O : Finset E := Finset.univ.filter (fun q => N.graph.source q = N.graph.source e.val)
    have hsub : ({e.val,f.val,g.val} : Finset E) ⊆ O := by
      intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl | rfl
      · simp [O]
      · simp [O,(two_vertex_orientation N b u v huv hall e f).1]
      · simp [O,(two_vertex_orientation N b u v huv hall e g).1]
    have hcard := Finset.card_le_card hsub
    have hthree : ({e.val,f.val,g.val} : Finset E).card = 3 := by
      simp [hevf,Ne.symm hge,Ne.symm hgf]
    have htwo : O.card ≤ 2 := outdegree_le_two N (N.graph.source e.val)
    omega
  have hpar := two_vertex_orientation N b u v huv hall e f
  exact ⟨e,f,hef,hcover,hpar.1,hpar.2,N.graph.acyclic_no_loop N.acyclic e.val⟩
#print axioms singleton_no_edges
#print axioms two_vertex_exact_bigon
end Nanuq.SmallBlob
