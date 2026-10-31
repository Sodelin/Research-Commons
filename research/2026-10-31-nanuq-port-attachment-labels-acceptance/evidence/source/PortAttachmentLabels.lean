import OriginalBlob
import NanuqActualPortCardinality

set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.PortAttachmentLabels
open Nanuq.Source Nanuq.RawBlock Set
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (b : N.graph.Blob)

/-- Every vertex of a nontrivial raw blob has TWO DISTINCT original nonbridge
IDs incident to it. This follows from actual raw connectivity and detours,
not from a simplegraph degree convention or a geometric cycle premise. -/
theorem two_raw_incident_ids
    (hnt : ∃ u v : BlobVertex N.graph b, u ≠ v) (v : BlobVertex N.graph b) :
    ∃ e f : BlobEdge N.graph b, e ≠ f ∧
      (N.graph.source e.val=v.val ∨ N.graph.target e.val=v.val) ∧
      (N.graph.source f.val=v.val ∨ N.graph.target f.val=v.val) := by
  classical
  let B := originalBlob N.graph b
  obtain ⟨u,w,huw⟩ := hnt
  obtain ⟨w,hvw⟩ : ∃ w : BlobVertex N.graph b, v ≠ w := by
    by_cases hvu : v=u
    · exact ⟨w,fun h => huw (hvu.symm.trans h)⟩
    · exact ⟨u,hvu⟩
  obtain ⟨e,_,he⟩ := exists_crossing B (original_blob_connected N.graph b v w)
    (S := fun x => x=v) rfl (Ne.symm hvw)
  obtain ⟨f,hfe,hf⟩ := second_crossing B (original_blob_bridgeless N.graph b) he
  have hinc : ∀ g : BlobEdge N.graph b, Crosses B (fun x => x=v) g →
      N.graph.source g.val=v.val ∨ N.graph.target g.val=v.val := by
    intro g hg
    by_cases hs : B.source g=v
    · exact Or.inl (congrArg Subtype.val hs)
    · have ht : B.target g=v := by
        by_contra hn
        exact hg ⟨fun h => False.elim (hs h),fun h => False.elim (hn h)⟩
      exact Or.inr (congrArg Subtype.val ht)
  exact ⟨e,f,Ne.symm hfe,hinc e he,hinc f hf⟩

/-- The original inner attachment of a bridge port is incident to that SAME
original bridge ID. The incoming/outgoing cap tag is not a substitute ID. -/
theorem port_id_incident (p : N.BlobPort b) :
    N.graph.source p.val.val=(N.originalPortInner b p).val ∨
      N.graph.target p.val.val=(N.originalPortInner b p).val := by
  by_cases hp : N.graph.bridgeQuotient.source p.val=b
  · exact Or.inl (N.originalPortInner_value_outgoing b p hp).symm
  · exact Or.inr (N.originalPortInner_value_incoming b p (p.property.resolve_left hp)).symm

/-- Distinct ports attach at distinct ORIGINAL raw vertices whenever the blob
is nontrivial, including the two-vertex bigon. A singleton is deliberately
excluded. No drawing, cycle, collar, permutation or order certificate is used. -/
theorem original_port_inner_injective
    (hnt : ∃ u v : BlobVertex N.graph b, u ≠ v) :
    Function.Injective (N.originalPortInner b) := by
  classical
  intro p q hpqInner
  by_contra hpq
  let v : BlobVertex N.graph b := ⟨(N.originalPortInner b p).val,(N.originalPortInner b p).property⟩
  obtain ⟨e,f,hef,he,hf⟩ := two_raw_incident_ids N b hnt v
  have hef' : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  have hpq' : p.val.val ≠ q.val.val := fun h => hpq (Subtype.ext (Subtype.ext h))
  have hep : e.val ≠ p.val.val := fun h => e.property.1 (h.symm ▸ p.val.property)
  have heq : e.val ≠ q.val.val := fun h => e.property.1 (h.symm ▸ q.val.property)
  have hfp : f.val ≠ p.val.val := fun h => f.property.1 (h.symm ▸ p.val.property)
  have hfq : f.val ≠ q.val.val := fun h => f.property.1 (h.symm ▸ q.val.property)
  have hp := port_id_incident N b p
  have hq : N.graph.source q.val.val=v.val ∨ N.graph.target q.val.val=v.val := by
    have hh := port_id_incident N b q
    have hv : (N.originalPortInner b q).val=v.val := congrArg Subtype.val hpqInner.symm
    exact hv ▸ hh
  let I : Finset E := Finset.univ.filter (fun g => N.graph.source g=v.val ∨ N.graph.target g=v.val)
  have hsub : ({e.val,f.val,p.val.val,q.val.val} : Finset E) ⊆ I := by
    intro g hg
    simp only [Finset.mem_insert,Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · simpa [I] using he
    · simpa [I] using hf
    · simpa [I,v] using hp
    · simpa [I] using hq
  have hfour : ({e.val,f.val,p.val.val,q.val.val} : Finset E).card=4 := by
    simp [hef',hep,heq,hfp,hfq,hpq']
  have hle := Finset.card_le_card hsub
  have hthree : I.card ≤ 3 := by
    have h := binary_incidence_bound N v.val
    have hset : {g | N.graph.source g=v.val ∨ N.graph.target g=v.val} = (I : Set E) := by
      ext g; simp [I]
    rw [hset,Set.ncard_coe_finset] at h
    exact h
  omega

#print axioms two_raw_incident_ids
#print axioms original_port_inner_injective
end Nanuq.PortAttachmentLabels
