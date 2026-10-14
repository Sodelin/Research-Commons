import NanuqActualLocalChoiceQuartetMean
import Mathlib.Data.Fintype.Sum

/-! Literal rooted capping data: retain original internal edge occurrences,
replace bridge ports by taxon tips, and insert exactly one binary root on the
incoming port of a nonroot blob. The boundary and new-root degrees below are
derived from the original source. Full interior degree/LSA admission and the
root-suppressed readout are subsequent obligations. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem original_root_blob_has_no_incoming_port (e : N.graph.BridgeEdge) :
    N.graph.bridgeQuotient.target e ≠ N.graph.blobOf N.root := by
  intro h
  exact N.blob_quotient_acyclic (N.graph.bridgeQuotient.source e)
    (Relation.TransGen.head' ⟨e,rfl,h⟩
      (N.blob_quotient_rooted (N.graph.bridgeQuotient.source e)))

theorem original_nonroot_blob_incoming_port (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) :
    ∃ p : N.BlobPort b, N.graph.bridgeQuotient.target p.val = b := by
  rcases Relation.ReflTransGen.cases_tail (N.blob_quotient_rooted b) with
    h | ⟨a, _, e, hs, ht⟩
  · exact False.elim (hn h)
  · exact ⟨⟨e,Or.inr ht⟩,ht⟩

noncomputable def originalIncomingBlobPort (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) : N.BlobPort b :=
  Classical.choose (N.original_nonroot_blob_incoming_port b hn)

theorem originalIncomingBlobPort_target (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) :
    N.graph.bridgeQuotient.target (N.originalIncomingBlobPort b hn).val = b :=
  Classical.choose_spec (N.original_nonroot_blob_incoming_port b hn)

theorem original_incoming_port_unique (b : N.graph.Blob) (p q : N.BlobPort b)
    (hp : N.graph.bridgeQuotient.target p.val = b)
    (hq : N.graph.bridgeQuotient.target q.val = b) : p = q := by
  apply Subtype.ext
  exact N.blob_quotient_uniqueIncoming p.val q.val (hp.trans hq.symm)

noncomputable def originalRootedCapEntry (b : N.graph.Blob) : N.OriginalBlobVertex b :=
  if h : b = N.graph.blobOf N.root then ⟨N.root,h.symm⟩
  else N.originalPortInner b (N.originalIncomingBlobPort b h)

theorem originalRootedCapEntry_nonroot_value (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) :
    (N.originalRootedCapEntry b).val =
      N.graph.target (N.originalIncomingBlobPort b hn).val.val := by
  simp only [originalRootedCapEntry,dif_neg hn]
  exact N.originalPortInner_value_incoming b _ (N.originalIncomingBlobPort_target b hn)

theorem originalRootedCapEntry_nonroot_not_hybrid (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) :
    ¬ N.graph.IsHybrid (N.originalRootedCapEntry b).val := by
  rw [N.originalRootedCapEntry_nonroot_value b hn]
  exact GProgram.G6.BridgeEntry.original_bridge_target_not_hybrid N
    (N.originalIncomingBlobPort b hn).val.property

abbrev RootedCapRootTag (b : N.graph.Blob) :=
  {_u : Unit // b ≠ N.graph.blobOf N.root}
abbrev RootedCapVertex (b : N.graph.Blob) :=
  Sum (N.OriginalBlobVertex b) (Sum (N.BlobPort b) (N.RootedCapRootTag b))
abbrev RootedCapArc (b : N.graph.Blob) :=
  Sum (N.OriginalBlobArc b) (Sum (N.BlobPort b) (N.RootedCapRootTag b))

noncomputable instance rootedCapVertexFintype (b : N.graph.Blob) :
    Fintype (N.RootedCapVertex b) := by
  classical
  unfold RootedCapVertex RootedCapRootTag OriginalBlobVertex
  infer_instance

noncomputable instance rootedCapArcFintype (b : N.graph.Blob) :
    Fintype (N.RootedCapArc b) := by
  classical
  unfold RootedCapArc RootedCapRootTag OriginalBlobArc
  infer_instance

noncomputable instance rootedCapVertexDecidableEq (b : N.graph.Blob) :
    DecidableEq (N.RootedCapVertex b) := Classical.decEq _

noncomputable def actualRootedCapRoot (b : N.graph.Blob) : N.RootedCapVertex b :=
  if h : b = N.graph.blobOf N.root then Sum.inl ⟨N.root,h.symm⟩
  else Sum.inr (Sum.inr ⟨(),h⟩)

noncomputable def actualRootedCapGraph (b : N.graph.Blob) :
    EdgeGraph (N.RootedCapVertex b) (N.RootedCapArc b) where
  source := Sum.elim (fun e => Sum.inl ⟨N.graph.source e.val,e.property.1⟩)
    (Sum.elim (fun p => if N.graph.bridgeQuotient.source p.val = b then
      Sum.inl (N.originalPortInner b p) else N.actualRootedCapRoot b)
      (fun _ => N.actualRootedCapRoot b))
  target := Sum.elim (fun e => Sum.inl ⟨N.graph.target e.val,e.property.2⟩)
    (Sum.elim (fun p => Sum.inr (Sum.inl p))
      (fun _ => Sum.inl (N.originalRootedCapEntry b)))

def actualRootedCapHybridMark (b : N.graph.Blob) : N.RootedCapArc b → Prop :=
  Sum.elim (fun e => N.graph.IsHybrid (N.graph.target e.val))
    (fun _ => False)

theorem actualRootedCapRoot_ne_port_tip (b : N.graph.Blob) (p : N.BlobPort b) :
    N.actualRootedCapRoot b ≠ Sum.inr (Sum.inl p) := by
  unfold actualRootedCapRoot
  split <;> simp

theorem actual_rooted_cap_port_degrees (b : N.graph.Blob) (p : N.BlobPort b) :
    (N.actualRootedCapGraph b).inDegree (Sum.inr (Sum.inl p)) = 1 ∧
      (N.actualRootedCapGraph b).outDegree (Sum.inr (Sum.inl p)) = 0 := by
  classical
  constructor
  · apply Finset.card_eq_one_iff_existsUnique.mpr
    refine ⟨Sum.inr (Sum.inl p),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,?_⟩
    intro f hf
    have ht := (Finset.mem_filter.mp hf).2
    rcases f with e | (q | t)
    · simp [actualRootedCapGraph] at ht
    · simpa [actualRootedCapGraph] using ht
    · simp [actualRootedCapGraph] at ht
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have hs := (Finset.mem_filter.mp hf).2
    rcases f with e | (q | t)
    · simp [actualRootedCapGraph] at hs
    · by_cases hq : N.graph.bridgeQuotient.source q.val = b
      · simp [actualRootedCapGraph,hq] at hs
      · exact N.actualRootedCapRoot_ne_port_tip b p
          (by simpa [actualRootedCapGraph,hq] using hs)
    · exact N.actualRootedCapRoot_ne_port_tip b p
        (by simpa [actualRootedCapGraph] using hs)

theorem originalRootedCapIncoming_outside_source (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) :
    N.graph.bridgeQuotient.source (N.originalIncomingBlobPort b hn).val ≠ b := by
  intro h
  exact (N.graph.bridgeQuotient.bridge_endpoints_ne
    (N.graph.quotient_edge_is_bridge (N.originalIncomingBlobPort b hn).val))
      (h.trans (N.originalIncomingBlobPort_target b hn).symm)

theorem actual_rooted_cap_fresh_root_degrees (b : N.graph.Blob)
    (hn : b ≠ N.graph.blobOf N.root) :
    (N.actualRootedCapGraph b).inDegree (N.actualRootedCapRoot b) = 0 ∧
      (N.actualRootedCapGraph b).outDegree (N.actualRootedCapRoot b) = 2 := by
  classical
  constructor
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have ht := (Finset.mem_filter.mp hf).2
    rcases f with e | (p | t) <;>
      simp [actualRootedCapGraph,actualRootedCapRoot,hn] at ht
  · let pe : N.RootedCapArc b := Sum.inr (Sum.inl (N.originalIncomingBlobPort b hn))
    let re : N.RootedCapArc b := Sum.inr (Sum.inr ⟨(),hn⟩)
    have heq : Finset.univ.filter
        (fun f => (N.actualRootedCapGraph b).source f = N.actualRootedCapRoot b) =
        {pe,re} := by
      ext f
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
        Finset.mem_singleton]
      rcases f with e | (p | t)
      · simp [actualRootedCapGraph,actualRootedCapRoot,hn,pe,re]
      · by_cases hp : N.graph.bridgeQuotient.source p.val = b
        · simp [actualRootedCapGraph,hp,actualRootedCapRoot,hn,pe,re]
          intro h
          have he : p = N.originalIncomingBlobPort b hn := h
          subst p
          exact N.originalRootedCapIncoming_outside_source b hn hp
        · have ht : N.graph.bridgeQuotient.target p.val = b := p.property.resolve_left hp
          have hpi := N.original_incoming_port_unique b p (N.originalIncomingBlobPort b hn)
            ht (N.originalIncomingBlobPort_target b hn)
          have hni := N.originalRootedCapIncoming_outside_source b hn
          simp [actualRootedCapGraph,pe,re,hpi,hni]
      · have ht : t = ⟨(),hn⟩ := Subtype.ext (Subsingleton.elim _ _)
        simp [actualRootedCapGraph,pe,re,ht]
    change (Finset.univ.filter _).card = 2
    rw [heq]
    simp [pe,re]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_port_degrees
#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_fresh_root_degrees
