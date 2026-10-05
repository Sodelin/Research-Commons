import NanuqActualRootedCapDegrees

/-! Actual raw cap directed paths and acyclicity. Every original internal
path is lifted on its literal edge IDs; cap tips are sinks and the cap root
has no incoming occurrence. No rootedness/admission field is supplied. -/
namespace Nanuq.Source.EdgeGraph
variable {A F : Type*} [Fintype F] [DecidableEq A] (G : EdgeGraph A F)

theorem no_edge_source_of_outdegree_zero {a : A} (h : G.outDegree a = 0)
    (e : F) : G.source e ≠ a := by
  classical
  intro he
  have hp : 0 < G.outDegree a :=
    Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩
  rw [h] at hp
  exact Nat.not_lt_zero _ hp

theorem no_edge_target_of_indegree_zero {a : A} (h : G.inDegree a = 0)
    (e : F) : G.target e ≠ a := by
  classical
  intro he
  have hp : 0 < G.inDegree a :=
    Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩
  rw [h] at hp
  exact Nat.not_lt_zero _ hp

theorem dreach_from_outdegree_zero_eq {a c : A} (h : G.outDegree a = 0)
    (hr : G.DReach a c) : a = c := by
  rcases Relation.ReflTransGen.cases_head hr with heq | ⟨v,⟨e,hs,_⟩,_⟩
  · exact heq
  · exact False.elim (G.no_edge_source_of_outdegree_zero h e hs)

theorem dreach_to_indegree_zero_eq {a c : A} (h : G.inDegree c = 0)
    (hr : G.DReach a c) : a = c := by
  rcases Relation.ReflTransGen.cases_tail hr with heq | ⟨v,_,e,_,ht⟩
  · exact heq
  · exact False.elim (G.no_edge_target_of_indegree_zero h e ht)
end Nanuq.Source.EdgeGraph

namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_rooted_cap_dreach_from_inner_projects (b : N.graph.Blob)
    (a : N.OriginalBlobVertex b) {z : N.RootedCapVertex b}
    (h : (N.actualRootedCapGraph b).DReach (Sum.inl a) z) :
    ∀ c : N.OriginalBlobVertex b, z = Sum.inl c → N.graph.DReach a.val c.val := by
  induction h with
  | refl =>
      intro c hc
      have heq : a = c := Sum.inl.inj hc
      subst c
      exact .refl
  | @tail u w hp hs ih =>
      intro c hc
      obtain ⟨f,hfu,hfw⟩ := hs
      rcases f with e | (p | t)
      · have ht : N.graph.target e.val = c.val :=
          congrArg Subtype.val (Sum.inl.inj (hfw.trans hc))
        exact (ih ⟨N.graph.source e.val,e.property.1⟩ hfu.symm).tail ⟨e.val,rfl,ht⟩
      · have ht : Sum.inr (Sum.inl p) = Sum.inl c := hfw.trans hc
        cases ht
      · have hr : Sum.inl a = N.actualRootedCapRoot b :=
          (N.actualRootedCapGraph b).dreach_to_indegree_zero_eq
            (N.actual_rooted_cap_root_degrees b).1 (by rw [hfu] at hp;exact hp)
        exact False.elim (t.property (N.actualRootedCapRoot_inner_implies_root_blob b a hr.symm))

theorem actual_rooted_cap_acyclic (b : N.graph.Blob) :
    (N.actualRootedCapGraph b).Acyclic := by
  intro v hv
  rcases v with a | (p | t)
  · obtain ⟨u,⟨f,hfs,hft⟩,hu⟩ := Relation.TransGen.head'_iff.mp hv
    rcases f with e | (p | t)
    · have hs : N.graph.source e.val = a.val := congrArg Subtype.val (Sum.inl.inj hfs)
      have hret := N.actual_rooted_cap_dreach_from_inner_projects b
        ⟨N.graph.target e.val,e.property.2⟩ (by rw [← hft] at hu;exact hu) a rfl
      exact N.acyclic a.val (Relation.TransGen.head' ⟨e.val,hs,rfl⟩ hret)
    · have hEq : Sum.inr (Sum.inl p) = Sum.inl a :=
        (N.actualRootedCapGraph b).dreach_from_outdegree_zero_eq
          (N.actual_rooted_cap_port_degrees b p).2 (by rw [← hft] at hu;exact hu)
      cases hEq
    · exact t.property (N.actualRootedCapRoot_inner_implies_root_blob b a hfs)
  · obtain ⟨u,⟨f,hs,_⟩,_⟩ := Relation.TransGen.head'_iff.mp hv
    exact (N.actualRootedCapGraph b).no_edge_source_of_outdegree_zero
      (N.actual_rooted_cap_port_degrees b p).2 f hs
  · obtain ⟨u,_,f,_,ht⟩ := Relation.TransGen.tail'_iff.mp hv
    have heq : N.actualRootedCapRoot b = Sum.inr (Sum.inr t) := by
      simp [actualRootedCapRoot,t.property]
    exact (N.actualRootedCapGraph b).no_edge_target_of_indegree_zero
      (N.actual_rooted_cap_root_degrees b).1 f (ht.trans heq.symm)

theorem original_blob_directed_path_lifts_cap (b : N.graph.Blob)
    (a : N.OriginalBlobVertex b) {v : V} (h : N.graph.DReach a.val v) :
    ∀ hv : N.graph.blobOf v = b,
      (N.actualRootedCapGraph b).DReach (Sum.inl a) (Sum.inl ⟨v,hv⟩) := by
  induction h with
  | refl => intro _;exact .refl
  | @tail u w hp hs ih =>
      intro hw
      have hforward : N.graph.bridgeQuotient.DReach b (N.graph.blobOf u) := by
        simpa only [a.property] using N.graph.dreach_projects_to_blobs hp
      have hback : N.graph.bridgeQuotient.DReach (N.graph.blobOf u) b := by
        simpa only [hw] using N.graph.dreach_projects_to_blobs (Relation.ReflTransGen.single hs)
      have hu : N.graph.blobOf u = b :=
        (N.graph.bridgeQuotient.dreach_antisymm N.blob_quotient_acyclic hforward hback).symm
      obtain ⟨e,he,ht⟩ := hs
      let f : N.OriginalBlobArc b := ⟨e,by rw [he];exact hu,by rw [ht];exact hw⟩
      exact (ih hu).tail ⟨Sum.inl f,
        congrArg Sum.inl (Subtype.ext he),congrArg Sum.inl (Subtype.ext ht)⟩

theorem original_rooted_cap_entry_every_switching (b : N.graph.Blob)
    (S : N.Switching) (v : N.OriginalBlobVertex b) :
    S.graph.DReach (N.originalRootedCapEntry b).val v.val := by
  by_cases hb : b = N.graph.blobOf N.root
  · simpa [originalRootedCapEntry,hb] using S.selected_rooted v.val
  · rw [N.originalRootedCapEntry_nonroot_value b hb]
    let p := N.originalIncomingBlobPort b hb
    have hside : N.graph.ReachWithout p.val.val (N.graph.target p.val.val) v.val :=
      N.graph.sameBlob_avoids_bridge p.val.property
        (Quotient.exact ((N.originalIncomingBlobPort_target b hb).trans v.property.symm))
    have hsel := (S.original_bridge_target_side_iff p.val.val p.val.property v.val).mpr hside
    exact (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic
      (S.retainedBridge p.val.val p.val.property) v.val).mp hsel

theorem actual_rooted_cap_root_reaches_entry (b : N.graph.Blob) :
    (N.actualRootedCapGraph b).DReach (N.actualRootedCapRoot b)
      (Sum.inl (N.originalRootedCapEntry b)) := by
  by_cases hb : b = N.graph.blobOf N.root
  · have heq : N.actualRootedCapRoot b = Sum.inl (N.originalRootedCapEntry b) := by
      simp [actualRootedCapRoot,originalRootedCapEntry,hb]
    rw [heq]
    exact .refl
  · exact Relation.ReflTransGen.single ⟨Sum.inr (Sum.inr ⟨(),hb⟩),rfl,rfl⟩

theorem actual_rooted_cap_rooted (b : N.graph.Blob) :
    ∀ v : N.RootedCapVertex b,
      (N.actualRootedCapGraph b).DReach (N.actualRootedCapRoot b) v := by
  have hinner (a : N.OriginalBlobVertex b) :
      (N.actualRootedCapGraph b).DReach (N.actualRootedCapRoot b) (Sum.inl a) := by
    let S : N.Switching := Classical.choice inferInstance
    have hs := N.original_rooted_cap_entry_every_switching b S a
    have ho : N.graph.DReach (N.originalRootedCapEntry b).val a.val :=
      Relation.ReflTransGen.mono (r := S.graph.DStep) (p := N.graph.DStep)
        (fun _ _ hh => S.dstep_original hh) _ _ hs
    exact (N.actual_rooted_cap_root_reaches_entry b).trans
      (N.original_blob_directed_path_lifts_cap b (N.originalRootedCapEntry b) ho a.property)
  intro v
  rcases v with a | (p | t)
  · exact hinner a
  · by_cases hp : N.graph.bridgeQuotient.source p.val = b
    · exact (hinner (N.originalPortInner b p)).tail
        ⟨Sum.inr (Sum.inl p),if_pos hp,rfl⟩
    · exact Relation.ReflTransGen.single ⟨Sum.inr (Sum.inl p),if_neg hp,rfl⟩
  · have heq : N.actualRootedCapRoot b = Sum.inr (Sum.inr t) := by
      simp [actualRootedCapRoot,t.property]
    rw [heq]
    exact .refl
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_acyclic
#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_rooted
