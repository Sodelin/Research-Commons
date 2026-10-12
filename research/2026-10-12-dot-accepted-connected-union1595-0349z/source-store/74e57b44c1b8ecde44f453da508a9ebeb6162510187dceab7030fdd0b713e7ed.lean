import NanuqActualPortCardinality

/-! Exact hybrid marks and switching equivalence for the admitted literal
rooted cap. Boundary/fresh-root arcs are ordinary. No desired quartet row,
anchor identity, geometric circularity, or global NANUQ conclusion is assumed. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_rooted_cap_inner_hybrid_iff (b : N.graph.Blob)
    (a : N.OriginalBlobVertex b) :
    (N.actualRootedCapGraph b).IsHybrid (Sum.inl a) ↔ N.graph.IsHybrid a.val := by
  unfold EdgeGraph.IsHybrid
  rw [(N.actual_rooted_cap_inner_degrees b a).1,
    (N.actual_rooted_cap_inner_degrees b a).2]

theorem actual_rooted_cap_hybrid_vertex (b : N.graph.Blob)
    (v : N.RootedCapVertex b) (hv : (N.actualRootedCapGraph b).IsHybrid v) :
    ∃ a : N.OriginalBlobVertex b, v = Sum.inl a ∧ N.graph.IsHybrid a.val := by
  rcases v with a | (p | t)
  · exact ⟨a,rfl,(N.actual_rooted_cap_inner_hybrid_iff b a).mp hv⟩
  · have h := (N.actual_rooted_cap_port_degrees b p).1
    have h2 := hv.1
    omega
  · have h := (N.actual_rooted_cap_fresh_root_degrees b t.property).1
    have he : N.actualRootedCapRoot b = Sum.inr (Sum.inr t) := by
      simp [actualRootedCapRoot,t.property]
    rw [he] at h
    have h2 := hv.1
    omega

theorem actual_rooted_cap_hybrid_mark_iff (b : N.graph.Blob)
    (f : N.RootedCapArc b) :
    N.actualRootedCapHybridMark b f ↔
      (N.actualRootedCapGraph b).IsHybrid ((N.actualRootedCapGraph b).target f) := by
  rcases f with e | (p | t)
  · exact (N.actual_rooted_cap_inner_hybrid_iff b
      ⟨N.graph.target e.val,e.property.2⟩).symm
  · change False ↔ (N.actualRootedCapGraph b).IsHybrid (Sum.inr (Sum.inl p))
    constructor
    · exact False.elim
    · intro h
      have h1 := (N.actual_rooted_cap_port_degrees b p).1
      have h2 := h.1
      omega
  · change False ↔ (N.actualRootedCapGraph b).IsHybrid
      (Sum.inl (N.originalRootedCapEntry b))
    rw [N.actual_rooted_cap_inner_hybrid_iff]
    exact iff_of_false id (N.originalRootedCapEntry_nonroot_not_hybrid b t.property)

theorem actual_rooted_cap_hybrid_target_internal (b : N.graph.Blob)
    (f : N.RootedCapArc b)
    (hh : (N.actualRootedCapGraph b).IsHybrid ((N.actualRootedCapGraph b).target f)) :
    ∃ e : N.OriginalBlobArc b, f = Sum.inl e := by
  have hm := (N.actual_rooted_cap_hybrid_mark_iff b f).mpr hh
  rcases f with e | u
  · exact ⟨e,rfl⟩
  · exact False.elim hm

namespace OriginalBlobSwitching
variable {N} {b : N.graph.Blob} (L : N.OriginalBlobSwitching b)

noncomputable def toActualRootedCapSwitching (hb : N.NonleafBlob b) :
    (N.actualEveryNonleafRootedCapSource b hb).Switching where
  keep := Sum.elim L.keep (fun _ => True)
  ordinary f hn := by
    rcases f with e | u
    · apply L.ordinary e
      intro hh
      exact hn ((N.actual_rooted_cap_hybrid_mark_iff b (Sum.inl e)).mp hh)
    · trivial
  hybrid_unique v hv := by
    obtain ⟨a,rfl,ha⟩ := N.actual_rooted_cap_hybrid_vertex b v hv
    obtain ⟨e,he,hk,hu⟩ := L.hybrid_unique a ha
    refine ⟨Sum.inl e,congrArg Sum.inl (Subtype.ext he),hk,?_⟩
    intro f hf hkf
    change (N.actualRootedCapGraph b).target f = Sum.inl a at hf
    obtain ⟨g,rfl⟩ := N.actual_rooted_cap_hybrid_target_internal b f (by rw [hf];exact hv)
    exact congrArg Sum.inl (hu g (congrArg Subtype.val (Sum.inl.inj hf)) hkf)
end OriginalBlobSwitching

namespace Switching
variable {N} {b : N.graph.Blob} {hb : N.NonleafBlob b}
variable (S : (N.actualEveryNonleafRootedCapSource b hb).Switching)

noncomputable def fromActualRootedCapSwitching : N.OriginalBlobSwitching b where
  keep e := S.keep (Sum.inl e)
  ordinary e hn := S.ordinary (Sum.inl e) (by
    intro hh
    exact hn ((N.actual_rooted_cap_hybrid_mark_iff b (Sum.inl e)).mpr hh))
  hybrid_unique a ha := by
    have hh : (N.actualRootedCapGraph b).IsHybrid (Sum.inl a) :=
      (N.actual_rooted_cap_inner_hybrid_iff b a).mpr ha
    obtain ⟨f,hf,hk,hu⟩ := S.hybrid_unique (Sum.inl a) hh
    change (N.actualRootedCapGraph b).target f = Sum.inl a at hf
    obtain ⟨e,rfl⟩ := N.actual_rooted_cap_hybrid_target_internal b f (by rw [hf];exact hh)
    refine ⟨e,congrArg Subtype.val (Sum.inl.inj hf),hk,?_⟩
    intro g hg hkg
    exact Sum.inl.inj (hu (Sum.inl g) (congrArg Sum.inl (Subtype.ext hg)) hkg)

theorem from_to_actual_rooted_cap_roundtrip :
    S.fromActualRootedCapSwitching.toActualRootedCapSwitching hb = S := by
  have hk : (S.fromActualRootedCapSwitching.toActualRootedCapSwitching hb).keep = S.keep := by
    funext f
    rcases f with e | u
    · rfl
    · apply propext
      change True ↔ S.keep (Sum.inr u)
      constructor
      · intro _
        apply S.ordinary
        intro hh
        exact (N.actual_rooted_cap_hybrid_mark_iff b (Sum.inr u)).mpr hh
      · intro _;trivial
  generalize hT : S.fromActualRootedCapSwitching.toActualRootedCapSwitching hb = T at hk ⊢
  cases T
  cases S
  cases hk
  rfl
end Switching

namespace OriginalBlobSwitching
variable {N} {b : N.graph.Blob} (L : N.OriginalBlobSwitching b)

theorem to_from_actual_rooted_cap_roundtrip (hb : N.NonleafBlob b) :
    (L.toActualRootedCapSwitching hb).fromActualRootedCapSwitching = L := by
  apply OriginalBlobSwitching.ext
  rfl

noncomputable def actualRootedCapSwitchingEquiv (hb : N.NonleafBlob b) :
    N.OriginalBlobSwitching b ≃ (N.actualEveryNonleafRootedCapSource b hb).Switching where
  toFun L := L.toActualRootedCapSwitching hb
  invFun S := S.fromActualRootedCapSwitching
  left_inv L := L.to_from_actual_rooted_cap_roundtrip hb
  right_inv S := S.from_to_actual_rooted_cap_roundtrip
end OriginalBlobSwitching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_rooted_cap_hybrid_mark_iff
#print axioms Nanuq.Source.RootedBinary.OriginalBlobSwitching.toActualRootedCapSwitching
#print axioms Nanuq.Source.RootedBinary.Switching.fromActualRootedCapSwitching

#print axioms Nanuq.Source.RootedBinary.OriginalBlobSwitching.actualRootedCapSwitchingEquiv
