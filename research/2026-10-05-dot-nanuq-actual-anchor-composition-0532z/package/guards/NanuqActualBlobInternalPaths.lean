import guards.NanuqActualFourPortInvariance

set_option debug.skipKernelTC false

/-! A common original entry and physical internal selected paths. These feed
the forthcoming literal capped-blob switching restriction; they do not assume
its quartet law or the global anchor identity. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem original_blob_entry_every_switching (N : RootedBinary V E X)
    (b : N.graph.Blob) :
    ∃ r : V, N.graph.blobOf r = b ∧ ∀ S : N.Switching, ∀ v : V,
      N.graph.blobOf v = b → S.graph.DReach r v := by
  by_cases hroot : b = N.graph.blobOf N.root
  · exact ⟨N.root, hroot.symm, fun S v _ => S.selected_rooted v⟩
  · rcases Relation.ReflTransGen.cases_tail (N.blob_quotient_rooted b) with
      heq | ⟨a, _, e, hs, ht⟩
    · exact False.elim (hroot heq)
    · refine ⟨N.graph.target e.val, ht, ?_⟩
      intro S v hv
      have h0 := N.graph.sameBlob_avoids_bridge e.property
        (Quotient.exact (ht.trans hv.symm))
      have h1 := (S.original_bridge_target_side_iff e.val e.property v).mpr h0
      exact (S.graph.target_side_iff_descendant S.selected_uniqueIncoming
        S.selected_acyclic (S.retainedBridge e.val e.property) v).mp h1

namespace Switching
variable {N : RootedBinary V E X} (S : N.Switching)

theorem selected_dreach_inside_original_blob
    (b : N.graph.Blob) {a c : V}
    (ha : N.graph.blobOf a = b) (hc : N.graph.blobOf c = b)
    (h : S.graph.DReach a c) :
    S.graph.UReach (fun f => N.graph.blobOf (N.graph.source f.val) = b ∧
      N.graph.blobOf (N.graph.target f.val) = b) a c := by
  revert hc
  induction h with
  | refl => intro _; exact .refl
  | @tail v w hp hstep ih =>
    intro hw
    have hp0 : N.graph.DReach a v :=
      Relation.ReflTransGen.mono (r := S.graph.DStep) (p := N.graph.DStep)
        (fun _ _ hh => S.dstep_original hh) a v hp
    have hvw0 : N.graph.DReach v w :=
      Relation.ReflTransGen.single (S.dstep_original hstep)
    have hforward : N.graph.bridgeQuotient.DReach b (N.graph.blobOf v) := by
      simpa only [ha] using N.graph.dreach_projects_to_blobs hp0
    have hback : N.graph.bridgeQuotient.DReach (N.graph.blobOf v) b := by
      simpa only [hw] using N.graph.dreach_projects_to_blobs hvw0
    have hv : N.graph.blobOf v = b :=
      (N.graph.bridgeQuotient.dreach_antisymm N.blob_quotient_acyclic hforward hback).symm
    obtain ⟨f, hs, ht⟩ := hstep
    exact (ih hv).tail ⟨f, ⟨by change N.graph.blobOf (S.graph.source f) = b; rw [hs]; exact hv,
      by change N.graph.blobOf (S.graph.target f) = b; rw [ht]; exact hw⟩, Or.inl ⟨hs, ht⟩⟩

theorem selected_original_blob_internal_connected
    (b : N.graph.Blob) {a c : V}
    (ha : N.graph.blobOf a = b) (hc : N.graph.blobOf c = b) :
    S.graph.UReach (fun f => N.graph.blobOf (N.graph.source f.val) = b ∧
      N.graph.blobOf (N.graph.target f.val) = b) a c := by
  obtain ⟨r, hr, hentry⟩ := N.original_blob_entry_every_switching b
  exact (S.graph.ureach_symm
    (S.selected_dreach_inside_original_blob b hr ha (hentry S a ha))).trans
      (S.selected_dreach_inside_original_blob b hr hc (hentry S c hc))
end Switching
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.original_blob_entry_every_switching
#print axioms Nanuq.Source.RootedBinary.Switching.selected_original_blob_internal_connected
