import G1SemidirectedSelectedRetainedCutPaths

/-! The merged former-root cut corresponds to deleting ONE original root
arc, with the other root arc collapsed to its child. This avoids both a
false dangling-root cut and a hidden additional selection assumption. -/
namespace G1SemidirectedMergedRootCutPaths
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1RootSubdivisionPlanarAdmission G1LiteralSemidirectedSwitchingTransport
open G1SemidirectedSelectedRetainedCutPaths
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def collapseDeletedFirst (N : RootedBinary V E X) (ports : RootPorts N)
    (v : V) : SuppressedVertex N := if hv : v = N.root then secondChild N ports else ⟨v,hv⟩
@[simp] lemma collapse_deleted_first_nonroot (N : RootedBinary V E X) (ports : RootPorts N)
    (v : SuppressedVertex N) : collapseDeletedFirst N ports v.val = v := by
  simp [collapseDeletedFirst,v.property]

lemma actual_original_without_root_first_collapse (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) {v w : V} (h : N.graph.UReach (OriginalWithout N S ports.first) v w) :
    (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inr ()))
      (collapseDeletedFirst N ports v) (collapseDeletedFirst N ports w) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨f,hf,hinc⟩ := hstep
    have hex : (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inr ()))
        (collapseDeletedFirst N ports (N.graph.source f)) (collapseDeletedFirst N ports (N.graph.target f)) := by
      rcases actual_original_edge_cases N ports f with hfirst | hsecond | hn
      · exact False.elim (hf.2 hfirst)
      · subst f
        have ht := collapse_deleted_first_nonroot N ports (secondChild N ports)
        change collapseDeletedFirst N ports (N.graph.target ports.second) = secondChild N ports at ht
        rw [ports.source_second,ht]
        simp only [collapseDeletedFirst,dif_pos rfl]
        exact .refl
      · have hs := collapse_deleted_first_nonroot N ports (keptSource N ⟨f,hn⟩)
        have ht := collapse_deleted_first_nonroot N ports (keptTarget N ⟨f,hn⟩)
        change collapseDeletedFirst N ports (N.graph.source f) = keptSource N ⟨f,hn⟩ at hs
        change collapseDeletedFirst N ports (N.graph.target f) = keptTarget N ⟨f,hn⟩ at ht
        rw [hs,ht]
        exact (suppressedGraph N ports).ureach_single ⟨.inl ⟨f,hn⟩,⟨hf.1,by simp⟩,Or.inl ⟨rfl,rfl⟩⟩
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [hs,ht] at hex; exact ih.trans hex
    · rw [hs,ht] at hex; exact ih.trans ((suppressedGraph N ports).ureach_symm hex)

lemma actual_suppressed_without_merged_expansion (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) {v w : SuppressedVertex N}
    (h : (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inr ())) v w) :
    N.graph.UReach (OriginalWithout N S ports.first) v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨f,hf,hinc⟩ := hstep
    have hex : N.graph.UReach (OriginalWithout N S ports.first)
        ((suppressedGraph N ports).source f).val ((suppressedGraph N ports).target f).val := by
      cases f with
      | inl f =>
        have hn : f.val ≠ ports.first := fun he => f.property (he ▸ ports.source_first)
        exact N.graph.ureach_single ⟨f.val,⟨hf.1,hn⟩,N.graph.inc_source_target f.val⟩
      | inr f => cases f; exact False.elim (hf.2 rfl)
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [hs,ht] at hex; exact ih.trans hex
    · rw [hs,ht] at hex; exact ih.trans (N.graph.ureach_symm hex)

/-- Actual cut paths of the merged edge, including its first-endpoint side,
are exactly those of the original first root arc after deleting that arc. -/
theorem actual_merged_root_cut_path_iff (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (v w : SuppressedVertex N) :
    (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inr ())) v w ↔
      N.graph.UReach (OriginalWithout N S ports.first) v.val w.val := by
  constructor
  · exact actual_suppressed_without_merged_expansion N ports S
  · intro h
    simpa only [collapse_deleted_first_nonroot] using actual_original_without_root_first_collapse N ports S h

#print axioms actual_merged_root_cut_path_iff
end G1SemidirectedMergedRootCutPaths
