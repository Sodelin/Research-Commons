import G1SplicedSourceAdmission
import SourceResolve

/-! Actual original one-parent switchings restrict to the constructed physical
two-port splice. No displayed-tree or target identity is a structure field.
Contributor: dot, 2026-10-03. -/
namespace G1SplicedOriginalSwitching
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SpliceDegrees G1SplicedSourceAdmission G1CutChildPorts
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_child_target_not_hybrid (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : ¬N.graph.IsHybrid (N.graph.target A.child) := by
  intro hh
  exact actual_hybrid_parent_nonbridge N A.child hh A.child_bridge

noncomputable def splicedKeep (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (S : N.Switching) : SplicedEdge N b A → Prop
  | .inl e => S.keep e.val
  | .inr _ => True

/-- Every actual original switching produces an actual switching of the
constructed admitted splice. Retained edge IDs keep their original choices. -/
noncomputable def restrictSwitching (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (S : N.Switching) : (splicedNetwork N hc b hb A).Switching where
  keep := splicedKeep N hc b A S
  ordinary := by
    intro e hn
    cases e with
    | inr u => trivial
    | inl e =>
      apply S.ordinary e.val
      intro hh
      apply hn
      exact (actual_splice_hybrid_iff N hc b A (retainedTarget N hc b A e)).mpr hh
  hybrid_unique := by
    intro v hv
    have hraw : N.graph.IsHybrid v.val := (actual_splice_hybrid_iff N hc b A v).mp hv
    obtain ⟨e,he,hkeep,hu⟩ := S.hybrid_unique v.val hraw
    have hne : e ≠ A.child := by
      intro heq
      exact actual_child_target_not_hybrid N b A (heq ▸ he.symm ▸ hraw)
    have hret := actual_in_edge_kept_of_ne_child N hc b A v e he hne
    let f : RetainedEdge N b A := ⟨e,hret⟩
    refine ⟨Sum.inl f,?_,hkeep,?_⟩
    · exact Subtype.ext he
    · intro g hg hk
      cases g with
      | inr u =>
        have ht : N.graph.target A.child = v.val := congrArg Subtype.val hg
        exact False.elim (actual_child_target_not_hybrid N b A (ht.symm ▸ hraw))
      | inl g =>
        have ht : N.graph.target g.val = v.val := congrArg Subtype.val hg
        exact congrArg Sum.inl (Subtype.ext (hu g.val ht hk))

#print axioms restrictSwitching

noncomputable def liftedKeep (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (T : (splicedNetwork N hc b hb A).Switching) (e : E) : Prop :=
  if he : e ∉ removedEdges N b A then T.keep (.inl ⟨e,he⟩)
  else e ≠ A.fragment.parents.parent1

/-- Every actual reduced switching lifts to an actual ORIGINAL switching.
The deleted hybrid is assigned one actual original arm; no tree oracle is used. -/
noncomputable def liftSwitching (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (T : (splicedNetwork N hc b hb A).Switching) : N.Switching where
  keep := liftedKeep N hc b hb A T
  ordinary := by
    intro e hn
    by_cases he : e ∉ removedEdges N b A
    · rw [liftedKeep,dif_pos he]
      apply T.ordinary (.inl ⟨e,he⟩)
      intro hh
      exact hn ((actual_splice_hybrid_iff N hc b A (retainedTarget N hc b A ⟨e,he⟩)).mp hh)
    · rw [liftedKeep,dif_neg he]
      intro heq
      subst e
      exact hn (A.fragment.parents.target1 ▸ A.fragment.parents.isHybrid)
  hybrid_unique := by
    intro v hv
    by_cases hH : v = A.fragment.parents.hybrid
    · subst v
      refine ⟨A.fragment.parents.parent0,A.fragment.parents.target0,?_,?_⟩
      · have hm : A.fragment.parents.parent0 ∈ removedEdges N b A := by simp [removedEdges]
        rw [liftedKeep,dif_neg (fun hn => hn hm)]
        exact A.fragment.parents.different
      · intro e he hk
        rcases actual_hybrid_parents_exhaustive N b A e he with he | he
        · exact he
        · subst e
          simp [liftedKeep,removedEdges] at hk
    · have hU : v ≠ A.fragment.upper := by
        intro heq
        have hd := (actual_upper_tree_degrees N hc b A).1
        have hh := hv.1
        rw [heq,hd] at hh
        omega
      let v' : SplicedVertex N b A := ⟨v,hU,hH⟩
      have hv' : (spliceGraph N hc b A).IsHybrid v' := (actual_splice_hybrid_iff N hc b A v').mpr hv
      obtain ⟨e,he,hk,hu⟩ := T.hybrid_unique v' hv'
      cases e with
      | inr u =>
        have ht : N.graph.target A.child = v := congrArg Subtype.val he
        exact False.elim (actual_child_target_not_hybrid N b A (ht.symm ▸ hv))
      | inl e =>
        have het : N.graph.target e.val = v := congrArg Subtype.val he
        refine ⟨e.val,het,?_,?_⟩
        · simpa only [liftedKeep,dif_pos e.property] using hk
        · intro f hf hfk
          have hfc : f ≠ A.child := by
            intro heq
            exact actual_child_target_not_hybrid N b A (heq ▸ hf.symm ▸ hv)
          have hret := actual_in_edge_kept_of_ne_child N hc b A v' f hf hfc
          have hkf : T.keep (.inl ⟨f,hret⟩) := by simpa only [liftedKeep,dif_pos hret] using hfk
          have htarget : (spliceGraph N hc b A).target (.inl ⟨f,hret⟩) = v' := Subtype.ext hf
          have heq := hu (.inl ⟨f,hret⟩) htarget hkf
          exact congrArg Subtype.val (Sum.inl.inj heq)

#print axioms liftSwitching

lemma switching_ext (N : RootedBinary V E X) (S T : N.Switching)
    (h : ∀ e, S.keep e ↔ T.keep e) : S = T := by
  cases S with
  | mk ks os hs =>
    cases T with
    | mk kt ot ht =>
      have hk : ks = kt := funext (fun e => propext (h e))
      subst kt
      rfl

theorem actual_restrict_lift_switching (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (T : (splicedNetwork N hc b hb A).Switching) :
    restrictSwitching N hc b hb A (liftSwitching N hc b hb A T) = T := by
  apply switching_ext
  intro e
  cases e with
  | inl e => simp only [restrictSwitching,splicedKeep,liftSwitching,liftedKeep,dif_pos e.property]
  | inr u =>
    have hk : T.keep (.inr u) := by
      apply T.ordinary
      intro hh
      exact actual_child_target_not_hybrid N b A
        ((actual_splice_hybrid_iff N hc b A (descendantInterface N b A)).mp hh)
    simp only [restrictSwitching,splicedKeep,true_iff,hk]

#print axioms actual_restrict_lift_switching
end G1SplicedOriginalSwitching
