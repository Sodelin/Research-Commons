import G1ActualRootedSwitchingPhysicalCuts

/-! Literal selected EDGE-DELETION path transport for retained edges of the
semidirected partner. The former root collapses to a selected root child;
if one hybrid root arc was deleted, no false merged edge is inserted. -/
namespace G1SemidirectedSelectedRetainedCutPaths
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1RootSubdivisionPlanarAdmission G1LiteralSemidirectedSwitchingTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def collapseSelectedRoot (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (v : V) : SuppressedVertex N :=
  if hv : v = N.root then if S.keep ports.first then firstChild N ports else secondChild N ports else ⟨v,hv⟩

@[simp] lemma collapse_nonroot (N : RootedBinary V E X) (ports : RootPorts N) (S : N.Switching)
    (v : SuppressedVertex N) : collapseSelectedRoot N ports S v.val = v := by
  simp [collapseSelectedRoot,v.property]

def OriginalWithout (N : RootedBinary V E X) (S : N.Switching) (e : E) : E → Prop :=
  fun f => S.keep f ∧ f ≠ e

def SuppressedWithout (N : RootedBinary V E X) (ports : RootPorts N) (S : N.Switching)
    (e : SuppressedEdge N) : SuppressedEdge N → Prop := fun f => suppressedKeep N ports S f ∧ f ≠ e

lemma actual_original_selected_edge_collapse (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (e : KeptEdge N) (f : E) (hf : OriginalWithout N S e.val f) :
    (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inl e))
      (collapseSelectedRoot N ports S (N.graph.source f)) (collapseSelectedRoot N ports S (N.graph.target f)) := by
  rcases actual_original_edge_cases N ports f with hfirst | hsecond | hn
  · subst f
    have ht := collapse_nonroot N ports S (firstChild N ports)
    change collapseSelectedRoot N ports S (N.graph.target ports.first) = firstChild N ports at ht
    rw [ports.source_first,ht]
    simp only [collapseSelectedRoot,dif_pos rfl,if_pos hf.1]
    exact .refl
  · subst f
    have ht := collapse_nonroot N ports S (secondChild N ports)
    change collapseSelectedRoot N ports S (N.graph.target ports.second) = secondChild N ports at ht
    rw [ports.source_second,ht]
    by_cases hk : S.keep ports.first
    · simp only [collapseSelectedRoot,dif_pos rfl,if_pos hk]
      exact (suppressedGraph N ports).ureach_single ⟨.inr (),⟨⟨hk,hf.1⟩,by simp⟩,Or.inl ⟨rfl,rfl⟩⟩
    · simp only [collapseSelectedRoot,dif_pos rfl,if_neg hk]
      exact .refl
  · have hs := collapse_nonroot N ports S (keptSource N ⟨f,hn⟩)
    have ht := collapse_nonroot N ports S (keptTarget N ⟨f,hn⟩)
    change collapseSelectedRoot N ports S (N.graph.source f) = keptSource N ⟨f,hn⟩ at hs
    change collapseSelectedRoot N ports S (N.graph.target f) = keptTarget N ⟨f,hn⟩ at ht
    rw [hs,ht]
    exact (suppressedGraph N ports).ureach_single ⟨.inl ⟨f,hn⟩,
      ⟨hf.1,fun h => hf.2 (congrArg Subtype.val (Sum.inl.inj h))⟩,Or.inl ⟨rfl,rfl⟩⟩

lemma actual_original_selected_without_collapse (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (e : KeptEdge N) {v w : V}
    (h : N.graph.UReach (OriginalWithout N S e.val) v w) :
    (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inl e))
      (collapseSelectedRoot N ports S v) (collapseSelectedRoot N ports S w) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨f,hf,hinc⟩ := hstep
    have hex := actual_original_selected_edge_collapse N ports S e f hf
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [hs,ht] at hex; exact ih.trans hex
    · rw [hs,ht] at hex; exact ih.trans ((suppressedGraph N ports).ureach_symm hex)

lemma actual_suppressed_selected_edge_expansion (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (e : KeptEdge N) (f : SuppressedEdge N)
    (hf : SuppressedWithout N ports S (.inl e) f) :
    N.graph.UReach (OriginalWithout N S e.val) ((suppressedGraph N ports).source f).val
      ((suppressedGraph N ports).target f).val := by
  cases f with
  | inl f => exact N.graph.ureach_single ⟨f.val,⟨hf.1,fun h => hf.2 (congrArg Sum.inl (Subtype.ext h))⟩,
      N.graph.inc_source_target f.val⟩
  | inr f =>
    have hfirst : ports.first ≠ e.val := fun h => e.property (h.symm ▸ ports.source_first)
    have hsecond : ports.second ≠ e.val := fun h => e.property (h.symm ▸ ports.source_second)
    have h1 : N.graph.UReach (OriginalWithout N S e.val) (N.graph.target ports.first) N.root :=
      N.graph.ureach_single ⟨ports.first,⟨hf.1.1,hfirst⟩,Or.inr ⟨ports.source_first,rfl⟩⟩
    have h2 : N.graph.UReach (OriginalWithout N S e.val) N.root (N.graph.target ports.second) :=
      N.graph.ureach_single ⟨ports.second,⟨hf.1.2,hsecond⟩,Or.inl ⟨ports.source_second,rfl⟩⟩
    exact h1.trans h2

lemma actual_suppressed_selected_without_expansion (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (e : KeptEdge N) {v w : SuppressedVertex N}
    (h : (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inl e)) v w) :
    N.graph.UReach (OriginalWithout N S e.val) v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨f,hf,hinc⟩ := hstep
    have hex := actual_suppressed_selected_edge_expansion N ports S e f hf
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [hs,ht] at hex; exact ih.trans hex
    · rw [hs,ht] at hex; exact ih.trans (N.graph.ureach_symm hex)

/-- Actual path equivalence after deleting the ONE retained edge ID, with
all selected root/hybrid choices fixed in their original switching. -/
theorem actual_retained_selected_cut_path_iff (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (e : KeptEdge N) (v w : SuppressedVertex N) :
    (suppressedGraph N ports).UReach (SuppressedWithout N ports S (.inl e)) v w ↔
      N.graph.UReach (OriginalWithout N S e.val) v.val w.val := by
  constructor
  · exact actual_suppressed_selected_without_expansion N ports S e
  · intro h
    simpa only [collapse_nonroot] using actual_original_selected_without_collapse N ports S e h

#print axioms actual_retained_selected_cut_path_iff
end G1SemidirectedSelectedRetainedCutPaths
