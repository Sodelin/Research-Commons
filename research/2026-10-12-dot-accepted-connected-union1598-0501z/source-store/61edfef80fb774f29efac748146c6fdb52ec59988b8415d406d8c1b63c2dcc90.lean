import G1OneSameOuterSemidirectedCoreAssembly

/-! Direct cut-child admission in the literal semidirected partner.
Suppressing the former degree-two root cannot destroy ANY retained original
bridge: every alleged new detour expands through the original two root arcs.
Hence actual hybrid child cuts remain incident in the semidirected graph,
without importing a different literature definition or a desired class field. -/
namespace G1RootSuppressionCutChildTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_suppressed_edge_without_expansion (N : RootedBinary V E X) (ports : RootPorts N)
    (e : KeptEdge N) (f : SuppressedEdge N) (hf : f ≠ .inl e) :
    N.graph.ReachWithout e.val ((suppressedGraph N ports).source f).val
      ((suppressedGraph N ports).target f).val := by
  cases f with
  | inl f =>
    exact N.graph.ureach_single ⟨f.val,
      (fun h => hf (congrArg Sum.inl (Subtype.ext h))),N.graph.inc_source_target f.val⟩
  | inr f =>
    have hfirst : ports.first ≠ e.val := fun h => e.property (h.symm ▸ ports.source_first)
    have hsecond : ports.second ≠ e.val := fun h => e.property (h.symm ▸ ports.source_second)
    have h1 : N.graph.ReachWithout e.val (N.graph.target ports.first) N.root :=
      N.graph.ureach_single ⟨ports.first,hfirst,Or.inr ⟨ports.source_first,rfl⟩⟩
    have h2 : N.graph.ReachWithout e.val N.root (N.graph.target ports.second) :=
      N.graph.ureach_single ⟨ports.second,hsecond,Or.inl ⟨ports.source_second,rfl⟩⟩
    exact h1.trans h2

theorem actual_suppressed_without_expansion (N : RootedBinary V E X) (ports : RootPorts N)
    (e : KeptEdge N) {v w : SuppressedVertex N}
    (h : (suppressedGraph N ports).ReachWithout (.inl e) v w) :
    N.graph.ReachWithout e.val v.val w.val := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨f,hf,hinc⟩ := hstep
    have hex := actual_suppressed_edge_without_expansion N ports e f hf
    rcases hinc with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · rw [hs,ht] at hex
      exact ih.trans hex
    · rw [hs,ht] at hex
      exact ih.trans (N.graph.ureach_symm hex)

theorem actual_retained_original_bridge_after_root_suppression (N : RootedBinary V E X)
    (ports : RootPorts N) (e : KeptEdge N) (he : N.graph.IsBridge e.val) :
    (suppressedGraph N ports).IsBridge (.inl e) := by
  intro hdetour
  exact he (actual_suppressed_without_expansion N ports e hdetour)

lemma actual_hybrid_nonroot (N : RootedBinary V E X) (h : V) (hh : N.graph.IsHybrid h) : h ≠ N.root := by
  intro he
  have hd := hh.1
  rw [he,N.root_degrees.1] at hd
  norm_num at hd

/-- Every actual binary hybrid retains its literal original child edge ID,
now an incident cut edge in the root-suppressed semidirected multigraph.
This realizes the primary binary articulation-node galledness condition. -/
theorem actual_semidirected_hybrid_incident_child_cut (N : RootedBinary V E X)
    (hc : CutChild N) (ports : RootPorts N) (h : V) (hh : N.graph.IsHybrid h) :
    ∃ e : KeptEdge N, N.graph.source e.val = h ∧
      (suppressedGraph N ports).source (.inl e) = ⟨h,actual_hybrid_nonroot N h hh⟩ ∧
      (suppressedGraph N ports).IsBridge (.inl e) := by
  obtain ⟨e,hs,_⟩ := hybrid_child_exists_unique N h hh
  have hn : N.graph.source e ≠ N.root := fun he => actual_hybrid_nonroot N h hh (hs.symm.trans he)
  refine ⟨⟨e,hn⟩,hs,Subtype.ext hs,?_⟩
  exact actual_retained_original_bridge_after_root_suppression N ports ⟨e,hn⟩ (hc e (hs ▸ hh))

#print axioms actual_semidirected_hybrid_incident_child_cut
end G1RootSuppressionCutChildTransport
