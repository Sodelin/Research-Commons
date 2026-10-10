import G1SpliceDegrees

/-!
# Lowest-stable-ancestor preservation through the actual two-port splice

Contributor: dot, 2026-10-03. Original root-to-taxon walks avoiding a retained
vertex are projected to actual core walks avoiding that same vertex. The case
where the blocked vertex is the rootward interface is handled by the original
entering bridge; no removed vertex can then be visited. LSA is DERIVED.
-/
namespace G1SpliceLSA
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SpliceCutTransport G1SpliceRootBlob G1SpliceDegrees
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_edge_collapse_short (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : E) :
    collapseVertex N b A (N.graph.source e) = collapseVertex N b A (N.graph.target e) ∨
    (spliceGraph N hc b A).DStep (collapseVertex N b A (N.graph.source e))
      (collapseVertex N b A (N.graph.target e)) := by
  by_cases he : e ∈ removedEdges N b A
  · have he : e = A.entry ∨ e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
      simpa only [removedEdges,Finset.mem_insert,Finset.mem_singleton] using he
    rcases he with rfl | rfl | rfl | rfl
    · rw [A.entry_target,collapse_removed N b A _ (Or.inl rfl)]
      have hs := collapse_kept N b A (rootwardInterface N b A)
      change collapseVertex N b A (N.graph.source A.entry) = rootwardInterface N b A at hs
      exact Or.inl hs
    · rw [A.child_source,collapse_removed N b A _ (Or.inr rfl)]
      have ht := collapse_kept N b A (descendantInterface N b A)
      change collapseVertex N b A (N.graph.target A.child) = descendantInterface N b A at ht
      rw [ht]
      exact Or.inr ⟨Sum.inr (),rfl,rfl⟩
    · rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false,
        A.fragment.parents.target0,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact Or.inl rfl
    · rw [show N.graph.source A.fragment.parents.parent1 = A.fragment.upper from A.fragment.arm_sources true,
        A.fragment.parents.target1,collapse_removed N b A _ (Or.inl rfl),collapse_removed N b A _ (Or.inr rfl)]
      exact Or.inl rfl
  · let e' : RetainedEdge N b A := ⟨e,he⟩
    have hs := collapse_kept N b A (retainedSource N hc b A e')
    have ht := collapse_kept N b A (retainedTarget N hc b A e')
    change collapseVertex N b A (N.graph.source e) = retainedSource N hc b A e' at hs
    change collapseVertex N b A (N.graph.target e) = retainedTarget N hc b A e' at ht
    rw [hs,ht]
    exact Or.inr ⟨Sum.inl e',rfl,rfl⟩

lemma actual_collapsed_guarded_step (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (blocked : SplicedVertex N b A)
    {v w : V} (hstep : N.graph.DStep v w)
    (hv : collapseVertex N b A v ≠ blocked) (hw : collapseVertex N b A w ≠ blocked) :
    Relation.ReflTransGen
      (fun x y : SplicedVertex N b A => (spliceGraph N hc b A).DStep x y ∧ x ≠ blocked ∧ y ≠ blocked)
      (collapseVertex N b A v) (collapseVertex N b A w) := by
  obtain ⟨e,hes,het⟩ := hstep
  have hs := actual_edge_collapse_short N hc b A e
  rw [hes,het] at hs
  rcases hs with heq | hstep
  · rw [heq]
  · exact Relation.ReflTransGen.single ⟨hstep,hv,hw⟩

lemma collapse_ne_blocked_of_rootward_ne (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (blocked : SplicedVertex N b A)
    (hblocked : blocked.val ≠ N.graph.source A.entry) (v : V) (hv : v ≠ blocked.val) :
    collapseVertex N b A v ≠ blocked := by
  intro heq
  by_cases hinside : v = A.fragment.upper ∨ v = A.fragment.parents.hybrid
  · rw [collapse_removed N b A v hinside] at heq
    exact hblocked (congrArg Subtype.val heq).symm
  · rw [collapseVertex,dif_neg hinside] at heq
    exact hv (congrArg Subtype.val heq)

lemma collapse_ne_blocked_of_outside (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (blocked : SplicedVertex N b A)
    (v : V) (hv : v ≠ blocked.val) (hout : v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid) :
    collapseVertex N b A v ≠ blocked := by
  intro heq
  rw [collapseVertex,dif_neg (not_or.mpr hout)] at heq
  exact hv (congrArg Subtype.val heq)

lemma actual_source_side_excludes_removed (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (v : V)
    (hv : N.graph.ReachWithout A.entry (N.graph.source A.entry) v) :
    v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid := by
  refine ⟨?_,?_⟩
  · intro h
    apply A.entry_bridge
    rw [h] at hv
    rw [A.entry_target]
    exact hv
  · intro h
    have hp : N.graph.ReachWithout A.entry A.fragment.parents.hybrid A.fragment.upper :=
      N.graph.ureach_single ⟨A.fragment.parents.parent0,(actual_entry_parent0_distinct N b A).symm,
        Or.inr ⟨A.fragment.arm_sources false,A.fragment.parents.target0⟩⟩
    apply A.entry_bridge
    rw [A.entry_target]
    exact (h ▸ hv).trans hp

lemma actual_avoiding_projection_noninterface (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (blocked : SplicedVertex N b A)
    (hblocked : blocked.val ≠ N.graph.source A.entry) {v w : V}
    (h : N.graph.AvoidReach blocked.val v w) :
    (spliceGraph N hc b A).AvoidReach blocked (collapseVertex N b A v) (collapseVertex N b A w) := by
  rcases h with ⟨hv,hw,hp⟩
  refine ⟨collapse_ne_blocked_of_rootward_ne N b A blocked hblocked v hv,
    collapse_ne_blocked_of_rootward_ne N b A blocked hblocked w hw,?_⟩
  clear hv hw
  induction hp with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact ih.trans (actual_collapsed_guarded_step N hc b A blocked hstep.1
        (collapse_ne_blocked_of_rootward_ne N b A blocked hblocked _ hstep.2.1)
        (collapse_ne_blocked_of_rootward_ne N b A blocked hblocked _ hstep.2.2))

lemma actual_avoiding_projection_interface (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (blocked : SplicedVertex N b A)
    (hblocked : blocked.val = N.graph.source A.entry) {w : V}
    (h : N.graph.AvoidReach blocked.val N.root w) :
    (spliceGraph N hc b A).AvoidReach blocked (collapseVertex N b A N.root) (collapseVertex N b A w) := by
  have general : ∀ {z : V},
      Relation.ReflTransGen (fun x y => N.graph.DStep x y ∧ x ≠ blocked.val ∧ y ≠ blocked.val) N.root z →
      N.graph.ReachWithout A.entry (N.graph.source A.entry) z ∧
      Relation.ReflTransGen
        (fun x y : SplicedVertex N b A => (spliceGraph N hc b A).DStep x y ∧ x ≠ blocked ∧ y ≠ blocked)
        (collapseVertex N b A N.root) (collapseVertex N b A z) := by
    intro z hp
    induction hp with
    | refl => exact ⟨N.root_on_source_side A.entry,.refl⟩
    | @tail z t _ hstep ih =>
        obtain ⟨e,hes,het⟩ := hstep.1
        have he : e ≠ A.entry := by
          intro hentry
          have hz : z = blocked.val := hes.symm.trans ((congrArg N.graph.source hentry).trans hblocked.symm)
          exact hstep.2.1 hz
        have ht : N.graph.ReachWithout A.entry (N.graph.source A.entry) t :=
          ih.1.tail ⟨e,he,Or.inl ⟨hes,het⟩⟩
        have hzout := actual_source_side_excludes_removed N b A z ih.1
        have htout := actual_source_side_excludes_removed N b A t ht
        exact ⟨ht,ih.2.trans (actual_collapsed_guarded_step N hc b A blocked hstep.1
          (collapse_ne_blocked_of_outside N b A blocked z hstep.2.1 hzout)
          (collapse_ne_blocked_of_outside N b A blocked t hstep.2.2 htout))⟩
  have hz := general h.2.2
  refine ⟨collapse_ne_blocked_of_outside N b A blocked N.root h.1
    (actual_source_side_excludes_removed N b A N.root (N.root_on_source_side A.entry)),
    collapse_ne_blocked_of_outside N b A blocked w h.2.1 (actual_source_side_excludes_removed N b A w hz.1),hz.2⟩

/-- Every ORIGINAL taxon-reaching walk avoiding a retained vertex has an
actual core taxon-reaching walk avoiding that SAME retained vertex. -/
theorem actual_original_root_avoid_projects (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (blocked : SplicedVertex N b A) (x : X) (h : N.graph.AvoidReach blocked.val N.root (N.leaf x)) :
    (spliceGraph N hc b A).AvoidReach blocked (retainedRoot N b hb A) (retainedTaxa N b A x) := by
  have hp : (spliceGraph N hc b A).AvoidReach blocked
      (collapseVertex N b A N.root) (collapseVertex N b A (N.leaf x)) := by
    by_cases hi : blocked.val = N.graph.source A.entry
    · exact actual_avoiding_projection_interface N hc b A blocked hi h
    · exact actual_avoiding_projection_noninterface N hc b A blocked hi h
  have hr := collapse_kept N b A (retainedRoot N b hb A)
  have ht := collapse_kept N b A (retainedTaxa N b A x)
  change collapseVertex N b A N.root = retainedRoot N b hb A at hr
  change collapseVertex N b A (N.leaf x) = retainedTaxa N b A x at ht
  rw [hr,ht] at hp
  exact hp

/-- Actual original LSA root is preserved; the conclusion is not an input
normal-form/dominance premise. Original labels and root identity stay fixed. -/
theorem actual_splice_least_stable (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (v : SplicedVertex N b A)
    (hdom : ∀ x, (spliceGraph N hc b A).Dominates (retainedRoot N b hb A) v (retainedTaxa N b A x)) :
    v = retainedRoot N b hb A := by
  by_contra hne
  have hraw : v.val ≠ N.root := by intro h; exact hne (Subtype.ext h)
  obtain ⟨x,hx⟩ := N.exists_leaf_avoiding_of_ne_root hraw
  exact hdom x (actual_original_root_avoid_projects N hc b hb A v x hx)

end G1SpliceLSA
