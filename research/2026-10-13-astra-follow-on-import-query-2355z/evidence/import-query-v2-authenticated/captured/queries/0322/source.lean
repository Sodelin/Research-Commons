import G1OriginalSpanCalendarDecomposition

/-! Original registered atom rows and complete selected-population support.
Contributor: dot, 2026-10-03. No desired source law is an admission premise. -/
namespace G1OriginalSpanAtomAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G2 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open G1OriginalDecoratedSpan G1OriginalSpanCalendarDecomposition G1OriginalCalendarDecomposition
open G1OriginalNodeBatchBinding G1CanonicalEpochSpecialization G1CanonicalEpochBlockBinding
open G1OriginalComponentNodeIdentity G1CompactComponentBlockRows G1NonrootBigonKernel
open G1ActualTwoPortBlob G1ExtractedComponentProgram
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

lemma actual_registered_bigon_node (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : V → unitInterval) (common : V → Bool) (B : NonrootBigon N)
    (hp : B.parents = H.parents ⟨B.parents.hybrid,B.parents.isHybrid⟩) :
    originalNodeOperation N H (fun h => gamma h.val) (fun h => common h.val) B.parents.hybrid =
      bigonPulse N B (gamma B.parents.hybrid) (common B.parents.hybrid) := by
  have hr : B.parents.hybrid ≠ N.root := by
    rw [← B.parents.target0]; exact N.edge_target_ne_root _
  simp only [originalNodeOperation,dif_neg hr,dif_pos B.parents.isHybrid,bigonPulse]
  rw [← hp]

lemma actual_bigon_incoming_pair (N : RootedBinary V E X) (B : NonrootBigon N) :
    incomingEdges N B.parents.hybrid = {B.parents.parent0,B.parents.parent1} := by
  ext e
  simp only [incomingEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro he
    exact edge_pair_exhaustive _ _ _ B.parents.different
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,B.parents.target0⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,B.parents.target1⟩) B.parents.isHybrid.1 e
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  · rintro (rfl | rfl)
    · exact B.parents.target0
    · exact B.parents.target1

lemma actual_registered_bigon_source (N : RootedBinary V E X) (B : NonrootBigon N) :
    ∀ e ∈ incomingEdges N B.parents.hybrid, N.graph.source e = B.upper := by
  intro e he
  rcases (by simpa only [actual_bigon_incoming_pair N B,Finset.mem_insert,Finset.mem_singleton] using he :
    e = B.parents.parent0 ∨ e = B.parents.parent1) with rfl | rfl
  · exact B.arm_sources false
  · exact B.arm_sources true

lemma actual_registered_bigon_canonical_cover (N : RootedBinary V E X) (B : NonrootBigon N) :
    ∀ e ∈ incomingEdges N B.parents.hybrid, e ∈ [B.parents.parent0,B.parents.parent1] := by
  intro e he
  simpa only [actual_bigon_incoming_pair N B,Finset.mem_insert,Finset.mem_singleton,
    List.mem_cons,List.not_mem_nil,or_false] using he

/-- Complete original hybrid atom row at its actual original date interval. -/
theorem actual_original_bigon_span_atom_row (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : V → unitInterval) (common : V → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (B : NonrootBigon N) (hp : B.parents = H.parents ⟨B.parents.hybrid,B.parents.isHybrid⟩)
    (s : Code N sample) (hs : AtNodePanel (state s) keep B.parents.hybrid) :
    (sourceProgram N r (fullSpanAgenda N C H gamma common B.parents.hybrid B.upper) s).map (projection N keep) =
      (sourceProgram N r (bigonProgram N C B (gamma B.parents.hybrid) (common B.parents.hybrid)) s).map
        (projection N keep) := by
  have hr : B.parents.hybrid ≠ N.root := by
    rw [← B.parents.target0]; exact N.edge_target_ne_root _
  have hh := actual_canonical_epoch_block_binding N C H (fun h => gamma h.val) (fun h => common h.val) r keep
    _ _ hr (actual_span_dates_strict N C (.bigon B)) (actual_registered_bigon_source N B) _ _
    (actual_original_exits_cover N C _ _ (actual_registered_bigon_source N B))
    (actual_registered_bigon_canonical_cover N B) s hs
  simpa only [fullSpanAgenda,actual_registered_bigon_node N H gamma common B hp,
    List.map_cons,List.map_nil,List.cons_append,List.nil_append,bigonProgram,bigonDuration] using hh

theorem actual_original_bigon_span_atom_exit (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : V → unitInterval) (common : V → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (C : Calendar N.graph)
    (B : NonrootBigon N) (hp : B.parents = H.parents ⟨B.parents.hybrid,B.parents.isHybrid⟩)
    (s : Code N sample) (hs : AtNodePanel (state s) keep B.parents.hybrid)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (bigonProgram N C B (gamma B.parents.hybrid) (common B.parents.hybrid)) s).support) :
    AtNodePanel (state d) keep B.upper := by
  have hr : B.parents.hybrid ≠ N.root := by
    rw [← B.parents.target0]; exact N.edge_target_ne_root _
  apply actual_compact_epoch_block_exit_support N H (fun h => gamma h.val) (fun h => common h.val) r keep
    B.parents.hybrid B.upper hr (bigonDuration N C B) [B.parents.parent0,B.parents.parent1]
    (actual_registered_bigon_source N B) (actual_registered_bigon_canonical_cover N B) s hs
  simpa only [actual_registered_bigon_node N H gamma common B hp,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,bigonProgram] using hd

theorem actual_original_edge_span_atom_exit (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : V → unitInterval) (common : V → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (C : Calendar N.graph)
    (e : E) (degree : N.graph.inDegree (N.graph.target e) = 1)
    (s : Code N sample) (hs : AtNodePanel (state s) keep (N.graph.target e))
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (edgeProgram N C e degree) s).support) :
    AtNodePanel (state d) keep (N.graph.source e) := by
  have hin := actual_single_incoming_edges N e degree
  have hsource : ∀ f ∈ incomingEdges N (N.graph.target e), N.graph.source f = N.graph.source e := by
    intro f hf
    have he : f = e := by simpa only [hin,Finset.mem_singleton] using hf
    subst f; rfl
  have hcover : ∀ f ∈ incomingEdges N (N.graph.target e), f ∈ [e] := by
    intro f hf
    simpa only [hin,Finset.mem_singleton,List.mem_singleton] using hf
  apply actual_compact_epoch_block_exit_support N H (fun h => gamma h.val) (fun h => common h.val) r keep
    (N.graph.target e) (N.graph.source e) (N.edge_target_ne_root e) (edgeDuration N C e) [e]
    hsource hcover s hs
  simpa only [actual_original_ordinary_edge_identity N H (fun h => gamma h.val) (fun h => common h.val) e degree,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append,edgeProgram] using hd

end G1OriginalSpanAtomAdmission
