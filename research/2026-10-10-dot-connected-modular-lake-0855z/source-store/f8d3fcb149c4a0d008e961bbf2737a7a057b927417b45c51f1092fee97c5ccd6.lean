import G1CanonicalEpochSpecialization

/-! Actual original canonical block rows equal compact original edge/bigon
words. Contributor: dot, 2026-10-03. Parent alignment is derived from registry. -/
namespace G1CompactComponentBlockRows
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open G1CanonicalEpochBlockBinding G1OriginalCalendarDecomposition
open G1OriginalNodeBatchBinding G1CanonicalEpochSpecialization G1OriginalComponentNodeIdentity
open G1ExtractedComponentProgram G1NonrootBigonKernel G1OriginalRegistryBigon
open G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_canonical_ordinary_block_row (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (e : E) (degree : N.graph.inDegree (N.graph.target e) = 1) (es : List E) (he : e ∈ es)
    (s : Code N sample) (hs : AtNodePanel (state s) keep (N.graph.target e)) :
    (sourceProgram N r (canonicalEpochBlock N C H gamma common (N.graph.target e) (N.graph.source e) es) s).map
      (projection N keep) = (sourceProgram N r (edgeProgram N C e degree) s).map (projection N keep) := by
  have hi := actual_single_incoming_edges N e degree
  have hsource : ∀ f ∈ incomingEdges N (N.graph.target e), N.graph.source f = N.graph.source e := by
    intro f hf
    have hfe : f = e := by simpa only [hi,Finset.mem_singleton] using hf
    subst f; rfl
  have hcover : ∀ f ∈ incomingEdges N (N.graph.target e), f ∈ es := by
    intro f hf
    have hfe : f = e := by simpa only [hi,Finset.mem_singleton] using hf
    subst f; exact he
  have hcanonical : ∀ f ∈ incomingEdges N (N.graph.target e), f ∈ [e] := by
    intro f hf
    simpa only [hi,Finset.mem_singleton,List.mem_singleton] using hf
  have hh := actual_canonical_epoch_block_binding N C H gamma common r keep
    (N.graph.target e) (N.graph.source e) (N.edge_target_ne_root e) (C.edge_older e)
    hsource es [e] hcover hcanonical s hs
  simpa only [actual_original_ordinary_edge_identity N H gamma common e degree,
    List.map_singleton,List.cons_append,List.nil_append,edgeProgram,edgeDuration] using hh

lemma actual_aligned_hybrid_identity (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    let B := registryAlignedBigon N hc b A H
    originalNodeOperation N H gamma common B.fragment.parents.hybrid =
      bigonPulse N B.fragment (gamma (originalHybrid N b B)) (common (originalHybrid N b B)) := by
  dsimp only
  have hsite : (registryAlignedBigon N hc b A H).fragment.parents.hybrid = A.fragment.parents.hybrid :=
    H.original_site _
  have hhy : originalHybrid N b (registryAlignedBigon N hc b A H) = originalHybrid N b A :=
    Subtype.ext hsite
  rw [hsite,hhy]
  exact actual_original_hybrid_pulse_identity N hc b A H gamma common

theorem actual_canonical_aligned_bigon_block_row (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) :
    let B := registryAlignedBigon N hc b A H
    AtNodePanel (state s) keep B.fragment.parents.hybrid →
    (sourceProgram N r (canonicalEpochBlock N C H gamma common B.fragment.parents.hybrid B.fragment.upper
      (originalExits N C (C.age B.fragment.upper))) s).map (projection N keep) =
      (sourceProgram N r (bigonProgram N C B.fragment
        (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s).map (projection N keep) := by
  dsimp only
  let B := registryAlignedBigon N hc b A H
  intro hs
  have hr : B.fragment.parents.hybrid ≠ N.root := by
    rw [← B.fragment.parents.target0]
    exact N.edge_target_ne_root _
  have hdate : C.age B.fragment.parents.hybrid < C.age B.fragment.upper := by
    simpa only [B.fragment.parents.target0,
      show N.graph.source B.fragment.parents.parent0 = B.fragment.upper from B.fragment.arm_sources false]
      using C.edge_older B.fragment.parents.parent0
  have hin := actual_bigon_incoming_edges N b B
  have hsource : ∀ e ∈ incomingEdges N B.fragment.parents.hybrid, N.graph.source e = B.fragment.upper := by
    intro e he
    rcases (by simpa only [hin,Finset.mem_insert,Finset.mem_singleton] using he :
      e = B.fragment.parents.parent0 ∨ e = B.fragment.parents.parent1) with rfl | rfl
    · exact B.fragment.arm_sources false
    · exact B.fragment.arm_sources true
  have hcanonical : ∀ e ∈ incomingEdges N B.fragment.parents.hybrid,
      e ∈ [B.fragment.parents.parent0,B.fragment.parents.parent1] := by
    intro e he
    simpa only [hin,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using he
  have hh := actual_canonical_epoch_block_binding N C H gamma common r keep _ _ hr hdate hsource _ _
    (actual_original_exits_cover N C _ _ hsource) hcanonical s hs
  have hp := actual_aligned_hybrid_identity N hc b A H gamma common
  change originalNodeOperation N H gamma common B.fragment.parents.hybrid =
    bigonPulse N B.fragment (gamma (originalHybrid N b B)) (common (originalHybrid N b B)) at hp
  simpa only [hp,List.map_cons,List.map_nil,List.cons_append,List.nil_append,bigonProgram,bigonDuration] using hh

end G1CompactComponentBlockRows
