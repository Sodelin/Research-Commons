import G1CompactSourceComposition
import G1ExtractedComponentProgram
import G1OriginalRegistryBigon

/-! Exact original-node to compact-word identity. Contributor: dot,
2026-10-03. Registry order, gamma and the SAME register coordinate are retained. -/
namespace G1OriginalComponentNodeIdentity
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open G1CutChildPorts G1ActualTwoPortBlob G1ExtractedComponentProgram G1OriginalRegistryBigon
open G1NonrootBigonKernel G1OriginalNodeBatchBinding G1BigonFootprint
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

theorem actual_original_ordinary_edge_identity (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (e : E) (degree : N.graph.inDegree (N.graph.target e) = 1) :
    originalNodeOperation N H gamma common (N.graph.target e) = .ordinary e degree := by
  have hr := N.edge_target_ne_root e
  have hh : ¬ N.graph.IsHybrid (N.graph.target e) := by
    intro hh
    have h := hh.1
    rw [degree] at h
    norm_num at h
  obtain ⟨f,_,hf⟩ := N.incoming_unique_of_indegree_one degree
  have he : (defaultSelector N).edge ⟨N.graph.target e,hr⟩ = e :=
    (hf _ ((defaultSelector N).target _)).trans (hf e rfl).symm
  simp [originalNodeOperation,hr,hh,he]

theorem actual_original_hybrid_pulse_identity (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    originalNodeOperation N H gamma common A.fragment.parents.hybrid =
      bigonPulse N (registryFragment N hc b A H)
        (gamma (originalHybrid N b A)) (common (originalHybrid N b A)) := by
  have hr : A.fragment.parents.hybrid ≠ N.root := by
    rw [← A.fragment.parents.target0]
    exact N.edge_target_ne_root _
  simp [originalNodeOperation,hr,A.fragment.parents.isHybrid,bigonPulse,registryFragment,originalHybrid]

lemma actual_single_incoming_edges (N : RootedBinary V E X) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) :
    incomingEdges N (N.graph.target e) = {e} := by
  obtain ⟨f,_,hf⟩ := N.incoming_unique_of_indegree_one degree
  ext g
  simp only [incomingEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · intro ht
    exact (hf g ht).trans (hf e rfl).symm
  · rintro rfl
    rfl

lemma actual_bigon_incoming_edges (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) :
    incomingEdges N A.fragment.parents.hybrid = {A.fragment.parents.parent0,A.fragment.parents.parent1} := by
  ext e
  simp only [incomingEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · exact actual_hybrid_parents_exhaustive N b A e
  · rintro (rfl | rfl)
    · exact A.fragment.parents.target0
    · exact A.fragment.parents.target1

end G1OriginalComponentNodeIdentity
