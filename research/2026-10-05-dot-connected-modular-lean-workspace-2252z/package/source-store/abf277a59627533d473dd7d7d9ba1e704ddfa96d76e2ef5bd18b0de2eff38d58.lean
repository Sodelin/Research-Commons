import G1InitializedFrontierPrefix
import G1BigonFootprint

/-! Align graph extraction to the SAME supplied original parent registry.
Contributor: dot, 2026-10-03. Parent ordering is a source parameter: arbitrary
Classical extraction order may not silently reuse a nonfair gamma. This module
constructs the actual bigon with precisely the original registry's two edges. -/
namespace G1OriginalRegistryBigon
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint
open G1NonrootBigonKernel UnifiedLean.Source.NativeParentRouting
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def originalHybrid (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Hybrid N := ⟨A.fragment.parents.hybrid,A.fragment.parents.isHybrid⟩

lemma original_registry_arm_source (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N) (bit : Bool) :
    N.graph.source ((H.parents (originalHybrid N b A)).parent bit) = A.fragment.upper := by
  have ht := registry_parent_target N H (originalHybrid N b A) bit
  have he := actual_hybrid_parents_exhaustive N b A _ ht
  rcases he with he | he
  · rw [he]; exact A.fragment.arm_sources false
  · rw [he]; exact A.fragment.arm_sources true

noncomputable def registryFragment (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N) : NonrootBigon N where
  parents := H.parents (originalHybrid N b A)
  upper := A.fragment.upper
  upper_nonroot := A.fragment.upper_nonroot
  arm_sources := original_registry_arm_source N hc b A H

lemma original_registry_parent_pair_exact (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (H : OriginalParentRegistry N) (e : E) :
    e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 ↔
      e = (H.parents (originalHybrid N b A)).parent0 ∨ e = (H.parents (originalHybrid N b A)).parent1 := by
  let parents := Finset.univ.filter (fun f : E => N.graph.target f = A.fragment.parents.hybrid)
  have hs0 : (H.parents (originalHybrid N b A)).parent0 ∈ parents :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,registry_parent_target N H (originalHybrid N b A) false⟩
  have hs1 : (H.parents (originalHybrid N b A)).parent1 ∈ parents :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,registry_parent_target N H (originalHybrid N b A) true⟩
  constructor
  · intro he
    apply edge_pair_exhaustive parents _ _ (H.parents (originalHybrid N b A)).different hs0 hs1 A.fragment.parents.isHybrid.1 e
    rcases he with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,A.fragment.parents.target0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,A.fragment.parents.target1⟩
  · intro he
    apply actual_hybrid_parents_exhaustive N b A e
    rcases he with rfl | rfl
    · exact registry_parent_target N H (originalHybrid N b A) false
    · exact registry_parent_target N H (originalHybrid N b A) true

/-- Same actual blob, cut interfaces and original footprint; only the internal
parent ordering is aligned to the ORIGINAL supplied registry. No gamma or
shared-register coordinate is renamed/refitted. -/
noncomputable def registryAlignedBigon (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N) : ActualBlobBigon N b where
  fragment := registryFragment N hc b A H
  upper_in_blob := A.upper_in_blob
  hybrid_in_blob := by
    change N.graph.blobOf (H.parents (originalHybrid N b A)).hybrid = b
    rw [show (H.parents (originalHybrid N b A)).hybrid = A.fragment.parents.hybrid from H.original_site _]; exact A.hybrid_in_blob
  vertices_exact v := by
    change N.graph.blobOf v = b ↔ v = A.fragment.upper ∨ v = (H.parents (originalHybrid N b A)).hybrid
    rw [show (H.parents (originalHybrid N b A)).hybrid = A.fragment.parents.hybrid from H.original_site _]
    exact A.vertices_exact v
  entry := A.entry
  entry_bridge := A.entry_bridge
  entry_target := A.entry_target
  entry_source_outside := A.entry_source_outside
  child := A.child
  child_bridge := A.child_bridge
  child_source := by
    change N.graph.source A.child = (H.parents (originalHybrid N b A)).hybrid
    rw [show (H.parents (originalHybrid N b A)).hybrid = A.fragment.parents.hybrid from H.original_site _]; exact A.child_source
  child_target_outside := A.child_target_outside
  internal_edges_exact e := (A.internal_edges_exact e).trans (original_registry_parent_pair_exact N b A H e)

theorem actual_registry_aligned_parents (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N) :
    (registryAlignedBigon N hc b A H).fragment.parents = H.parents (originalHybrid N b A) := rfl

end G1OriginalRegistryBigon
