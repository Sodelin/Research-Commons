import OriginalBlob
namespace Nanuq.RawBlock
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
/-- Direct original RootedBinary endpoint. No bridgelessness or degree certificate is assumed. -/
theorem binary_blob_delete_vertex_connected (N : RootedBinary V E X)
    (b : N.graph.Blob) {v a c : BlobVertex N.graph b} (ha : a ≠ v) (hc : c ≠ v) :
    (originalBlob N.graph b).UReach (Avoid (originalBlob N.graph b) v) a c :=
  original_blob_delete_vertex_connected N.graph (binary_incidence_bound N) b ha hc
#print axioms binary_blob_delete_vertex_connected
end Nanuq.RawBlock
