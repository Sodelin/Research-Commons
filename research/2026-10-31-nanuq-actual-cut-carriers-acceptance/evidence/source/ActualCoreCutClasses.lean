import ActualOpenedCore

/-! UNCOMPILED LOCAL DRAFT for the coherent actual cut-carrier package.
Bridge separation is DERIVED from the qualified actual opened tree, not an
extra source or geometric separation premise. -/
set_option debug.skipKernelTC false
namespace Nanuq.OpenedCore
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)

include hb in
/-- Every literal retained original core edge separates its actual endpoint
classes. This follows by lifting a hypothetical detour to the original opened
tree with the SAME forbidden edge occurrence. -/
theorem actual_core_all_bridges (k : N.OriginalBlobArc b) :
    (coreGraph N b hg).IsBridge k := by
  intro h
  have hlift := core_cut_walk_lifts N b hg hb k h
  have hbri := (N.actual_galled_cap_opens_to_tree hg b hb).2.2
    (coreEdgeLift N b hg hb k)
  apply hbri
  rw [coreEdgeLift_source,coreEdgeLift_target]
  exact hlift

#print axioms actual_core_all_bridges
end Nanuq.OpenedCore
