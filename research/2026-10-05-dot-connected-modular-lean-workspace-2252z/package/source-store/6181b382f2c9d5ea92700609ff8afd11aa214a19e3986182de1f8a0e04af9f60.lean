import GraphMedianUnique
import AnchorPortCounts

/-! The finite port-count dichotomy instantiated on actual original blobs and
their actual taxon projections.  Unique medians are derived from the source.
This does not yet identify the four-port local quartet row or circular order. -/
namespace Nanuq.Source.RootedBinary

open Nanuq.PortPatterns
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem actual_quartet_blob_port_branching (N : RootedBinary V E X)
    (q : Fin 4 ↪ X) :
    ((Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (fun i => N.blobProjection b.val b.property (q i)) = 4)).card = 1 ∧
      (Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (fun i => N.blobProjection b.val b.property (q i)) = 3)).card = 0) ∨
    ((Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (fun i => N.blobProjection b.val b.property (q i)) = 4)).card = 0 ∧
      (Finset.univ.filter (fun b : {b : N.graph.Blob // N.NonleafBlob b} =>
        portCount (fun i => N.blobProjection b.val b.property (q i)) = 3)).card = 2) := by
  classical
  let f := fun (b : {b : N.graph.Blob // N.NonleafBlob b}) (i : Fin 4) =>
    N.blobProjection b.val b.property (q i)
  have hu : ∀ i : Fin 4, ∃! b, tripleInjective (f b) i := by
    intro i
    let q3 : Fin 3 ↪ X := ⟨fun j => q (omitTriple i j), by
      intro j k h
      exact (omitTriple i).injective (q.injective h)⟩
    obtain ⟨b, ⟨hb, hbi⟩, hunique⟩ := N.existsUnique_three_way_blob q3
    refine ⟨⟨b, hb⟩, hbi, ?_⟩
    intro c hc
    apply Subtype.ext
    exact hunique c.val ⟨c.property, hc⟩
  exact branching_port_counts_of_unique f hu

end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_quartet_blob_port_branching
