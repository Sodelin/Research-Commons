import NanuqActualRootedCapReadout
import NanuqActualBridgeQuartetResolution

/-! A repeated actual port pair supplies a literal original bridge quartet.
These source-side facts are intended for the three-port terms in the anchor
sum; the anchor identity and global composition are not assumed. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem actual_port_pair_hasQuartet (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (p : N.BlobPort b) (a c d e : X)
    (ha : N.blobProjection b hb a = p) (hc : N.blobProjection b hb c = p)
    (hd : N.blobProjection b hb d ≠ p) (he : N.blobProjection b hb e ≠ p) :
    N.graph.HasQuartet (N.leaf a) (N.leaf c) (N.leaf d) (N.leaf e) := by
  let f := p.val.val
  have hf : N.graph.IsBridge f := p.val.property
  rcases p.property with hs | ht
  · have hT (x : X) : N.blobProjection b hb x = p ↔
        N.graph.ReachWithout f (N.graph.target f) (N.leaf x) :=
      N.blobProjection_eq_iff_target_side b hb x p hs
    have hS (x : X) (hx : N.blobProjection b hb x ≠ p) :
        N.graph.ReachWithout f (N.graph.source f) (N.leaf x) := by
      rcases N.graph.edge_side_cover f (N.underlying_connected _ _) with h | h
      · exact h
      · exact False.elim (hx ((hT x).mpr h))
    exact ⟨f,hf,Or.inr ⟨hS d hd,hS e he,(hT a).mp ha,(hT c).mp hc⟩⟩
  · have hS (x : X) : N.blobProjection b hb x = p ↔
        N.graph.ReachWithout f (N.graph.source f) (N.leaf x) :=
      N.blobProjection_eq_iff_source_side b hb x p ht
    have hT (x : X) (hx : N.blobProjection b hb x ≠ p) :
        N.graph.ReachWithout f (N.graph.target f) (N.leaf x) := by
      rcases N.graph.edge_side_cover f (N.underlying_connected _ _) with h | h
      · exact False.elim (hx ((hS x).mpr h))
      · exact h
    exact ⟨f,hf,Or.inl ⟨(hS a).mp ha,(hS c).mp hc,hT d hd,hT e he⟩⟩

theorem actual_repeated_port_pair_raw_mean (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (h01 : N.blobProjection b hb (q 0) = N.blobProjection b hb (q 1))
    (h20 : N.blobProjection b hb (q 2) ≠ N.blobProjection b hb (q 0))
    (h30 : N.blobProjection b hb (q 3) ≠ N.blobProjection b hb (q 0)) :
    N.rawQuartetMean q = 0 := by
  exact N.actual_rawQuartetMean_of_original_bridge q .xy_zw
    (N.actual_port_pair_hasQuartet b hb _ (q 0) (q 1) (q 2) (q 3) rfl h01.symm h20 h30)

theorem actual_repeated_cross_port_raw_mean (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (h02 : N.blobProjection b hb (q 0) = N.blobProjection b hb (q 2))
    (h10 : N.blobProjection b hb (q 1) ≠ N.blobProjection b hb (q 0))
    (h30 : N.blobProjection b hb (q 3) ≠ N.blobProjection b hb (q 0)) :
    N.rawQuartetMean q = 1 := by
  exact N.actual_rawQuartetMean_of_original_bridge q .xz_yw
    (N.actual_port_pair_hasQuartet b hb _ (q 0) (q 2) (q 1) (q 3) rfl h02.symm h10 h30)

theorem actual_repeated_port_03_raw_mean (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hij : N.blobProjection b hb (q 0) = N.blobProjection b hb (q 3))
    (hki : N.blobProjection b hb (q 1) ≠ N.blobProjection b hb (q 0))
    (hli : N.blobProjection b hb (q 2) ≠ N.blobProjection b hb (q 0)) :
    N.rawQuartetMean q = 1 := by
  apply N.actual_rawQuartetMean_of_original_bridge q .xw_yz
  exact N.actual_port_pair_hasQuartet b hb _ (q 0) (q 3) (q 1) (q 2) rfl hij.symm hki hli

theorem actual_repeated_port_12_raw_mean (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hij : N.blobProjection b hb (q 1) = N.blobProjection b hb (q 2))
    (hki : N.blobProjection b hb (q 0) ≠ N.blobProjection b hb (q 1))
    (hli : N.blobProjection b hb (q 3) ≠ N.blobProjection b hb (q 1)) :
    N.rawQuartetMean q = 1 := by
  apply N.actual_rawQuartetMean_of_original_bridge q .xw_yz
  obtain ⟨e,he,h | h⟩ := N.actual_port_pair_hasQuartet b hb _
    (q 1) (q 2) (q 0) (q 3) rfl hij.symm hki hli
  · exact ⟨e,he,Or.inr h⟩
  · exact ⟨e,he,Or.inl h⟩

theorem actual_repeated_port_13_raw_mean (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hij : N.blobProjection b hb (q 1) = N.blobProjection b hb (q 3))
    (hki : N.blobProjection b hb (q 0) ≠ N.blobProjection b hb (q 1))
    (hli : N.blobProjection b hb (q 2) ≠ N.blobProjection b hb (q 1)) :
    N.rawQuartetMean q = 1 := by
  apply N.actual_rawQuartetMean_of_original_bridge q .xz_yw
  obtain ⟨e,he,h | h⟩ := N.actual_port_pair_hasQuartet b hb _
    (q 1) (q 3) (q 0) (q 2) rfl hij.symm hki hli
  · exact ⟨e,he,Or.inr h⟩
  · exact ⟨e,he,Or.inl h⟩

theorem actual_repeated_port_23_raw_mean (q : Fin 4 ↪ X)
    (b : N.graph.Blob) (hb : N.NonleafBlob b)
    (hij : N.blobProjection b hb (q 2) = N.blobProjection b hb (q 3))
    (hki : N.blobProjection b hb (q 0) ≠ N.blobProjection b hb (q 2))
    (hli : N.blobProjection b hb (q 1) ≠ N.blobProjection b hb (q 2)) :
    N.rawQuartetMean q = 0 := by
  apply N.actual_rawQuartetMean_of_original_bridge q .xy_zw
  obtain ⟨e,he,h | h⟩ := N.actual_port_pair_hasQuartet b hb _
    (q 2) (q 3) (q 0) (q 1) rfl hij.symm hki hli
  · exact ⟨e,he,Or.inr h⟩
  · exact ⟨e,he,Or.inl h⟩
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_port_pair_hasQuartet
#print axioms Nanuq.Source.RootedBinary.actual_repeated_port_pair_raw_mean
#print axioms Nanuq.Source.RootedBinary.actual_repeated_cross_port_raw_mean
