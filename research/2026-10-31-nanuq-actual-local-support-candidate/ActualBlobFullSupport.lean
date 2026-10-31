import ActualLowPorts
import ActualSingletonPorts

/-! UNCOMPILED actual local support provider for every nonleaf blob.
The transparent conclusion below is PROVED from the original cap/drawing;
it is not an additional source/order certificate. Global A.7 transport,
given global C compatibility and original semidirected admission remain open. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open Nanuq.Weighted Nanuq.Reconstruction Nanuq.RawBlock
open G1ActualDisplayedClusterSplitTransport
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

/-- Exact output, not a premise: two-port zero and, for ≥3 ports, positive
mass circular decomposition with ALL actual displayed splits as exact support.
Rank is chosen BEFORE all masses/coefficients/cuts. -/
def LocalFullSupportAt (N : RootedBinary V E X) {n : Nat} (rank : X ≃ Fin n) : Prop :=
  (n=2 → ∀ (m : X → ℚ) (x y : X), N.actualWeightedAnchorDistance m x y=0) ∧
  (3≤n → ∀ (m : X → ℚ), (∀ x, 0<m x) →
    CircularDecomposable (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) ∧
    (∀ i j : Fin n, i<j →
      (0<circularAlpha (fun x y => N.actualWeightedAnchorDistance m (rank.symm x) (rank.symm y)) i j ↔
        ({rankIntervalSide rank i.val j.val,Finset.univ \ rankIntervalSide rank i.val j.val} :
          Finset (Finset X)) ∈ actualDisplayedSplits N Finset.univ)) ∧
    (∀ cut∈actualDisplayedSplits N Finset.univ, ∃ i j : Nat, i<j ∧ j<n ∧
      cut={rankIntervalSide rank i j,Finset.univ \ rankIntervalSide rank i j}))

theorem actual_three_port_full_support (N : RootedBinary V E X) (rank : X ≃ Fin 3) :
    LocalFullSupportAt N rank := by
  constructor
  · intro h; omega
  · intro _ m hm
    exact actual_three_port_support N rank m hm

theorem actual_two_port_full_support (N : RootedBinary V E X) (rank : X ≃ Fin 2) :
    LocalFullSupportAt N rank := by
  constructor
  · intro _ m x y
    exact actual_two_port_zero N rank m x y
  · intro h; omega

end Nanuq.ActualCutClusters

namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.ActualFinite Nanuq.ActualCutClusters
open Nanuq.AdjacentCertificate
open Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open scoped Graph Classical
local notation "Plane" => Schoenflies.Plane
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)
variable (hg : N.graph.GalledDetour) (hb : N.NonleafBlob b)
local notation "M" => N.actualEveryNonleafRootedCapSource b hb

include hg in
theorem actual_nontrivial_blob_full_local_support
    (face : TaxonOuterFace D N.leaf)
    (hnt : ∃ u v : BlobVertex N.graph b, u≠v) :
    ∃ (n : Nat) (rank : N.BlobPort b ≃ Fin n) (C : Set Plane),
      2≤n ∧ IsJordanCurve C ∧
      Graph.face (graph (blobCurves D b)) (curve (blobCurves D b))
        (coordinates face.outside)=outside C ∧ LocalFullSupportAt (M) rank := by
  obtain ⟨n,mask,rank,C,f,θ,xs,k,T,hn,hmask,hC,hface,hf,himage,hθ,hθinj,hnd,hall,
    horder,hk,hblocks,hsize,hlocal,hglobal,hsorted,hanchor⟩ :=
      actual_canonical_sorted_anchor_receiver N D b hg hb face hnt
  refine ⟨n,rank,C,hn,hC,hface,?_,?_⟩
  · intro he m x y
    subst n
    exact actual_two_port_zero (M) rank m x y
  · intro hn3 m hm
    exact actual_weighted_all_interval_support (M) n mask rank T hn3 hsize
      (fun q => (hlocal q).1) (fun q => (hlocal q).2) m hm

theorem actual_singleton_blob_full_local_support
    (v : BlobVertex N.graph b) (hall : ∀ w : BlobVertex N.graph b, w=v) :
    ∃ (n : Nat) (rank : N.BlobPort b ≃ Fin n),
      (n=2 ∨ n=3) ∧ LocalFullSupportAt (M) rank := by
  rcases Nanuq.SmallBlob.singleton_nonleaf_port_card N b v hall hb with h | h
  · exact ⟨2,Fintype.equivFinOfCardEq h,Or.inl rfl,
      actual_two_port_full_support (M) (Fintype.equivFinOfCardEq h)⟩
  · exact ⟨3,Fintype.equivFinOfCardEq h,Or.inr rfl,
      actual_three_port_full_support (M) (Fintype.equivFinOfCardEq h)⟩

include hg in
theorem actual_every_blob_full_local_support (face : TaxonOuterFace D N.leaf) :
    ∃ (n : Nat) (rank : N.BlobPort b ≃ Fin n), 2≤n ∧ LocalFullSupportAt (M) rank := by
  by_cases hnt : ∃ u v : BlobVertex N.graph b, u≠v
  · obtain ⟨n,rank,C,hn,hC,hface,hs⟩ :=
      actual_nontrivial_blob_full_local_support N D b hg hb face hnt
    exact ⟨n,rank,hn,hs⟩
  · obtain ⟨w,hw⟩ := Quotient.exists_rep b
    let v : BlobVertex N.graph b := ⟨w,hw⟩
    have hall : ∀ a : BlobVertex N.graph b, a=v := by
      intro a
      by_contra h
      exact hnt ⟨a,v,h⟩
    obtain ⟨n,rank,hn,hs⟩ := actual_singleton_blob_full_local_support N b hb v hall
    exact ⟨n,rank,by rcases hn with rfl | rfl <;> omega,hs⟩

end Nanuq.OpenedCore
