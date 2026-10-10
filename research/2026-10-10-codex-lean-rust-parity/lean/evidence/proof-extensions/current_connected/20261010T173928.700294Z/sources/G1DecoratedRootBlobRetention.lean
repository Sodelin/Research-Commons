import G1FiniteOriginalDecoratedCore

/-! Exact original whole root-blob retention after ALL constructed splices.
Contributor: dot, 2026-10-03. Includes original edge IDs and vertex bijection,
not only absence of a root boundary operation. -/
namespace G1DecoratedRootBlobRetention
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1DecoratedSpliceConstruction
open G1FiniteOriginalDecoratedCore G1ActualTwoPortBlob G1SpliceRootBlob G1BigonSpliceGraph
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def originalRootBlobEmbedding (O T : Source X) (D : Decoration O T) :
    {x : T.Vertex // T.network.graph.SameBlob T.network.root x} ↪
      {x : O.Vertex // O.network.graph.SameBlob O.network.root x} where
  toFun x := ⟨D.vertex x.val,by
    have h := (D.sameBlob T.network.root x.val).mp x.property
    rw [D.root] at h
    exact h⟩
  inj' x y h := Subtype.ext (D.vertex.injective (congrArg Subtype.val h))

/-- ALL original root-blob vertices are retained bijectively under the exact
original embedding; retained population/register IDs can use this bijection. -/
noncomputable def actualWholeOriginalRootBlobEquiv (O T : Source X) (D : Decoration O T) :
    {x : T.Vertex // T.network.graph.SameBlob T.network.root x} ≃
      {x : O.Vertex // O.network.graph.SameBlob O.network.root x} :=
  Equiv.ofBijective (originalRootBlobEmbedding O T D) ⟨(originalRootBlobEmbedding O T D).injective,by
    intro x
    obtain ⟨y,hy,heq⟩ := D.rootBlob_surjective x.val x.property
    exact ⟨⟨y,hy⟩,Subtype.ext heq⟩⟩

/-- Every actual original root-blob edge survives every constructed splice,
carrying the SAME ORIGINAL raw edge ID. No demographic reinterpretation is
necessary on the root blob. -/
theorem actual_original_root_blob_raw_edges_survive (O : Source X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (f : O.Edge)
    (hs : O.network.graph.SameBlob O.network.root (O.network.graph.source f))
    (ht : O.network.graph.SameBlob O.network.root (O.network.graph.target f)) :
    ∃ e : T.Edge, D.recipe e = .raw f := by
  induction hD with
  | initial => exact ⟨f,rfl⟩
  | @splice S D prior b hb hp ih =>
      obtain ⟨e,he⟩ := ih
      let A := extractedBigon S.network S.cutChild b hb ((G1CutChildPorts.actual_quotient_port_card S.network b).symm.trans hp)
      have hep := D.endpoints e
      rw [he] at hep
      change O.network.graph.target f = D.vertex (S.network.graph.target e) ∧
        O.network.graph.source f = D.vertex (S.network.graph.source e) at hep
      have hsrc : S.network.graph.SameBlob S.network.root (S.network.graph.source e) := by
        apply (D.sameBlob _ _).mpr
        rw [D.root,← hep.2]
        exact hs
      have htrg : S.network.graph.SameBlob S.network.root (S.network.graph.target e) := by
        apply (D.sameBlob _ _).mpr
        rw [D.root,← hep.1]
        exact ht
      have hkeep := actual_original_root_blob_edge_kept S.network b hb A e hsrc htrg
      exact ⟨Sum.inl ⟨e,hkeep⟩,he⟩

#print axioms actual_original_root_blob_raw_edges_survive
end G1DecoratedRootBlobRetention
