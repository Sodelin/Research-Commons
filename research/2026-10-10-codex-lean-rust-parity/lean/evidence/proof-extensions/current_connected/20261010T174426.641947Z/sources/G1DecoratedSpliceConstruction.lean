import G1LiftedOriginalBigon

/-! Constructed original-provenance labels under actual physical splices.
Contributor: dot, 2026-10-03. No supplied output law or scalar synthetic
rate occurs. Every new bridge stores a literal original-source span. -/
namespace G1DecoratedSpliceConstruction
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1ActualTwoPortBlob G1CutChildPorts G1NonrootBigonKernel G1LiftedOriginalBigon
open G1BigonSpliceGraph G1SplicedSourceAdmission G1SpliceDegrees G1SpliceRootBlob G1SpliceCutTransport
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def actualSplicedSource (S : Source X) (b : S.network.graph.Blob)
    (hb : b ≠ S.network.graph.blobOf S.network.root) (A : ActualBlobBigon S.network b) : Source X :=
  admit (splicedNetwork S.network S.cutChild b hb A)
    (actual_spliced_cut_child S.network S.cutChild b hb A)
    (splicedCalendar S.network S.cutChild b hb A S.calendar)

noncomputable def retainedVertexEmbedding (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) : SplicedVertex S.network b A ↪ O.Vertex where
  toFun v := D.vertex v.val
  inj' _ _ h := Subtype.ext (D.vertex.injective h)

noncomputable def splicedRecipe (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) :
    SplicedEdge S.network b A → Recipe O
  | .inl e => D.recipe e.val
  | .inr _ => .span (D.vertex (S.network.graph.target A.child))
      (D.vertex (S.network.graph.source A.entry)) (newOriginalSpan O S D H b A)

/-- Every physical splice keeps raw original nonbridge IDs and its entire
original root blob; the new bridge carries a composed ORIGINAL program. -/
noncomputable def spliceDecoration (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (hb : b ≠ S.network.graph.blobOf S.network.root) (A : ActualBlobBigon S.network b) :
    Decoration O (actualSplicedSource S b hb A) where
  vertex := retainedVertexEmbedding O S D b A
  root := D.root
  taxa x := D.taxa x
  calendar x := D.calendar x.val
  indegree x := (actual_splice_indegree S.network S.cutChild b A x).trans (D.indegree x.val)
  outdegree x := (actual_splice_outdegree S.network S.cutChild b A x).trans (D.outdegree x.val)
  sameBlob x y := (actual_kept_sameBlob_iff S.network S.cutChild b A x y).trans (D.sameBlob x.val y.val)
  rootBlob_surjective v hv := by
    obtain ⟨x,hx,hv⟩ := D.rootBlob_surjective v hv
    let y : SplicedVertex S.network b A := ⟨x,actual_original_root_blob_vertex_kept S.network b hb A x hx⟩
    exact ⟨y,(actual_kept_sameBlob_iff S.network S.cutChild b A _ y).mpr hx,hv⟩
  recipe := splicedRecipe O S D H b A
  endpoints e := by
    cases e with
    | inl e => exact D.endpoints e.val
    | inr z => exact ⟨rfl,rfl⟩
  raw_nonbridge e he := by
    cases e with
    | inl e =>
        exact D.raw_nonbridge e.val (by
          intro hh
          exact he ((actual_retained_bridge_iff S.network S.cutChild b A e).mpr hh))
    | inr z =>
        cases z
        exact False.elim (he (actual_new_edge_bridge S.network S.cutChild b A))
  raw_bridge e f h := by
    cases e with
    | inl e =>
        exact (actual_retained_bridge_iff S.network S.cutChild b A e).trans (D.raw_bridge e.val f h)
    | inr z => cases h
  raw_injective e f a he hf := by
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            exact congrArg Sum.inl (Subtype.ext (D.raw_injective e.val f.val a he hf))
        | inr z => cases hf
    | inr z => cases he

/-- Normalization's exact constructed step admits its derived original labels. -/
noncomputable def normalizedSpliceDecoration (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (hb : b ≠ S.network.graph.blobOf S.network.root) (hp : Fintype.card (S.network.BlobPort b) = 2) :
    Decoration O (splice S b hb hp) :=
  spliceDecoration O S D H b hb
    (extractedBigon S.network S.cutChild b hb ((actual_quotient_port_card S.network b).symm.trans hp))

end G1DecoratedSpliceConstruction
