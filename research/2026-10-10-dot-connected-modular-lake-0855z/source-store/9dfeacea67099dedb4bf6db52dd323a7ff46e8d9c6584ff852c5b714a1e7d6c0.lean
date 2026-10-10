import G1OriginatedClosingSourceAdmission

/-! Actual retained-node taxon reachability through ALL constructed graph
splices. Contributor: dot, 2026-10-03. Used for original-label cut cohorts. -/
namespace G1OriginatedTaxonReachTransport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1DecoratedSpliceConstruction G1ActualTwoPortBlob G1BigonSpliceGraph
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_splice_kept_directed_reach (S : Source X) (b : S.network.graph.Blob)
    (A : ActualBlobBigon S.network b) (v w : SplicedVertex S.network b A) :
    (spliceGraph S.network S.cutChild b A).DReach v w ↔ S.network.graph.DReach v.val w.val := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih =>
        obtain ⟨e,hes,het⟩ := hstep
        have he := actual_spliced_edge_expansion S.network S.cutChild b A e
        rw [hes,het] at he
        exact ih.trans he.to_reflTransGen
  · intro h
    have he := actual_original_reach_collapse S.network S.cutChild b A h
    rw [collapse_kept,collapse_kept] at he
    exact he

theorem actual_originated_taxon_reach (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    ∀ v : T.Vertex, ∀ x : X,
      T.network.graph.DReach v (T.network.leaf x) ↔ O.network.graph.DReach (D.vertex v) (O.network.leaf x) := by
  induction hD with
  | initial => exact fun _ _ => Iff.rfl
  | @splice S D prior b hb hp ih =>
      intro v x
      let A := extractedBigon S.network S.cutChild b hb ((G1CutChildPorts.actual_quotient_port_card S.network b).symm.trans hp)
      have h := actual_splice_kept_directed_reach S b A v (retainedTaxa S.network b A x)
      exact h.trans (ih v.val x)

#print axioms actual_originated_taxon_reach
end G1OriginatedTaxonReachTransport
