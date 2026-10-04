import G1CanonicalWholeOriginalActiveEpoch

/-! Actual root-blob and retained ancestral population observer. EVERY
current private original span location is outside the ENTIRE original root
blob, derived from physical ownership/provenance rather than assumed. -/
namespace G1ActualRootBlobPopulationFootprint
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open G1UnrankedSourceView G1ActualGraphNormalization G1DecoratedOriginalProvenance
open G1FiniteOriginalDecoratedCore G1OriginalSpanRegion G1OriginalActorOperationOwnership
open G1RootBlobRetainedBaseOwnership G1CanonicalActorLifecycleCompiler G1OriginalRecipePopulationOwnership
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def OriginalRootBlobPopulation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X) : Location V E → Prop
  | .node v => N.graph.SameBlob N.root v
  | .edge e => N.graph.SameBlob N.root (N.graph.source e) ∧ N.graph.SameBlob N.root (N.graph.target e)
  | .rootPopulation v => v = N.root

def observedRootPopulation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X) : Option (Location V E) → Prop
  | none => False
  | some p => OriginalRootBlobPopulation N p

noncomputable def originalRootBlobView {V E Copy : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (v : UnrankedView V E Copy) : UnrankedView V E Copy where
  genealogy x := if observedRootPopulation N (v.population x) then v.genealogy x else none
  population x := if observedRootPopulation N (v.population x) then v.population x else none
  register := v.register

/-- Whole original root-blob ownership forbids ALL private active locations,
including internal original populations. It is not only a root-node fact. -/
theorem actual_private_span_outside_original_root_blob (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (actor : BridgeActor T) (p : Location O.Vertex O.Edge)
    (hp : SpanLocation O (bridgeSpan O T D actor.val actor.property) p) :
    ¬ OriginalRootBlobPopulation O.network p := by
  cases p with
  | node v =>
    intro hr
    have hnone := actual_original_root_blob_node_has_no_actor_owner O H D hD v hr
    have hsome := actual_node_actor_owner_of_member O H D hD v actor hp
    rw [hsome] at hnone
    cases hnone
  | edge e =>
    rintro ⟨hs,ht⟩
    have hb := (actual_original_root_blob_population_retained_base O H D hD e hs ht).2
    have he := actual_population_owner_unique O H D hD e actor.val (by
      rw [←actual_bridge_span_populations]
      exact hp)
    exact hb (he ▸ actor.property)
  | rootPopulation v => exact False.elim hp

#print axioms actual_private_span_outside_original_root_blob
end G1ActualRootBlobPopulationFootprint
