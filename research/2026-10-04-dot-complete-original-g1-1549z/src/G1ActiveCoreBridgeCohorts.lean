import G1FinitePendingActorPromotion

/-! Distinct simultaneously active physical core bridges have disjoint
ORIGINAL descendant cohorts. Overlapping age intervals are permitted and
resolved by actual bridge routes, not a non-overlap assumption. -/
namespace G1ActiveCoreBridgeCohorts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginatedTaxonReachTransport
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Every complete original current-core tip route contains both descendant
bridges. Its physical calendar admits only one active edge at a time. -/
theorem actual_active_bridge_descendants_disjoint (T : Source.{u,v,w} X)
    (e f : T.Edge) (he : T.network.graph.IsBridge e) (hf : T.network.graph.IsBridge f)
    (hef : e ≠ f) (time : ℝ) (hae : T.calendar.Active time e) (haf : T.calendar.Active time f)
    (x : X) :
    ¬ (T.network.graph.DReach (T.network.graph.target e) (T.network.leaf x) ∧
      T.network.graph.DReach (T.network.graph.target f) (T.network.leaf x)) := by
  rintro ⟨hxe,hxf⟩
  obtain ⟨route,hr⟩ := original_tip_route_exists T.network x
  exact hef (hr.active_unique T.calendar
    (bridge_mem_every_descendant_route T.network he hr hxe)
    (bridge_mem_every_descendant_route T.network hf hr hxf) hae haf)

theorem actual_active_originated_original_descendants_disjoint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f)
    (time : ℝ) (hae : T.calendar.Active time e) (haf : T.calendar.Active time f) (x : X) :
    ¬ (O.network.graph.DReach (D.vertex (T.network.graph.target e)) (O.network.leaf x) ∧
      O.network.graph.DReach (D.vertex (T.network.graph.target f)) (O.network.leaf x)) := by
  rw [←actual_originated_taxon_reach O H D hD _ x,←actual_originated_taxon_reach O H D hD _ x]
  exact actual_active_bridge_descendants_disjoint T e f he hf hef time hae haf x

noncomputable def originalInsideCopies (O : Source X) {Copy : Type*} [Fintype Copy]
    (sample : Copy → X) (input : O.Vertex) : Finset Copy :=
  Finset.univ.filter (fun x => O.network.graph.DReach input (O.network.leaf (sample x)))

theorem actual_active_originated_original_cohorts_disjoint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T)
    (hD : Originated O H D) (e f : T.Edge) (he : T.network.graph.IsBridge e)
    (hf : T.network.graph.IsBridge f) (hef : e ≠ f)
    (time : ℝ) (hae : T.calendar.Active time e) (haf : T.calendar.Active time f)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) :
    Disjoint (originalInsideCopies O sample (D.vertex (T.network.graph.target e)))
      (originalInsideCopies O sample (D.vertex (T.network.graph.target f))) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact actual_active_originated_original_descendants_disjoint O H D hD e f he hf hef time hae haf (sample x)
    ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩

#print axioms actual_active_originated_original_cohorts_disjoint
end G1ActiveCoreBridgeCohorts
