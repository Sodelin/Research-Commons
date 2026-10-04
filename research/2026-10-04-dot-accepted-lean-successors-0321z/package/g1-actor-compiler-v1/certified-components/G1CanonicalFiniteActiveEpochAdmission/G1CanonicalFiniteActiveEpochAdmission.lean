import G1NaturalActiveActorFrontier

/-! Canonical arbitrary finite active actor family plus its ORIGINAL base
complement admits the ACTUAL source epoch tensor. All population separation
is derived at the real original frontier; there is no supplied product law. -/
namespace G1CanonicalFiniteActiveEpochAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceFiniteProjection
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalSpanRegion G1OriginatedNeutralSpanRegion G1DerivedSpanSeparatedAgenda
open G1ActualJointProgram G1ActualFinitePanelProgramTensor G1ActiveCoreBridgeCohorts
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1NaturalActiveActorFrontier
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_panel_union_member {Copy : Type*} [DecidableEq Copy] (keeps : List (Finset Copy)) (x : Copy) :
    x ∈ panelUnion keeps ↔ ∃ keep ∈ keeps, x ∈ keep := by
  induction keeps with
  | nil => simp [panelUnion]
  | cons keep keeps ih => simp only [panelUnion,Finset.mem_union,List.mem_cons,ih]; aesop

lemma actual_panel_subset_union {Copy : Type*} [DecidableEq Copy] (keeps : List (Finset Copy))
    (keep : Finset Copy) (h : keep ∈ keeps) : keep ⊆ panelUnion keeps := by
  intro x hx
  exact (actual_panel_union_member keeps x).mpr ⟨keep,h,hx⟩

lemma actual_panel_union_append {Copy : Type*} [DecidableEq Copy] (xs ys : List (Finset Copy)) :
    panelUnion (xs ++ ys) = panelUnion xs ∪ panelUnion ys := by
  induction xs with
  | nil => simp [panelUnion]
  | cons x xs ih => simp only [panelUnion,List.cons_append,ih,Finset.union_assoc]

lemma actual_disjoint_tail_union {Copy : Type*} [DecidableEq Copy] (keep : Finset Copy) (keeps : List (Finset Copy))
    (hdis : ∀ q ∈ keeps, Disjoint keep q) : Disjoint keep (panelUnion keeps) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨q,hq,hxq⟩ := (actual_panel_union_member keeps x).mp hy
  exact Finset.disjoint_left.mp (hdis q hq) hx hxq

lemma actual_finite_complement_epoch_agenda {V E Copy Y : Type*}
    [Fintype V] [Fintype E] [Fintype Y] [Fintype Copy] [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    (N : RootedBinary V E Y) {sample : Copy → Y} (r : PositivePairRates E) (duration : ℝ≥0)
    (s : Code N sample) (keeps : List (Finset Copy)) (base : Finset Copy)
    (hsep : ∀ keep ∈ keeps, G1JointSeparatedSourceGeometry.PopulationSeparated (state s) keep (Finset.univ \ keep))
    (hdis : keeps.Pairwise Disjoint) (hbase : ∀ keep ∈ keeps, Disjoint keep base) :
    PanelSeparatedAgenda N r [.interval duration] (keeps ++ [base]) s := by
  induction keeps with
  | nil =>
    refine ⟨⟨?_,?_⟩,trivial⟩
    · intro x hx y hy
      exact False.elim (Finset.notMem_empty y hy)
    · intro d hd
      trivial
  | cons keep keeps ih =>
    have hp := List.pairwise_cons.mp hdis
    refine ⟨⟨?_,fun _ _ => trivial⟩,ih (fun q hq => hsep q (List.mem_cons_of_mem keep hq)) hp.2
      (fun q hq => hbase q (List.mem_cons_of_mem keep hq))⟩
    have htaildis : Disjoint keep (panelUnion (keeps ++ [base])) := by
      rw [actual_panel_union_append]
      change Disjoint keep (panelUnion keeps ∪ (base ∪ ∅))
      simp only [Finset.union_empty,Finset.disjoint_union_right]
      exact ⟨actual_disjoint_tail_union keep keeps hp.1,hbase keep (List.mem_cons_self)⟩
    intro x hx y hy heq
    apply hsep keep (List.mem_cons_self) x hx y _ heq
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun hm => Finset.disjoint_left.mp htaildis hm hy⟩

noncomputable def activeOriginalPanels (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (actors : List (BridgeActor T)) :=
  actors.map (fun actor => originalInsideCopies O sample (actorInput O D actor))

noncomputable def activeOriginalBase (O : Source X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (actors : List (BridgeActor T)) :=
  Finset.univ \ panelUnion (activeOriginalPanels O D sample actors)

/-- Arbitrarily many concurrent bridge actors and their complete original
base complement have a DERIVED actual epoch tensor at the real source date
frontier. There is no fixed two/three actor bound or distinct-date premise. -/
theorem actual_finite_active_regions_epoch_admission (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actors : List (BridgeActor T))
    (hnodup : actors.Nodup) (node : O.Vertex)
    (hactive : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (r : PositivePairRates O.Edge) (duration : ℝ≥0) (s : Code O.network sample)
    (hregion : ∀ actor ∈ actors, ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
      SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)) :
    PanelSeparatedAgenda O.network r [.interval duration]
      (activeOriginalPanels O D sample actors ++ [activeOriginalBase O D sample actors]) s := by
  apply actual_finite_complement_epoch_agenda
  · intro keep hk
    obtain ⟨actor,hm,rfl⟩ := List.mem_map.mp hk
    apply actual_neutral_span_population_separator O (bridgeSpan O T D actor.val actor.property)
      (actual_originated_bridge_region_neutral O H D hD actor.val actor.property)
    · exact hregion actor hm
    · intro x hx
      have hx := (Finset.mem_sdiff.mp hx).2
      intro hd
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩)
  · apply List.pairwise_map.mpr
    apply hnodup.imp_of_mem
    intro a b ha hb hne
    apply actual_active_originated_original_cohorts_disjoint O H D hD a.val b.val a.property b.property
      (fun he => hne (Subtype.ext he)) _ (hactive a ha) (hactive b hb) sample
  · intro keep hk
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 (actual_panel_subset_union _ keep hk hx)


theorem actual_canonical_finite_active_epoch_admission (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (actors : List (BridgeActor T))
    (hnodup : actors.Nodup) (node : O.Vertex)
    (hactive : ∀ actor ∈ actors, T.calendar.Active (O.calendar.age node) actor.val)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool) (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (r : PositivePairRates O.Edge) (duration : ℝ≥0) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (G1InitializedFrontierPrefix.actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        (O.calendar.age node)) (initialCode O.network sample register)).support) :
    PanelSeparatedAgenda O.network r [.interval duration]
      (activeOriginalPanels O D sample actors ++ [activeOriginalBase O D sample actors]) s := by
  apply actual_finite_active_regions_epoch_admission O H D hD actors hnodup node hactive sample r duration s
  intro actor hm
  exact actual_real_frontier_active_actor_region O H D hD actor node (hactive actor hm) sample register gamma common r hs
#print axioms actual_canonical_finite_active_epoch_admission
end G1CanonicalFiniteActiveEpochAdmission
