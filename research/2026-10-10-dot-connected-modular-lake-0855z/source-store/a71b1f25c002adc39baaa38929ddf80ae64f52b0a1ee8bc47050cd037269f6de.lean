import G1ActualCanonicalFinalCutPort

/-! Source-derived runtime actor sets. Original exit prefixes close exactly
one literal original last cut, then every lower-date opening occurs before
that date's node batch. Equal closing/opening dates remain fully admitted. -/
namespace G1CanonicalPendingActorSets
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1ActorInterfaceUniqueness
open G1OriginalSpanRegion G1OriginalRecipePopulationOwnership G1ConstructedPopulationPartition
open G1PrivateActorLifetimeAdmission G1OriginalActorTemporalFootprint
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def beforeExitActors (T : Source X) (date : ℝ) : Finset (BridgeActor T) :=
  Finset.univ.filter (fun actor => T.calendar.age (T.network.graph.target actor.val) < date ∧
    date ≤ T.calendar.age (T.network.graph.source actor.val))

noncomputable def afterExitActors (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) (processed : List O.Edge) :
    Finset (BridgeActor T) :=
  (beforeExitActors T date).filter (fun actor => actorCut O H D hD actor ∉ processed)

noncomputable def dateOpeningActors (T : Source X) (date : ℝ) : Finset (BridgeActor T) :=
  Finset.univ.filter (fun actor => T.calendar.age (T.network.graph.target actor.val) = date)

noncomputable def afterOpeningActors (T : Source X) (date : ℝ) : Finset (BridgeActor T) :=
  Finset.univ.filter (fun actor => T.calendar.Active date actor.val)

lemma actual_actor_cuts_injective (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) :
    Function.Injective (actorCut O H D hD) := by
  intro a b heq
  have ha := actual_actor_cut_in_region O H D hD a
  have hb := actual_actor_cut_in_region O H D hD b
  rw [actual_bridge_span_populations] at ha hb
  rw [heq] at ha
  apply Subtype.ext
  exact (actual_population_owner_unique O H D hD _ a.val ha).trans
    (actual_population_owner_unique O H D hD _ b.val hb).symm

lemma actual_cut_in_date_exit_batch (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) (actor : BridgeActor T) :
    actorCut O H D hD actor ∈ G1OriginalCalendarDecomposition.originalExits O.network O.calendar date ↔
      T.calendar.age (T.network.graph.source actor.val) = date := by
  simp only [G1OriginalCalendarDecomposition.originalExits,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,
    actual_actor_cut_source,←D.calendar]

/-- An actual closing tag removes exactly its own current pending slot. No
other actor's cut can be confused with it, even at the same original date. -/
theorem actual_pending_exit_close_set_update (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) (processed : List O.Edge)
    (actor : BridgeActor T) :
    afterExitActors O H D hD date (processed ++ [actorCut O H D hD actor]) =
      (afterExitActors O H D hD date processed).erase actor := by
  ext other
  simp only [afterExitActors,Finset.mem_filter,List.mem_append,List.mem_singleton,not_or,Finset.mem_erase]
  constructor
  · rintro ⟨hp,hn,hcut⟩
    exact ⟨fun he => hcut (he ▸ rfl),hp,hn⟩
  · rintro ⟨hne,hp,hn⟩
    exact ⟨hp,hn,fun he => hne (actual_actor_cuts_injective O H D hD he)⟩

/-- ALL old same-date exits precede openings. Once all exits finish, adding
exactly that date's new actors gives the actual physical active-bridge set. -/
theorem actual_all_exits_then_openings_active_set (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) :
    afterExitActors O H D hD date (G1OriginalCalendarDecomposition.originalExits O.network O.calendar date) ∪
      dateOpeningActors T date = afterOpeningActors T date := by
  ext actor
  simp only [afterExitActors,beforeExitActors,dateOpeningActors,afterOpeningActors,Finset.mem_union,Finset.mem_filter,
    Finset.mem_univ,true_and,actual_cut_in_date_exit_batch,Calendar.Active]
  have hspan := T.calendar.edge_older actor.val
  constructor
  · rintro (⟨⟨hlo,hhi⟩,hne⟩ | hopen)
    · exact ⟨hlo.le,lt_of_le_of_ne hhi (Ne.symm hne)⟩
    · exact ⟨hopen.le,hopen ▸ hspan⟩
  · rintro ⟨hlo,hhi⟩
    rcases hlo.eq_or_lt with heq | hlo
    · exact Or.inr heq
    · exact Or.inl ⟨⟨hlo,hhi.le⟩,ne_of_gt hhi⟩

#print axioms actual_pending_exit_close_set_update
#print axioms actual_all_exits_then_openings_active_set
end G1CanonicalPendingActorSets
