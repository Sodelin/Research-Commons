import G1CanonicalOriginalBoundaryAsyncBatch

/-! The actor roles at consecutive ORIGINAL dates match exactly across one
original epoch. No private actor can open/close inside an original date gap;
all endpoints are retained original vertices. Initial pending base is whole. -/
namespace G1CanonicalOriginalDateGapRoles
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalPendingActorSets G1CanonicalOriginalExitAsyncStep
open G1CanonicalOriginalNodeAsyncStep G1CanonicalOriginalNodeAsyncBatch G1CanonicalOriginalExitCloseReplay
open G1CanonicalEpochSpecialization G1OriginalCalendarDecomposition G1CanonicalThreeEpochList
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

/-- Physical original date gap, independent of probabilities and actor outputs. -/
def OriginalDateGap (O : Source.{u,v,w} X) (lower upper : ℝ) : Prop :=
  ∀ node : O.Vertex, lower < O.calendar.age node → upper ≤ O.calendar.age node

lemma actual_next_original_date_gap (O : Source.{u,v,w} X) (lower upper : ℝ) (later : List ℝ)
    (heq : afterDate O.network O.calendar lower = upper :: later) : OriginalDateGap O lower upper := by
  intro node hn
  have hm := original_after_member O.network O.calendar lower node hn
  rw [heq] at hm
  have hp := original_after_ordered O.network O.calendar lower
  rw [heq] at hp
  rcases List.mem_cons.mp hm with he | hm
  · exact he.ge
  · exact ((List.pairwise_cons.mp hp).1 _ hm).le

/-- Every derived active coordinate before an original epoch is precisely the
not-yet-closed coordinate at its upper ORIGINAL pre-exit frontier. -/
theorem actual_original_gap_actor_role_set (O : Source.{u,v,w} X) {T : Source X}
    (D : Decoration O T) (lower upper : ℝ) (hlt : lower < upper) (hgap : OriginalDateGap O lower upper) :
    afterOpeningActors T lower = beforeExitActors T upper := by
  ext actor
  simp only [afterOpeningActors,beforeExitActors,Finset.mem_filter,Finset.mem_univ,true_and,Calendar.Active]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨hlo.trans_lt hlt,?_⟩
    have hp := hgap (D.vertex (T.network.graph.source actor.val)) (by simpa only [D.calendar] using hhi)
    simpa only [D.calendar] using hp
  · rintro ⟨hlo,hhi⟩
    refine ⟨?_,hlt.trans_le hhi⟩
    by_contra hn
    have hp := hgap (D.vertex (T.network.graph.target actor.val)) (by simpa only [D.calendar] using lt_of_not_ge hn)
    have hp : upper ≤ T.calendar.age (T.network.graph.target actor.val) := by simpa only [D.calendar] using hp
    exact (not_lt_of_ge hp) hlo

/-- Original causal projections are identical across the epoch role boundary;
canonical list ordering and hidden representative IDs play no role. -/
theorem actual_original_gap_same_runtime_projection (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (lower upper : ℝ) (hlt : lower < upper) (hgap : OriginalDateGap O lower upper) :
    canonicalDateProjection O D (sample := sample) lower =
      canonicalExitProjection O H D hD (sample := sample) upper [] := by
  unfold canonicalDateProjection canonicalExitProjection
  apply actual_original_actor_projection_membership O D
  intro actor
  simp only [canonicalDateActors,canonicalExitActors,Finset.mem_toList,afterExitActors,
    Finset.mem_filter,List.not_mem_nil,not_false_eq_true,and_true]
  rw [actual_original_gap_actor_role_set O D lower upper hlt hgap]

/-- No actual private bridge has opened before the first original date. -/
theorem actual_first_original_pre_exit_actor_set_empty (O : Source.{u,v,w} X)
    {T : Source X} (D : Decoration O T) :
    beforeExitActors T (firstOriginalDate O.network O.calendar) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro actor hm
  have hp := (Finset.mem_filter.mp hm).2.1
  have hb : firstOriginalDate O.network O.calendar ≤ O.calendar.age (D.vertex (T.network.graph.target actor.val)) :=
    firstOriginalDate_le O.network O.calendar _
  rw [←D.calendar] at hb
  exact (not_lt_of_ge hb) hp

#print axioms actual_original_gap_same_runtime_projection
#print axioms actual_first_original_pre_exit_actor_set_empty
end G1CanonicalOriginalDateGapRoles
