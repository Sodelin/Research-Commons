import G1PrivateActorLifetimeAdmission

/-! All actors opening at one original date are admitted at the REAL original
BEFORE-node-batch frontier: all original exits finish, all opens occur, then
the original node operations keep their exact order. A closing cut still
closes immediately after its literal original exit. -/
namespace G1CanonicalBatchOpeningCalendar
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1TaggedOriginalCalendar G1CanonicalActorLifecycleCompiler
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def compileAfterOpening (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) :
    OriginalEvent O → List (ActorInstruction O T)
  | .interval a b => [.epoch a b]
  | event =>
      (match eventActor O H D hD event with
        | none => [ActorInstruction.baseBoundary event]
        | some actor => [ActorInstruction.privateBoundary actor event]) ++
      (closingActor O H D hD event).toList.map ActorInstruction.close

noncomputable def batchOpenings (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) :=
  (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList.flatMap
    (fun v => (openingActor O H D hD (.node v)).toList.map (ActorInstruction.open (O := O)))

noncomputable def batchActorInstructions (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) (date : ℝ) :
    List (ActorInstruction O T) :=
  (Finset.univ.filter (fun e : O.Edge => O.calendar.age (O.network.graph.source e) = date)).toList.flatMap
    (fun e => compileAfterOpening O H D hD (.exit e)) ++
  batchOpenings O H D hD date ++
  (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList.flatMap
    (fun v => compileAfterOpening O H D hD (.node v))

noncomputable def batchActorTail (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) :
    ℝ → List ℝ → List (ActorInstruction O T)
  | _,[] => []
  | a,b::bs => .epoch a b :: (batchActorInstructions O H D hD b ++ batchActorTail O H D hD b bs)

noncomputable def batchActorCalendar (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D) : List (ActorInstruction O T) :=
  match sortedOriginalDates O.network O.calendar with
  | [] => []
  | a::as => batchActorInstructions O H D hD a ++ batchActorTail O H D hD a as

lemma actual_after_opening_event_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (event : OriginalEvent O) :
    (compileAfterOpening O H D hD event).flatMap (eraseInstruction O H gamma common) = [eraseEvent O H gamma common event] := by
  cases event with
  | interval a b => rfl
  | node v =>
      simp only [compileAfterOpening]
      cases eventActor O H D hD (.node v) <;> simp [closingActor,eraseInstruction]
  | exit e =>
      simp only [compileAfterOpening]
      cases eventActor O H D hD (.exit e) <;> cases closingActor O H D hD (.exit e) <;> simp [eraseInstruction]

lemma actual_batch_opening_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (date : ℝ) :
    (batchOpenings O H D hD date).flatMap (eraseInstruction O H gamma common) = [] := by
  unfold batchOpenings
  rw [List.flatMap_assoc]
  apply List.flatMap_eq_nil_iff.mpr
  intro v hv
  cases openingActor O H D hD (.node v) <;> simp [eraseInstruction]

lemma actual_batch_actor_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (date : ℝ) :
    (batchActorInstructions O H D hD date).flatMap (eraseInstruction O H gamma common) =
      boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) date := by
  simp only [batchActorInstructions,List.flatMap_append,actual_batch_opening_erasure,List.append_nil,List.flatMap_assoc]
  simp_rw [actual_after_opening_event_erasure]
  simp only [eraseEvent]
  have hE := List.flatMap_pure_eq_map
    (fun e : O.Edge => (ProgramStep.boundary (.exit e) : ProgramStep O.network))
    (Finset.univ.filter (fun e : O.Edge => O.calendar.age (O.network.graph.source e) = date)).toList
  have hV := List.flatMap_pure_eq_map
    (fun v : O.Vertex => (ProgramStep.boundary (originalNodeOperation O.network H (fun h => gamma h.val) (fun h => common h.val) v) : ProgramStep O.network))
    (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList
  change (Finset.univ.filter (fun e : O.Edge => O.calendar.age (O.network.graph.source e) = date)).toList.flatMap
    (fun e => [ProgramStep.boundary (.exit e)]) = _ at hE
  change (Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = date)).toList.flatMap
    (fun v => [ProgramStep.boundary (originalNodeOperation O.network H (fun h => gamma h.val) (fun h => common h.val) v)]) = _ at hV
  rw [hE,hV]
  rfl

lemma actual_batch_actor_tail_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (dates : List ℝ) (a : ℝ) :
    (batchActorTail O H D hD a dates).flatMap (eraseInstruction O H gamma common) =
      calendarTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
      simp only [batchActorTail,List.flatMap_cons,eraseInstruction,List.singleton_append,List.flatMap_append,calendarTail]
      rw [actual_batch_actor_erasure,ih]

/-- Arbitrary-many/coincident-date literal source binding, with all openings
at the exact real frontier used by the canonical TRUE-current-root K theorem.
Pending stochastic coordinate execution is a separate source obligation. -/
theorem actual_full_batch_actor_calendar_erasure (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source.{u,v,w} X} (D : Decoration O T) (hD : Originated O H D)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) :
    (batchActorCalendar O H D hD).flatMap (eraseInstruction O H gamma common) =
      compiledCalendarProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) := by
  unfold batchActorCalendar compiledCalendarProgram
  cases sortedOriginalDates O.network O.calendar with
  | nil => rfl
  | cons a as => rw [List.flatMap_append,actual_batch_actor_erasure,actual_batch_actor_tail_erasure]

#print axioms actual_full_batch_actor_calendar_erasure
end G1CanonicalBatchOpeningCalendar
