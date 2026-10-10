import G1WholeCanonicalPrivateWordTrueK

/-! Literal cuts of the ACTUAL history-carrying runtime calendar. The entire
old boundary/epoch program is decomposed before any kernel is promoted. This
binds source-derived opening/closing positions to concrete execution lists. -/
namespace G1OriginalRuntimeCalendarCuts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1UnrankedSourceView
open G1CanonicalOriginalEpochAsync G1CanonicalOriginalAdjacentRecordedRow
open G1CanonicalWholeCalendarRecordedSuffix G1CanonicalInitializedWholeCalendarHistory
open G1ActualOriginalBoundaryRootHistory G1PendingBaseCheckpointRecorder
open G1PendingOriginalRootBlobCheckpointHistory G1PendingActorInterfaceCommutation
open G1CanonicalThreeEpochList G1OriginalCalendarDecomposition
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def recordedEpochBlock (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X) (r : PositivePairRates O.Edge)
    (lower upper : ℝ) := recordedBlock (pendingRootBlobObservation O)
      (canonicalEpochAsyncOps O D sample r lower (Real.toNNReal (upper-lower)))

noncomputable def recordedRuntimeTail (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) :
    ℝ → List ℝ → List (AsyncOperation (BridgeActor T) (UnrankedView O.Vertex O.Edge Copy)
      (UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)))
  | _,[] => []
  | lower,next::later => recordedEpochBlock O D sample r lower next ++
      canonicalRecordedBoundaryOps O H D hD sample gamma common r next ++
      recordedRuntimeTail O H D hD sample gamma common r next later

noncomputable def stoppedRuntimeTail (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (stop : ℝ) :
    ℝ → List ℝ → List (AsyncOperation (BridgeActor T) (UnrankedView O.Vertex O.Edge Copy)
      (UnrankedView O.Vertex O.Edge Copy × List (UnrankedView O.Vertex O.Edge Copy)))
  | _,[] => []
  | lower,next::later => if next = stop then recordedEpochBlock O D sample r lower next else
      recordedEpochBlock O D sample r lower next ++ canonicalRecordedBoundaryOps O H D hD sample gamma common r next ++
      stoppedRuntimeTail O H D hD sample gamma common r stop next later

noncomputable def beforeRuntimeBoundary (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (stop : ℝ) :=
  match sortedOriginalDates O.network O.calendar with
  | [] => []
  | date::dates => if date = stop then [] else canonicalRecordedBoundaryOps O H D hD sample gamma common r date ++
      stoppedRuntimeTail O H D hD sample gamma common r stop date dates

lemma actual_recorded_runtime_suffix_tail (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge) (date : ℝ) (dates : List ℝ) :
    canonicalRecordedCalendarSuffix O H D hD sample gamma common r date dates =
      canonicalRecordedBoundaryOps O H D hD sample gamma common r date ++
      recordedRuntimeTail O H D hD sample gamma common r date dates := by
  induction dates generalizing date with
  | nil => simp [canonicalRecordedCalendarSuffix,recordedRuntimeTail]
  | cons next dates ih =>
    simp only [canonicalRecordedCalendarSuffix,canonicalRecordedBoundaryEpochOps,recordedRuntimeTail,recordedEpochBlock]
    rw [ih]
    simp only [List.append_assoc]

theorem actual_recorded_runtime_tail_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (dates : List ℝ) (ho : dates.Pairwise (· < ·)) (stop : ℝ) (hm : stop ∈ dates) (lower : ℝ) :
    recordedRuntimeTail O H D hD sample gamma common r lower dates =
      stoppedRuntimeTail O H D hD sample gamma common r stop lower dates ++
      canonicalRecordedBoundaryOps O H D hD sample gamma common r stop ++
      recordedRuntimeTail O H D hD sample gamma common r stop (dates.filter (fun date => decide (stop < date))) := by
  induction dates generalizing lower with
  | nil => exact False.elim (List.not_mem_nil hm)
  | cons next dates ih =>
    have hp := List.pairwise_cons.mp ho
    by_cases hn : next = stop
    · subst next
      rw [filter_after_head hp.1]
      simp [recordedRuntimeTail,stoppedRuntimeTail]
    · have hs : stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hn)
      have hlt := hp.1 _ hs
      have hf : (next::dates).filter (fun date => decide (stop < date)) = dates.filter (fun date => decide (stop < date)) :=
        by simp [not_lt_of_gt hlt]
      rw [hf]
      simp only [recordedRuntimeTail,stoppedRuntimeTail,if_neg hn]
      rw [ih hp.2 hs next]
      simp only [List.append_assoc]

/-- Concrete whole runtime list, cut at an actual ORIGINAL date. This is a
derived list identity and contains no caller-supplied stochastic row. -/
theorem actual_whole_recorded_runtime_date_cut (O : Source.{u,v,w} X) (H : OriginalParentRegistry O.network)
    {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] (sample : Copy → X)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (stop : ℝ) (hm : stop ∈ sortedOriginalDates O.network O.calendar) :
    canonicalRecordedWholeCalendarOps O H D hD sample gamma common r =
      beforeRuntimeBoundary O H D hD sample gamma common r stop ++
      canonicalRecordedBoundaryOps O H D hD sample gamma common r stop ++
      recordedRuntimeTail O H D hD sample gamma common r stop (afterDate O.network O.calendar stop) := by
  have hne : sortedOriginalDates O.network O.calendar ≠ [] := by
    intro he; rw [he] at hm; exact List.not_mem_nil hm
  obtain ⟨date,dates,he⟩ := List.exists_cons_of_ne_nil hne
  have ho := original_dates_strict O.network O.calendar
  rw [he] at ho hm
  have hp := List.pairwise_cons.mp ho
  unfold canonicalRecordedWholeCalendarOps beforeRuntimeBoundary
  rw [he]
  dsimp only
  rw [actual_recorded_runtime_suffix_tail]
  by_cases hd : date = stop
  · subst date
    simp [afterDate,he,filter_after_head hp.1]
  · have hs : stop ∈ dates := (List.mem_cons.mp hm).resolve_left (Ne.symm hd)
    have hlt := hp.1 _ hs
    rw [if_neg hd,actual_recorded_runtime_tail_cut O H D hD sample gamma common r dates hp.2 stop hs date]
    simp [afterDate,he,not_lt_of_gt hlt,List.append_assoc]

#print axioms actual_whole_recorded_runtime_date_cut
end G1OriginalRuntimeCalendarCuts
