import G7CompletedUnrankedRelabelling
import UnifiedLean.Source.ControlledUnrankedSourceProjectivity

/-! Original-ID masks under graph relabelling. Reuses the inherited actual
forcing compiler; the natural parameter bank is not refitted. Contributor: dot. -/
namespace GProgram.G7.OriginalControlRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceCompletedUnrankedTree UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open GProgram.G7.OriginalRelabelling GProgram.G7.CalendarNodeRelabelling
open GProgram.G7.NaturalCalendarRelabelling GProgram.G7.NaturalWordRelabelling
open GProgram.G7.SnapshotRelabelling GProgram.G7.CompletedUnrankedRelabelling
open scoped Classical
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

/-- The same original hybrid and parent bit, transported once for every row. -/
def mask (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (a : OriginalMask N) : OriginalMask (network N v e) :=
  fun h => a ((hybrids N v e).symm h)

@[simp] theorem mask_id (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (a : OriginalMask N) (h : Hybrid N) : mask N v e a (hybrids N v e h) = a h := by
  simp [mask]

/-- A user-facing original ID keeps the same assignment and parent bit in
all rows; only its graph-side registry representative is relabelled. -/
theorem named_mask {ID : Type*} (N : RootedBinary V E X)
    (v : V ≃ W) (e : E ≃ F) (ids : ID ≃ Hybrid N) (a : ID → Option Bool) :
    mask N v e (fun h => a (ids.symm h)) =
      fun h => a ((ids.trans (hybrids N v e)).symm h) := rfl

theorem controlled_gamma (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (p : HybridProbabilities N) (a : OriginalMask N) :
    gamma N v e (controlledGamma p a) =
      controlledGamma (inheritance N v e p) (mask N v e a) := by
  funext h
  unfold gamma controlledGamma mask
  cases a ((hybrids N v e).symm h) <;> rfl

theorem controlled_mode (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Hybrid N → Bool) (a : OriginalMask N) :
    common N v e (controlledMode c a) =
      controlledMode (common N v e c) (mask N v e a) := by
  funext h
  unfold common controlledMode mask
  cases a ((hybrids N v e).symm h) <;> rfl

theorem controlled_calendar (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E)
    (a : OriginalMask N) :
    (controlledCalendarLaw N C sample H p c r a).map (code N v e) =
      controlledCalendarLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) (mask N v e a) := by
  unfold controlledCalendarLaw controlledCalendarProgram
  rw [initialized_word]
  congr 1
  funext reg
  rw [compiled_agenda,controlled_gamma,controlled_mode]

theorem controlled_completed (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E)
    (a : OriginalMask N) :
    (controlledCompletedLaw N C sample H p c r a).map (code N v e) =
      controlledCompletedLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) (mask N v e a) := by
  unfold controlledCompletedLaw
  rw [PMF.map_bind]
  simp_rw [completion_kernel]
  change (controlledCalendarLaw N C sample H p c r a).bind
    (completionKernel (network N v e) (rates e r) ∘ code N v e) = _
  rw [← PMF.bind_map,controlled_calendar]

theorem controlled_completed_unranked (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (c : Hybrid N → Bool) (r : PositivePairRates E)
    (a : OriginalMask N) :
    controlledCompletedUnrankedLaw N C sample H p c r a =
      controlledCompletedUnrankedLaw (network N v e) (calendar N v e C) sample (registry N v e H)
        (inheritance N v e p) (common N v e c) (rates e r) (mask N v e a) := by
  unfold controlledCompletedUnrankedLaw
  rw [← controlled_completed N v e C sample H p c r a,PMF.map_comp]
  congr 1

#print axioms mask_id
#print axioms named_mask
#print axioms controlled_gamma
#print axioms controlled_mode
#print axioms controlled_calendar
#print axioms controlled_completed
#print axioms controlled_completed_unranked
end GProgram.G7.OriginalControlRelabelling
