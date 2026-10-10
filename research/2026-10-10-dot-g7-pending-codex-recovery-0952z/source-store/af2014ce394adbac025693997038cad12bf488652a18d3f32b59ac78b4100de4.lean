import G7OriginalEdgeGathering

/-! Literal graph/calendar compiler binding for the all-original-edge gathering
algorithm. No symbolic-word equality or generator identity is a premise.
Candidate: uncompiled, dot 2026-10-10. -/
namespace GProgram.G7.ActualCalendarGathering
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourcePoissonExponential
open GProgram.G7.OriginalEdgeOperators GProgram.G7.OriginalEdgeBoundary
open GProgram.G7.OriginalEdgeGathering
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def instantiateEvent (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : Event V E → ProgramStep N
  | .interval t => .interval t
  | .exit e => .boundary (.exit e)
  | .node v => .boundary (originalNodeOperation N H gamma common v)

lemma actual_event_matrix (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (op : Event V E)
    (s d : Code N sample) :
    (sourceProgramStep N r (instantiateEvent N H gamma common op) s d).toReal =
      eventMatrix N H gamma common r op s d := by
  cases op with
  | interval t => exact actual_source_epoch_exponential_sum N r t s d
  | exit e => rfl
  | node v => rfl

/-- Entire actual finite source program, before the gathering transformation. -/
theorem actual_event_word_matrix (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (ops : List (Event V E))
    (s d : Code N sample) :
    (sourceProgram N r (ops.map (instantiateEvent N H gamma common)) s d).toReal =
      ((ops.map (eventMatrix N H gamma common r)).prod) s d := by
  induction ops generalizing s with
  | nil =>
    simp [sourceProgram,PMF.pure_apply,Matrix.one_apply,eq_comm]
  | cons op ops ih =>
    rw [List.map_cons,sourceProgram,bind_probability_real,tsum_fintype]
    simp only [List.map_cons,List.prod_cons,Matrix.mul_apply,ih,actual_event_matrix]

noncomputable def boundaryEvents (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) : List (Event V E) :=
  ((Finset.univ.filter (fun e : E => C.age (N.graph.source e)=a)).toList.map Event.exit) ++
  ((Finset.univ.filter (fun v : V => C.age v=a)).toList.map Event.node)

noncomputable def tailEvents (N : RootedBinary V E X) (C : Calendar N.graph) : ℝ → List ℝ → List (Event V E)
  | _,[] => []
  | a,b::bs => .interval (Real.toNNReal (b-a)) :: (boundaryEvents N C b ++ tailEvents N C b bs)

noncomputable def calendarEvents (N : RootedBinary V E X) (C : Calendar N.graph) : List (Event V E) :=
  match sortedOriginalDates N C with
  | [] => []
  | a::as => boundaryEvents N C a ++ tailEvents N C a as

lemma boundaryEvents_instantiates (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) :
    (boundaryEvents N C a).map (instantiateEvent N H gamma common) = boundaryOperations N C H gamma common a := by
  simp [boundaryEvents,boundaryOperations,List.map_append,List.map_map,Function.comp_def,instantiateEvent]

lemma tailEvents_instantiates (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dates : List ℝ) (a : ℝ) :
    (tailEvents N C a dates).map (instantiateEvent N H gamma common) = calendarTail N C H gamma common a dates := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [tailEvents,calendarTail,List.map_cons,List.map_append,
      instantiateEvent,boundaryEvents_instantiates,ih]

theorem actual_generated_calendar_word (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) :
    (calendarEvents N C).map (instantiateEvent N H gamma common) = compiledCalendarProgram N C H gamma common := by
  unfold calendarEvents compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => rfl
  | cons a dates => rw [List.map_append,boundaryEvents_instantiates,tailEvents_instantiates]

/-- Source-level whole-calendar gathering, conditional on its SAME original
register. The remaining elapsed-time telescope is about these generated IDs,
not a supplied symbolic law or an independently re-fitted probability table. -/
theorem actual_initialized_calendar_gathering (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (d : Code N sample) :
    (sourceProgram N r (compiledCalendarProgram N C H gamma common)
      (UnifiedLean.Source.SourceInitializedCalendar.initialCode N sample register) d).toReal =
      (initialRow N sample register *
        (((gather N r (calendarEvents N C)).2).map (gatheredMatrix N H gamma common)).prod) () d := by
  rw [←actual_generated_calendar_word,actual_event_word_matrix]
  have h := congrArg (fun M : Matrix Unit (Code N sample) ℝ => M () d)
    (initialized_entire_word_gathering N sample register H gamma common r (calendarEvents N C))
  simpa [Matrix.mul_apply,initialRow] using h

/-- The actual natural register distribution is integrated once. For forcing,
use controlledGamma/controlledMode in the conditional result while retaining
this natural originalRegisterPMF, as in the accepted controlled calendar law. -/
theorem actual_natural_calendar_gathering (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (d : Code N sample) :
    (naturalCalendarLaw N C sample H p common r d).toReal =
      ∑ register : V → Bool, (originalRegisterPMF N p register).toReal *
        (initialRow N sample register *
          (((gather N r (calendarEvents N C)).2).map
            (gatheredMatrix N H (originalGamma p) common)).prod) () d := by
  rw [naturalCalendarLaw,bind_probability_real,tsum_fintype]
  apply Finset.sum_congr rfl
  intro register _
  rw [actual_initialized_calendar_gathering]

end GProgram.G7.ActualCalendarGathering
