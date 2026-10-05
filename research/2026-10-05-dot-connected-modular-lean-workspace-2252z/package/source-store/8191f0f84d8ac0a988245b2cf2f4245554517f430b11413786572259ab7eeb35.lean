import G1OriginalHistoryQuotient

/-! Repeated K macros preserve EVERY original agenda exterior checkpoint,
including its original descendant-labelled opaque trees/populations/Γ, joint
with all later phase histories and the final causal interface. -/
namespace G1RepeatedOriginalExteriorHistoryMacros
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open G1ActualJointProgram G1ActualJointStageHistory
open G1UnrankedSourceView G1UnrankedActualFuture G1OriginalWholeCausalView
open G1OriginalOpaqueExteriorView G1OriginalExteriorHistoryProduct
open G1ActualHistoryEnrichedKMacro G1OriginalHistoryQuotient
open G1SourceMacroComposition G1UnrankedExteriorHistoryKInsertion
open scoped Classical
variable {V E X Copy Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The fixed ORIGINAL-copy exterior cohort is physically classified by the
initial current roots. This prevents hidden survivor IDs from changing the
observed exterior panel. Canonical source admission derives this condition. -/
structure OriginalHistoryPlan (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (observedOutside : Finset Copy)
    (s : Code N sample) where
  physical : PhysicalMacroPlan N sample r phase s
  cohort : originalExteriorCopies (state s) physical.outside = observedOutside

noncomputable def admittedHistoryRow (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (observedOutside : Finset Copy)
    (planner : (s : Code N sample) → Option (OriginalHistoryPlan N sample r phase observedOutside s))
    (s : Code N sample) : PMF (List (UnrankedView V E Copy) × Code N sample) :=
  match planner s with
  | none => originalObservedPhaseRow N r phase observedOutside s
  | some a => sourceKHistoryMacro N r a.physical.inside a.physical.outside phase s a.physical.inside_live

theorem actual_admitted_history_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (observedOutside : Finset Copy)
    (planner : (s : Code N sample) → Option (OriginalHistoryPlan N sample r phase observedOutside s))
    (s : Code N sample) :
    (admittedHistoryRow N r phase observedOutside planner s).map (historyFinalView N) =
      (originalObservedPhaseRow N r phase observedOutside s).map (historyFinalView N) := by
  unfold admittedHistoryRow
  cases h : planner s with
  | none => rfl
  | some a =>
    change (sourceKHistoryMacro N r a.physical.inside a.physical.outside phase s a.physical.inside_live).map
      (fun v => (v.1,wholeOriginalView N v.2)) = _
    have ha := actual_history_enriched_K_macro_row N r a.physical.inside a.physical.outside
      a.physical.exitPopulation phase s a.physical.inside_live a.physical.partition
      a.physical.separated a.physical.physical
    simpa only [originalObservedPhaseRow,PMF.map_comp,Function.comp_def,historyFinalView,
      originalExteriorHistory,exteriorHistory,a.cohort] using ha

theorem actual_admitted_history_end_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (observedOutside : Finset Copy)
    (planner : (s : Code N sample) → Option (OriginalHistoryPlan N sample r phase observedOutside s))
    (s : Code N sample) {out : List (UnrankedView V E Copy) × Code N sample}
    (hout : out ∈ (admittedHistoryRow N r phase observedOutside planner s).support) :
    out.2 ∈ (sourceProgram N r phase s).support := by
  unfold admittedHistoryRow at hout
  cases h : planner s with
  | none =>
    have hp : out ∈ (originalObservedPhaseRow N r phase observedOutside s).support := by simpa [h] using hout
    obtain ⟨tr,ht,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    exact real_history_end_support N r phase s tr ht
  | some a =>
    exact actual_history_enriched_K_macro_support N r a.physical.inside a.physical.outside phase s
      a.physical.inside_live a.physical.separated (by simpa [h] using hout)

structure OriginalHistoryStage (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) where
  phase : List (ProgramStep N)
  observedOutside : Finset Copy
  planner : (s : Code N sample) → Option (OriginalHistoryPlan N sample r phase observedOutside s)

abbrev FullExteriorHistory (V E Copy Obs : Type*) := List (List (UnrankedView V E Copy)) × Obs

def prependPhaseHistory (tr : List (UnrankedView V E Copy)) (h : FullExteriorHistory V E Copy Obs) :
    FullExteriorHistory V E Copy Obs := (tr::h.1,h.2)

noncomputable def actualOriginalHistoryRun (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs) :
    List (OriginalHistoryStage N sample r) → Code N sample → PMF (FullExteriorHistory V E Copy Obs)
  | [],s => (terminal (wholeOriginalView N s)).map (fun o => ([],o))
  | a::as,s => (originalObservedPhaseRow N r a.phase a.observedOutside s).bind
      (fun out => (actualOriginalHistoryRun N r terminal as out.2).map (prependPhaseHistory out.1))

noncomputable def historyEnrichedMacroRun (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs) :
    List (OriginalHistoryStage N sample r) → Code N sample → PMF (FullExteriorHistory V E Copy Obs)
  | [],s => (terminal (wholeOriginalView N s)).map (fun o => ([],o))
  | a::as,s => (admittedHistoryRow N r a.phase a.observedOutside a.planner s).bind
      (fun out => (historyEnrichedMacroRun N r terminal as out.2).map (prependPhaseHistory out.1))

theorem actual_original_history_run_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs)
    (stages : List (OriginalHistoryStage N sample r)) (s z : Code N sample)
    (h : wholeOriginalView N s = wholeOriginalView N z) :
    actualOriginalHistoryRun N r terminal stages s = actualOriginalHistoryRun N r terminal stages z := by
  induction stages generalizing s z with
  | nil => simp only [actualOriginalHistoryRun,h]
  | cons a as ih =>
    rw [actualOriginalHistoryRun,actualOriginalHistoryRun]
    apply bind_through_equal_view ([],s) _ _ (historyFinalView N)
      (actual_original_observed_history_row_independent N r a.phase a.observedOutside s z h)
    intro d w hw
    change (d.1,wholeOriginalView N d.2) = (w.1,wholeOriginalView N w.2) at hw
    have hp : d.1 = w.1 := congrArg (fun v : List (UnrankedView V E Copy) × UnrankedView V E Copy => v.1) hw
    have hv : wholeOriginalView N d.2 = wholeOriginalView N w.2 :=
      congrArg (fun v : List (UnrankedView V E Copy) × UnrankedView V E Copy => v.2) hw
    rw [ih d.2 w.2 hv,hp]

/-- Every within-phase ORIGINAL exterior checkpoint remains JOINT across all
source-derived K macro stages and their terminal quotient continuation. No
history is replaced by an endpoint-only or independently resampled marginal. -/
theorem actual_repeated_K_full_original_exterior_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs)
    (stages : List (OriginalHistoryStage N sample r)) (s : Code N sample) :
    historyEnrichedMacroRun N r terminal stages s = actualOriginalHistoryRun N r terminal stages s := by
  induction stages generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [historyEnrichedMacroRun,actualOriginalHistoryRun]
    simp_rw [ih]
    apply bind_through_equal_view ([],s) _ _ (historyFinalView N)
      (actual_admitted_history_row N r a.phase a.observedOutside a.planner s)
    intro d w hw
    change (d.1,wholeOriginalView N d.2) = (w.1,wholeOriginalView N w.2) at hw
    have hp : d.1 = w.1 := congrArg (fun v : List (UnrankedView V E Copy) × UnrankedView V E Copy => v.1) hw
    have hv : wholeOriginalView N d.2 = wholeOriginalView N w.2 :=
      congrArg (fun v : List (UnrankedView V E Copy) × UnrankedView V E Copy => v.2) hw
    rw [actual_original_history_run_row_independent N r terminal as d.2 w.2 hv,hp]

theorem actual_correlated_entering_full_exterior_history {History : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (terminal : History → UnrankedView V E Copy → PMF Obs)
    (stages : List (OriginalHistoryStage N sample r)) (prior : PMF (Code N sample × History)) :
    prior.bind (fun c => (historyEnrichedMacroRun N r (terminal c.2) stages c.1).map (fun h => (c.2,h))) =
      prior.bind (fun c => (actualOriginalHistoryRun N r (terminal c.2) stages c.1).map (fun h => (c.2,h))) := by
  congr 1
  funext c
  rw [actual_repeated_K_full_original_exterior_history]

#print axioms actual_repeated_K_full_original_exterior_history
#print axioms actual_correlated_entering_full_exterior_history
end G1RepeatedOriginalExteriorHistoryMacros
