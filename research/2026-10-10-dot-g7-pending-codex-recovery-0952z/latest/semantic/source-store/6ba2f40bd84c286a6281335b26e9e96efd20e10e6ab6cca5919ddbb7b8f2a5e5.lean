import UnifiedLean.Source.OriginalFixedIDControls

/-!
# Actual ORIGINAL-mask controlled complete unranked source projectivity

Contributor: dot, 2026-10-02. Finishes the bounded original-control adapter to
G2: same source/registry/parameters, legal fixed original-ID partial routing
mask, actual CURRENT-owner endpoints, full graph-generated agenda, ancestral
completion, and EVERY selected copy panel. The original natural register is
retained; a forced node bypasses its unused natural coin. No new actuator,
posterior refitting or desired cross-source terminal-law field is supplied.
-/
namespace UnifiedLean.Source.ControlledUnrankedSourceProjectivity
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest Filter
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceEventualCompletionLimit
open UnifiedLean.Source.SourceNaturalCompletedLimit
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierNatural
open UnifiedLean.Source.SourceUnrankedCopyProjectivity
open UnifiedLean.Source.SourceUnrankedAllPanels
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.OriginalFixedIDControls
open scoped Classical BigOperators NNReal Topology
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def controlledCalendarLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    sourceProgram N r (controlledCalendarProgram N C H p common mask) (initialCode N sample register))

lemma controlled_calendar_ancestral_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) {d : Code N sample}
    (hd : d ∈ (controlledCalendarLaw N C sample H p common r mask).support) : AncestralRoot N d := by
  obtain ⟨register,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact initialized_original_calendar_ancestral_support N C sample register H
    (controlledGamma p mask) (controlledMode common mask) r hdr

noncomputable def controlledAfterRoot (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) (t : ℝ≥0) : PMF (Code N sample) :=
  (controlledCalendarLaw N C sample H p common r mask).bind (sourceTimeKernel N r t)

noncomputable def controlledCompletedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) : PMF (Code N sample) :=
  (controlledCalendarLaw N C sample H p common r mask).bind (completionKernel N r)

noncomputable def controlledCompletedUnrankedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) : PMF (Finset (UnrankedTree Copy)) :=
  (controlledCompletedLaw N C sample H p common r mask).map
    (fun s => sourceUnrankedForest (state s) Finset.univ)

/-- Generic finite source-entry transport, immediately instantiated with the
DERIVED actual controlled-calendar root support. No limiting law is assumed. -/
lemma root_entry_completion_limit [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (law : PMF (Code N sample))
    (hroot : ∀ s ∈ law.support, AncestralRoot N s) (d : Code N sample) :
    Tendsto (fun t : ℝ≥0 => ((law.bind (sourceTimeKernel N r t)) d).toReal) atTop
      (𝓝 ((law.bind (completionKernel N r)) d).toReal) := by
  simp only [bind_probability_real,tsum_fintype]
  apply tendsto_finsetSum
  intro s _
  by_cases hs : s ∈ law.support
  · exact (actual_ancestral_kernel_tendsto_completion N r s d (hroot s hs)).const_mul _
  · have hz : law s = 0 := by simpa only [PMF.mem_support_iff,not_not] using hs
    simp only [hz,ENNReal.toReal_zero,zero_mul]
    exact tendsto_const_nhds

/-- The actual controlled graph-generated calendar has the SAME derived
ancestral completion limit; endpoint controls do not insert a law premise. -/
theorem controlled_source_tendsto_completed [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) (d : Code N sample) :
    Tendsto (fun t : ℝ≥0 => (controlledAfterRoot N C sample H p common r mask t d).toReal) atTop
      (𝓝 (controlledCompletedLaw N C sample H p common r mask d).toReal) :=
  root_entry_completion_limit N r _
    (fun s hs => controlled_calendar_ancestral_support N C sample H p common r mask hs) d

lemma controlled_after_root_program (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (mask : OriginalMask N) (t : ℝ≥0) :
    controlledAfterRoot N C sample H p common r mask t =
      (originalRegisterPMF N p).bind (fun register =>
        sourceProgram N r (controlledCalendarProgram N C H p common mask ++ [.interval t])
          (initialCode N sample register)) := by
  simp only [controlledAfterRoot,controlledCalendarLaw,PMF.bind_bind,sourceProgram_append,
    sourceProgram,sourceProgramStep,PMF.bind_pure]

/-- Each legal original forcing mask has actual full/small source-time law,
with the SAME original source parameters and once-drawn register prior. -/
theorem actual_controlled_after_root_cross_carrier (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (mask : OriginalMask N) (t : ℝ≥0) :
    (controlledAfterRoot N C sample H p common r mask t).map
      (fun d => joinedProjection N keep (.inl d)) =
    (controlledAfterRoot N C (selectedSample sample keep) H p common r mask t).map
      (fun d => joinedProjection N keep (.inr d)) := by
  rw [controlled_after_root_program,controlled_after_root_program]
  exact original_initialized_register_program_law N sample keep p r _

lemma controlled_completed_cross_carrier (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy) (hk : keep.Nonempty)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (mask : OriginalMask N) :
    (controlledCompletedLaw N C sample H p common r mask).map
      (fun d => joinedProjection N keep (.inl d)) =
    (controlledCompletedLaw N C (selectedSample sample keep) H p common r mask).map
      (fun d => joinedProjection N keep (.inr d)) := by
  obtain ⟨x,hx⟩ := hk
  letI : Nonempty Copy := ⟨x⟩
  letI : Nonempty (SelectedCopy keep) := ⟨⟨x,hx⟩⟩
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hf := finite_pmf_observer_limit
    (controlledAfterRoot N C sample H p common r mask) (controlledCompletedLaw N C sample H p common r mask)
    (fun d => joinedProjection N keep (.inl d))
    (controlled_source_tendsto_completed N C sample H p common r mask) v
  have hz := finite_pmf_observer_limit
    (controlledAfterRoot N C (selectedSample sample keep) H p common r mask)
    (controlledCompletedLaw N C (selectedSample sample keep) H p common r mask)
    (fun d => joinedProjection N keep (.inr d))
    (controlled_source_tendsto_completed N C (selectedSample sample keep) H p common r mask) v
  have he : ∀ t : ℝ≥0,
      (((controlledAfterRoot N C sample H p common r mask t).map
        (fun d => joinedProjection N keep (.inl d))) v).toReal =
      (((controlledAfterRoot N C (selectedSample sample keep) H p common r mask t).map
        (fun d => joinedProjection N keep (.inr d))) v).toReal := by
    intro t
    exact congrArg (fun q : PMF (JoinedIndex N sample keep) => (q v).toReal)
      (actual_controlled_after_root_cross_carrier N C sample keep H p common r mask t)
  exact tendsto_nhds_unique (hf.congr' (Eventually.of_forall he)) hz

/-- Complete actual G2 same-source rooted UNRANKED projectivity, for EVERY
selected original panel and EVERY legal partial/full ORIGINAL-ID forcing row.
Natural gamma, source/rates/calendar/registry and unforced COMMON registers
are preserved. No per-tip actuator or assumed response-law equality is added. -/
theorem actual_controlled_complete_unranked_all_panel_projectivity (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (keep : Finset Copy)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (mask : OriginalMask N) :
    (controlledCompletedLaw N C sample H p common r mask).map
      (fun s => sourceUnrankedForest (state s) keep) =
    (controlledCompletedUnrankedLaw N C (selectedSample sample keep) H p common r mask).map
      (fun F => F.image (mapUnranked Subtype.val)) := by
  by_cases hk : keep.Nonempty
  · have h := congrArg (fun law : PMF (JoinedIndex N sample keep) =>
        law.map (fun v => unrankedForest v.val))
      (controlled_completed_cross_carrier N C sample keep hk H p common r mask)
    simp only [PMF.map_comp,Function.comp_def,joinedProjection,joinedView] at h
    simp_rw [actual_small_unranked_label_lift] at h
    rw [controlledCompletedUnrankedLaw,PMF.map_comp]
    exact h
  · have he : keep = ∅ := Finset.not_nonempty_iff_eq_empty.mp hk
    subst keep
    letI : IsEmpty (SelectedCopy (∅ : Finset Copy)) := ⟨fun x => Finset.notMem_empty _ x.property⟩
    rw [controlledCompletedUnrankedLaw,PMF.map_comp]
    simp only [Function.comp_def,original_empty_panel_forest,no_copy_unranked_forest,Finset.image_empty]
    exact (PMF.map_const _ _).trans (PMF.map_const _ _).symm

/-- The legal-control theorem includes the original natural law EXACTLY when
no original site is forced, not by replacing it with an invented experiment. -/
theorem empty_mask_completed_original_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    controlledCompletedLaw N C sample H p common r (fun _ => none) =
      naturalCompletedLaw N C sample H p common r := by
  simp only [controlledCompletedLaw,controlledCalendarLaw,empty_mask_original_calendar,
    naturalCompletedLaw,naturalCalendarLaw]
  rfl

#print axioms controlled_calendar_ancestral_support
#print axioms controlled_source_tendsto_completed
#print axioms actual_controlled_after_root_cross_carrier
#print axioms actual_controlled_complete_unranked_all_panel_projectivity
#print axioms empty_mask_completed_original_law
end UnifiedLean.Source.ControlledUnrankedSourceProjectivity
