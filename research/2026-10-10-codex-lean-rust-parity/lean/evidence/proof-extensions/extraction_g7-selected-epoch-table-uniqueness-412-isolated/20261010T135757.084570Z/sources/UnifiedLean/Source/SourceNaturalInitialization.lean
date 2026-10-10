import UnifiedLean.Source.SourceInitializedCalendar
import UnifiedLean.Source.NativeIndependentPairMixture

/-!
# Natural original-site initialization and unconditional calendar kernel

Contributor: dot, 2026-10-02. Reuses the existing strict ORIGINAL hybrid
probability assignment. A real independent original-site Bernoulli product
constructs latent shared registers once; CURRENT independent pulses use the
same original parameters freshly at their actual node. The unconditional
initialized calendar PMF and selected transport are constructed, rather than
assuming a desired marginal/source law. Unused registers remain latent; this
adds no observation/control menu. Ancestral completion and full holding-clock
path/unranked/timed observation equivalence remain further source obligations.
-/
namespace UnifiedLean.Source.SourceNaturalInitialization
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.UniformizedSourceStep
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Same strict original parameter assignment, with true = original parent1
as in the native source coin construction; no orientation silently changes. -/
noncomputable def originalGamma {N : RootedBinary V E X} (p : HybridProbabilities N)
    (h : Hybrid N) : unitInterval := ⟨p.gamma h,⟨(p.positive h).le,(p.below_one h).le⟩⟩

noncomputable def originalRegisterMeasure (N : RootedBinary V E X) (p : HybridProbabilities N) :
    Measure (Hybrid N → Bool) := Measure.pi (fun h => bitMeasure (originalGamma p h))

instance originalRegister_probability (N : RootedBinary V E X) (p : HybridProbabilities N) :
    IsProbabilityMeasure (originalRegisterMeasure N p) := by
  unfold originalRegisterMeasure
  infer_instance

/-- One register per actual original hybrid, reused by COMMON; nonhybrid
register slots are the inert false convention and are never independent coins. -/
noncomputable def originalRegister (N : RootedBinary V E X) (coin : Hybrid N → Bool) : V → Bool :=
  fun v => if hh : N.graph.IsHybrid v then coin ⟨v,hh⟩ else false

noncomputable def originalRegisterPMF (N : RootedBinary V E X) (p : HybridProbabilities N) : PMF (V → Bool) :=
  (originalRegisterMeasure N p).toPMF.map (originalRegister N)

/-- Natural full-copy calendar kernel conditional operations are assembled
with their SAME original-site parameter assignment and a once-drawn register. -/
noncomputable def naturalCalendarLaw (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) common)
      (initialCode N sample register))

noncomputable def naturalSelectedCalendarLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (keep : Finset Copy) : PMF (SelectedIndex N sample keep) :=
  (originalRegisterPMF N p).bind (fun register =>
    selectedProgram N r keep (compiledCalendarProgram N C H (originalGamma p) common)
      (projection N keep (initialCode N sample register)))

/-- Unconditional whole selected-state law preserves ORIGINAL shared coupling
and natural CURRENT-root independent routing for all finite sample assignments. -/
theorem actual_natural_calendar_projection (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy) :
    (naturalCalendarLaw N C sample H p common r).map (projection N keep) =
      naturalSelectedCalendarLaw N C sample H p common r keep := by
  rw [naturalCalendarLaw,naturalSelectedCalendarLaw,PMF.map_bind]
  simp_rw [actual_source_program_projection]

/-- Natural register marginalization retains the derived complete initialized
physical-calendar support; all copies reach the same ORIGINAL ancestral root. -/
theorem natural_calendar_ancestral_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (naturalCalendarLaw N C sample H p common r).support) :
    ∀ x : Copy, copyLocation (state d) x = .rootPopulation N.root := by
  obtain ⟨register,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact initialized_original_calendar_ancestral_support N C sample register H (originalGamma p) common r hdr

/-- Arbitrary selected-state endpoint map is a derived probability transport,
not an assumed biological measurement/observed-law identification. -/
theorem natural_calendar_endpoint_probability {Obs : Type*}
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (keep : Finset Copy) (readout : SelectedIndex N sample keep → Obs) :
    (naturalCalendarLaw N C sample H p common r).map (readout ∘ projection N keep) =
      (naturalSelectedCalendarLaw N C sample H p common r keep).map readout := by
  rw [← PMF.map_comp,actual_natural_calendar_projection]

#print axioms originalRegisterPMF
#print axioms actual_natural_calendar_projection
#print axioms natural_calendar_ancestral_support
#print axioms natural_calendar_endpoint_probability
end UnifiedLean.Source.SourceNaturalInitialization
