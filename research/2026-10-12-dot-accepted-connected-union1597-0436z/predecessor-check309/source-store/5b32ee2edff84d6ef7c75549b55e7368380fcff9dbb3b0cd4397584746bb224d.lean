import UnifiedLean.Source.SourceUnrankedAllPanels

/-!
# Legal ORIGINAL-ID forcing masks in the actual source compiler

Contributor: dot, 2026-10-02. Ports the accepted G1/G2 §4 and G7 §3 control
contract: a partial assignment to actual ORIGINAL hybrid IDs overrides the
route of EVERY current live ancestor at that SAME node, regardless natural
C/I. No new site, per-tip actuator, graph/rate/gamma refitting or split of an
already merged ancestor is introduced. Unforced COMMON registers are retained.
-/
namespace UnifiedLean.Source.OriginalFixedIDControls
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory ProbabilityTheory
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical

/-- Boolean orientation is inherited: true selects ORIGINAL parent1. -/
def forcedParameter (b : Bool) : unitInterval := if b then 1 else 0

/-- Endpoint forcing is a genuine constant-current-owner PMF, including an
empty owner set. No deterministic pulse identity is assumed as a field. -/
theorem actual_forced_current_coin_pmf (Site : Type*) [Fintype Site] (b : Bool) :
    currentCoinPMF Site (forcedParameter b) = PMF.pure (fun _ : Site => b) := by
  have hμ : independentCoinMeasure Site (forcedParameter b) = Measure.dirac (fun _ : Site => b) := by
    apply Measure.ext_of_singleton
    intro coin
    rw [independentCoinMeasure,Measure.pi_singleton]
    cases b <;> simp [forcedParameter,bitMeasure,Measure.dirac_apply',Pi.single_apply,Fintype.prod_boole,funext_iff]
  apply PMF.toMeasure_injective
  rw [currentCoinPMF,Measure.toPMF_toMeasure,PMF.toMeasure_pure]
  exact hμ

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Every mask names only actual ORIGINAL hybrids from the source registry.
Finiteness follows from the supplied finite original graph, not a guessed cap. -/
abbrev OriginalMask (N : RootedBinary V E X) := Hybrid N → Option Bool

noncomputable def controlledGamma {N : RootedBinary V E X}
    (p : HybridProbabilities N) (mask : OriginalMask N) (h : Hybrid N) : unitInterval :=
  match mask h with
  | none => originalGamma p h
  | some b => forcedParameter b

noncomputable def controlledMode {N : RootedBinary V E X}
    (common : Hybrid N → Bool) (mask : OriginalMask N) (h : Hybrid N) : Bool :=
  match mask h with
  | none => common h
  | some _ => false

/-- Forcing bypasses that node's natural coin via its proved deterministic
endpoint pulse. The original source inheritance assignment p is not refitted. -/
noncomputable def controlledCalendarProgram (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (mask : OriginalMask N) :
    List (ProgramStep N) :=
  compiledCalendarProgram N C H (controlledGamma p mask) (controlledMode common mask)

lemma original_hybrid_not_root (N : RootedBinary V E X) (h : Hybrid N) : h.val ≠ N.root := by
  intro he
  have hh := h.property.1
  rw [he,N.root_degrees.1] at hh
  norm_num at hh

/-- Each forced original ID compiles to the actual SAME original hybrid's
constant-current-owner pulse, irrespective of its natural inheritance mode. -/
theorem original_forced_node_compiler (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (mask : OriginalMask N)
    (h : Hybrid N) (b : Bool) (hm : mask h = some b) :
    originalNodeOperation N H (controlledGamma p mask) (controlledMode common mask) h.val =
      .independent (H.parents h) (forcedParameter b) := by
  simp [originalNodeOperation,original_hybrid_not_root N h,h.property,controlledGamma,controlledMode,hm]

/-- Unforced original hybrid IDs retain their SAME natural mode/parameter,
including the original stored register for COMMON, not a fresh draw. -/
theorem original_unforced_node_compiler (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (mask : OriginalMask N)
    (h : Hybrid N) (hm : mask h = none) :
    originalNodeOperation N H (controlledGamma p mask) (controlledMode common mask) h.val =
      originalNodeOperation N H (originalGamma p) common h.val := by
  simp [originalNodeOperation,original_hybrid_not_root N h,h.property,controlledGamma,controlledMode,hm]

/-- Compiled forcing uses the already derived genuine PMF on ALL actual
CURRENT owners. Already coalesced original copies receive one route. -/
theorem actual_forced_hybrid_kernel {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (b : Bool) :
    boundaryKernel N (.independent H (forcedParameter b)) s =
      PMF.pure (pulseCode H s (fun _ => b)) := by
  rw [boundaryKernel,independentPulseKernel,actual_forced_current_coin_pmf,PMF.pure_map]

/-- Literal original current-owner parent route after actual source coding,
with parent bit orientation inherited from the original parent registry. -/
theorem actual_forced_owner_route {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (b : Bool)
    (a : AtNode (state s) H.hybrid) :
    copyLocation (state (pulseCode H s (fun _ => b))) a.val = .edge (H.parent b) := by
  rw [show copyLocation (state (pulseCode H s (fun _ => b))) a.val =
      copyLocation (pulse H (state s) (fun _ => b)) a.val from
    decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property _).forest a.val]
  have hrep : (state s).ancestor a.val = a.val := s.property.forest.representative a.val a.property.1
  change (pulse H (state s) (fun _ => b)).location ((state s).ancestor a.val) = _
  rw [hrep,pulse_routes_current_ancestor H (state s) (fun _ => b) a]

/-- Empty mask is EXACTLY the existing original natural graph calendar. -/
theorem empty_mask_original_calendar (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) :
    controlledCalendarProgram N C H p common (fun _ => none) =
      compiledCalendarProgram N C H (originalGamma p) common := by
  have hγ : controlledGamma p (fun _ => none) = originalGamma p := by funext h; rfl
  have hc : controlledMode common (fun _ => none) = common := by funext h; rfl
  rw [controlledCalendarProgram,hγ,hc]

#print axioms actual_forced_current_coin_pmf
#print axioms original_forced_node_compiler
#print axioms original_unforced_node_compiler
#print axioms actual_forced_hybrid_kernel
#print axioms actual_forced_owner_route
#print axioms empty_mask_original_calendar
end UnifiedLean.Source.OriginalFixedIDControls
