import UnifiedLean.Source.SourceNaturalInitialization
import UnifiedLean.Source.SourceActualHoldingClocks

/-!
# Positive selected-singleton mass in the actual initialized original program

Contributor: Codex integration G5 lane, 2026-10-08.

dot integration derivative, 2026-10-09: compatibility-only proof-script
repairs; theorem statements and source semantics are unchanged. The original
draft label below is preserved as history. Current verification is governed
by this packet's exact-byte build and full owned-declaration audit receipt.
STATUS: SOURCE DRAFT / COMPILER UNCHECKED. No compiler was run by this lane.

This discharges a bounded part of G5-B: the finite original program has a
strictly positive selected-singleton event, with the actual original register
prior and current-owner boundary kernels. The proof constructs a supported
no-real-merger branch through every interval and any supported boundary row.
It does not identify the program endpoint with the original physical path at
an arbitrary interior calendar time, classify every feasible original route,
or derive the five-partition conditional right germ.

The event reads only the pruned genealogy in the latent selected view. It
does not require the full carrier to have three roots or prohibit unselected
mergers. The stronger branch used to prove positivity has no real merger in
the full carrier; this is a witness inside the selected event, not a claim
that the two conditioning events are equal.
-/
namespace GProgram.G5.OriginalProgramSurvival
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Exact singleton original-label pruned genealogies. Population labels,
registers and the rest of the full forest are unrestricted. -/
def SingletonSelected (keep : Finset Copy) (v : SelectedView V E Copy) : Prop :=
  ∀ x ∈ keep, v.genealogy x = some (.leaf x)

/-- Actual original initialization supplies the event, for repeated sampled
species as well as injective taxon panels. Only COPY labels are distinct. -/
theorem actual_initial_singleton_selected (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) (register : V → Bool) :
    SingletonSelected keep (selectedView (state (initialCode N sample register)) keep) := by
  have hview := decode_encode_selectedView N.root (initial N sample register)
    (initial_valid N sample register) keep
  change SingletonSelected keep (selectedView (decodeSnapshot N.root
    (encodeSnapshot (initial N sample register) (initial_valid N sample register))) keep)
  rw [hview]
  intro x hx
  simp [selectedView, selectedGenealogy, initial, Genealogy.prune, hx]

/-- Every supported actual zero-time original boundary preserves the entire
selected genealogy. INDEPENDENT coins belong to the current AtNode owners. -/
theorem actual_boundary_selected_genealogy (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N)
    (s d : Code N sample) (hd : d ∈ (boundaryKernel N op s).support) :
    (selectedView (state d) keep).genealogy = (selectedView (state s) keep).genealogy := by
  cases op with
  | exit e =>
      have he : d = exitCode N s e := by
        simpa only [boundaryKernel, PMF.mem_support_pure_iff] using hd
      subst d
      rw [exitCode_view]
      rfl
  | ordinary e degree =>
      have he : d = ordinaryCode N s e := by
        simpa only [boundaryKernel, PMF.mem_support_pure_iff] using hd
      subst d
      rw [ordinaryCode_view]
      rfl
  | root =>
      have he : d = rootCode N s := by
        simpa only [boundaryKernel, PMF.mem_support_pure_iff] using hd
      subst d
      rw [rootCode_view]
      rfl
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa only [boundaryKernel, PMF.mem_support_pure_iff] using hd
      subst d
      rw [pulseCode_view]
      rfl
  | independent H gamma =>
      change d ∈ ((currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
        (pulseCode H s)).support at hd
      obtain ⟨coin, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      subst d
      rw [pulseCode_view]
      rfl

theorem actual_boundary_singleton_selected (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N)
    (s d : Code N sample) (hd : d ∈ (boundaryKernel N op s).support)
    (hs : SingletonSelected keep (selectedView (state s) keep)) :
    SingletonSelected keep (selectedView (state d) keep) := by
  intro x hx
  rw [actual_boundary_selected_genealogy N keep op s d hd]
  exact hs x hx

/-- The actual current total rate supplies a strictly positive self row.
This reuses the accepted exact survival formula; no rate floor is imposed. -/
theorem actual_epoch_self_in_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    s ∈ (sourceTimeKernel N r t s).support := by
  have hp : 0 < (sourceTimeKernel N r t s s).toReal := by
    rw [actual_source_kernel_no_merger]
    exact Real.exp_pos _
  apply (PMF.mem_support_iff _ _).mpr
  intro hz
  rw [hz, ENNReal.toReal_zero] at hp
  exact (lt_irrefl 0) hp

/-- A supported selected-singleton branch is constructed by induction on
the ACTUAL program bind recurrence, with no supplied entering/source law. -/
theorem actual_program_singleton_witness (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (hs : SingletonSelected keep (selectedView (state s) keep)) :
    ∃ d, d ∈ (sourceProgram N r ops s).support ∧
      SingletonSelected keep (selectedView (state d) keep) := by
  induction ops generalizing s with
  | nil => exact ⟨s, by simp [sourceProgram], hs⟩
  | cons op ops ih =>
      have hstep : ∃ d, d ∈ (sourceProgramStep N r op s).support ∧
          SingletonSelected keep (selectedView (state d) keep) := by
        cases op with
        | interval t => exact ⟨s, actual_epoch_self_in_support N r t s, hs⟩
        | boundary b =>
            obtain ⟨d, hd⟩ := (boundaryKernel N b s).support_nonempty
            exact ⟨d, hd, actual_boundary_singleton_selected N keep b s d hd hs⟩
      obtain ⟨d, hd, hds⟩ := hstep
      obtain ⟨z, hz, hzs⟩ := ih d hds
      refine ⟨z, ?_, hzs⟩
      change z ∈ ((sourceProgramStep N r op s).bind (sourceProgram N r ops)).support
      exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨d, hd, hz⟩

/-- SAME original graph, copy sample, once-drawn register and original rates.
Operations may be the actual retained calendar prefix or ancestral tail. -/
noncomputable def originalProgramLaw (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    sourceProgram N r ops (initialCode N sample register))

theorem actual_initialized_program_singleton_witness (N : RootedBinary V E X)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset Copy) (ops : List (ProgramStep N)) :
    ∃ d, d ∈ (originalProgramLaw N sample p r ops).support ∧
      SingletonSelected keep (selectedView (state d) keep) := by
  obtain ⟨register, hr⟩ := (originalRegisterPMF N p).support_nonempty
  obtain ⟨d, hd, hds⟩ := actual_program_singleton_witness N r keep ops
    (initialCode N sample register) (actual_initial_singleton_selected N sample keep register)
  exact ⟨d, (PMF.mem_support_bind_iff _ _ _).mpr ⟨register, hr, hd⟩, hds⟩

/-- One original copy at every original taxon is a genuine full-X starting
source, rather than a new experiment on ancestral representatives. -/
theorem actual_original_X_program_singleton_witness [DecidableEq X]
    (N : RootedBinary V E X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (keep : Finset X) (ops : List (ProgramStep N)) :
    ∃ d, d ∈ (originalProgramLaw N (id : X → X) p r ops).support ∧
      SingletonSelected keep (selectedView (state d) keep) :=
  actual_initialized_program_singleton_witness N id p r keep ops

#print axioms actual_initial_singleton_selected
#print axioms actual_boundary_selected_genealogy
#print axioms actual_boundary_singleton_selected
#print axioms actual_epoch_self_in_support
#print axioms actual_program_singleton_witness
#print axioms actual_initialized_program_singleton_witness
#print axioms actual_original_X_program_singleton_witness
end GProgram.G5.OriginalProgramSurvival
