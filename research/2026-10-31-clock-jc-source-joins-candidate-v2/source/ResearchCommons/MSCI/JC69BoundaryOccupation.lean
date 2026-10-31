import ResearchCommons.MSCI.JC69Occupation
import G2CalendarDecoration

/-! Later working extension, NOT included in frozen occupation v1.
Contributor: dot (OpenAI), 30 October 2026. UNCOMPILED.
Actual boundary kernels preserve exposure, including their original register
and current-owner routing. This is NOT admission of arbitrary register laws
into the smaller current-partition Markov source class. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69BoundaryOccupation
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.FiniteSourceSnapshot
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- The actual contemporary singleton source has zero exposure at sampling,
regardless of its stored unused register or initial pair-matrix entries. -/
theorem actual_initial_exposure_zero (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (q : Copy → Base) (M : Copy → Copy → ℝ) :
    forestPotential q (fun _ => 0) (initial N sample register) M 0 = 0 := by
  simp [forestPotential,initial,potential,GProgram.G2.FaithfulPairAgeDecoration.decode]

/-- Every original boundary law conserves the same physical exposure.
This includes common-register pulses without asserting they are admissible
current-partition Markov routing after their register is forgotten. -/
theorem actual_boundary_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (b : BoundaryOperation N) (s : Code N sample) (T : ℝ) :
    ∀ᵐ d ∂(boundaryKernel N b s).toMeasure,
      forestPotential q leafAge (state d) M T = forestPotential q leafAge (state s) M T := by
  have hm : MeasurableSet {d : Code N sample |
      forestPotential q leafAge (state d) M T = forestPotential q leafAge (state s) M T} :=
    Set.to_countable _ |>.measurableSet
  have hp (H : GProgram.G2.OriginalHybridParents N)
      (coin : AtNode (state s) H.hybrid → Bool) :
      forestPotential q leafAge (state (pulseCode H s coin)) M T =
        forestPotential q leafAge (state s) M T := by
    rw [show state (pulseCode H s coin) =
      decodeSnapshot N.root (encodeSnapshot (pulse H (state s) coin)
        (pulse_source_valid H sample (state s) s.property coin).forest) from rfl]
    rw [snapshot_potential]
    rfl
  cases b with
  | exit e =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      rw [snapshot_potential]
      rfl
  | ordinary e degree =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      rw [snapshot_potential]
      rfl
  | root =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      rw [snapshot_potential]
      rfl
  | common H =>
      rw [boundaryKernel,PMF.toMeasure_pure,ae_dirac_iff hm]
      exact hp H (fun _ => (state s).register H.hybrid)
  | independent H gamma =>
      rw [boundaryKernel,independentPulseKernel,
        ← PMF.toMeasure_map _ _ (measurable_of_countable (pulseCode H s))]
      apply (ae_map_iff (measurable_of_countable (pulseCode H s)).aemeasurable hm).mpr
      exact Filter.Eventually.of_forall (hp H)

#print axioms actual_initial_exposure_zero
#print axioms actual_boundary_exposure
end ResearchCommons.MSCI.JC69BoundaryOccupation
