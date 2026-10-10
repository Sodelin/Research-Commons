import G7SinglePopulationPolynomialKernel

/-!
Codex coordinator, 10 October 2026. Candidate source composition awaiting its
own kernel receipt. Reuses the unchanged original arbitrary-copy population
polynomial; it does not replace that theorem or assert a global G6 master.

For the SAME original source, entering code and physical population, equal
survival/exposure implies equality of the ENTIRE retained-state epoch PMF.
The reader and entering prior may retain arbitrary old genealogies/registers.
No independence of that prior is assumed. This does not transport between
different population names/graphs, build positive compressed chains or certify
chronological observations containing internal merger times.
-/

namespace GProgram.G6.OriginalPopulationExposure

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.G6.AncestralRateFree
open GProgram.G7.SinglePopulationPolynomialKernel
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Full retained-state equality, rather than equality of counts or survival.
Every other source rate may differ between the two positive rate banks. -/
theorem original_epoch_eq_of_survival_eq
    (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r rhat : PositivePairRates E) (t that : ℝ≥0)
    (h : Real.exp (-(pairRate r i) * (t : ℝ)) =
      Real.exp (-(pairRate rhat i) * (that : ℝ))) :
    sourceTimeKernel N r t s = sourceTimeKernel N rhat that s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [← actual_population_polynomial N s d i hs r t,
    ← actual_population_polynomial N s d i hs rhat that, h]

/-- Changing the duration and its one positive population rate together is
exact when their physical exposures agree, uniformly over all entering codes. -/
theorem original_epoch_eq_of_exposure_eq
    (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r rhat : PositivePairRates E) (t that : ℝ≥0)
    (h : pairRate r i * (t : ℝ) = pairRate rhat i * (that : ℝ)) :
    sourceTimeKernel N r t s = sourceTimeKernel N rhat that s := by
  apply original_epoch_eq_of_survival_eq N s i hs r rhat t that
  congr 1
  calc
    -(pairRate r i) * (t : ℝ) = -(pairRate r i * (t : ℝ)) := by ring
    _ = -(pairRate rhat i * (that : ℝ)) := congrArg (fun z : ℝ => -z) h
    _ = -(pairRate rhat i) * (that : ℝ) := by ring

/-- Every deterministic reader of the same retained code inherits the identity.
The reader is supplied; no cross-source or timed-history decoder is inferred. -/
theorem original_epoch_reader_eq_of_exposure_eq
    (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r rhat : PositivePairRates E) (t that : ℝ≥0)
    (h : pairRate r i * (t : ℝ) = pairRate rhat i * (that : ℝ))
    {Readout : Type*} (readout : Code N sample → Readout) :
    PMF.map readout (sourceTimeKernel N r t s) =
      PMF.map readout (sourceTimeKernel N rhat that s) := by
  exact congrArg (PMF.map readout)
    (original_epoch_eq_of_exposure_eq N s i hs r rhat t that h)

/-- One arbitrary entering prior can correlate all old subtrees and register
bits. Integrating the full conditional rows introduces no exterior independence. -/
theorem original_epoch_entering_mixture_eq_of_exposure_eq
    (N : RootedBinary V E X) {sample : Copy → X} (i : Option E)
    (prior : PMF {s : Code N sample // CoLocated N s i})
    (r rhat : PositivePairRates E) (t that : ℝ≥0)
    (h : pairRate r i * (t : ℝ) = pairRate rhat i * (that : ℝ)) :
    PMF.bind prior (fun s => sourceTimeKernel N r t s.val) =
      PMF.bind prior (fun s => sourceTimeKernel N rhat that s.val) := by
  apply congrArg (PMF.bind prior)
  funext s
  exact original_epoch_eq_of_exposure_eq N s.val i s.property r rhat t that h

end GProgram.G6.OriginalPopulationExposure

#print axioms GProgram.G6.OriginalPopulationExposure.original_epoch_eq_of_survival_eq
#print axioms GProgram.G6.OriginalPopulationExposure.original_epoch_eq_of_exposure_eq
#print axioms GProgram.G6.OriginalPopulationExposure.original_epoch_reader_eq_of_exposure_eq
#print axioms GProgram.G6.OriginalPopulationExposure.original_epoch_entering_mixture_eq_of_exposure_eq
