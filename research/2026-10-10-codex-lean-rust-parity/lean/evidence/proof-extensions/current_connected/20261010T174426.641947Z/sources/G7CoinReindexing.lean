import G7OriginalRelabelling
import UnifiedLean.Source.SourceBoundaryKernels
import UnifiedLean.Source.SourceNaturalInitialization

/-!
Actual original-coin product measures under finite registry/current-owner
bijections. Contributor: dot, 2026-10-09. Uses the existing source Bernoulli
measures; equality of desired source kernels is not a premise.
-/
namespace GProgram.G7.CoinReindexing
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open GProgram.G7.OriginalRelabelling
open scoped Classical

variable {A B : Type*} [Fintype A] [Fintype B]
def coinTransport (e : A ≃ B) (c : A → Bool) : B → Bool := fun b => c (e.symm b)

theorem current_coin_measure (e : A ≃ B) (gamma : unitInterval) :
    MeasurePreserving (coinTransport e) (independentCoinMeasure A gamma)
      (independentCoinMeasure B gamma) := by
  have h := measurePreserving_piCongrLeft (fun _ : B => bitMeasure gamma) e
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : B => Bool) e)) = coinTransport e := by
    funext c b
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,coinTransport]
  rw [he] at h
  exact h

theorem current_coin_pmf (e : A ≃ B) (gamma : unitInterval) :
    (currentCoinPMF A gamma).map (coinTransport e) = currentCoinPMF B gamma := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (coinTransport e) (currentCoinPMF A gamma) (current_coin_measure e gamma).measurable]
  simp only [currentCoinPMF,Measure.toPMF_toMeasure]
  exact (current_coin_measure e gamma).map_eq

variable {V E W F X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]

theorem original_gamma_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (p : HybridProbabilities N) (h : Hybrid N) :
    originalGamma (inheritance N v e p) ((hybrids N v e) h) = originalGamma p h := by
  apply Subtype.ext
  exact inheritance_preserved N v e p h

/-- The same original-site parameter vector is transported jointly, before
COMMON registers are drawn. Parameters are not selected separately per row. -/
theorem original_coin_measure (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (p : HybridProbabilities N) :
    MeasurePreserving (coinTransport (hybrids N v e)) (originalRegisterMeasure N p)
      (originalRegisterMeasure (network N v e) (inheritance N v e p)) := by
  have h := measurePreserving_piCongrLeft
    (fun h : Hybrid (network N v e) => bitMeasure (originalGamma (inheritance N v e p) h))
    (hybrids N v e)
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Hybrid (network N v e) => Bool)
      (hybrids N v e))) = coinTransport (hybrids N v e) := by
    funext c b
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,coinTransport]
  rw [he] at h
  simp only [original_gamma_preserved] at h
  exact h

#print axioms current_coin_pmf
#print axioms original_coin_measure
end GProgram.G7.CoinReindexing
