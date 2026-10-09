import G5TriplePartitionReadout
import G5SelectedSingletonRates

/-!
# Four exact moments of the actual frozen triple source

Contributor: dot, 2026-10-09. SOURCE DRAFT / COMPILER UNCHECKED.
These are source theorems, not fitted moment assumptions. The pair readouts
come from actual selected-copy epoch transport; the triple readout uses the
actual three-copy catalogue. The clocks are those of the unchanged original
edge/root populations, and conditioning is only at the entering cut.
-/
namespace GProgram.G5.ActualTripleMoments
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G5.OriginalProgramSurvival
open GProgram.G5.SelectedSingletonCarrier
open GProgram.G5.SelectedDiscreteSurvival
open GProgram.G5.SelectedSingletonRates
open GProgram.G5.TriplePartitionReadout
open scoped Classical NNReal ENNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

noncomputable def pairDistinct (N : RootedBinary V E X) {sample : Fin 3 → X}
    (i j : Fin 3) (s : Code N sample) : Bool :=
  decide ((state s).ancestor i ≠ (state s).ancestor j)

noncomputable def tripleDistinct (N : RootedBinary V E X) {sample : Fin 3 → X}
    (s : Code N sample) : Bool :=
  decide (Function.Injective (state s).ancestor)

/-- Each pair's exact marginal survival, allowing the third root to merge
invisibly in the full carrier. -/
theorem actual_pair_distinct_survival (N : RootedBinary V E X)
    {sample : Fin 3 → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : Fin 3 → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (i j : Fin 3) (hij : i ≠ j) (t : ℝ≥0) :
    (((sourceTimeKernel N r t s).map (pairDistinct N i j)) true).toReal =
      Real.exp (-(coincidentPairRate r (place i) (place j) * (t : ℝ))) := by
  have h := actual_selected_discrete_survival N r {i,j} s
    (actual_all_singleton_restrict N s hs {i,j}) t
  rw [PMF.map_comp, actual_selected_pair_rate N r s place hloc i j hij] at h
  have hf : (selectedDiscreteReadout N {i,j} ∘
      fun d : Code N sample => joinedProjection N {i,j} (.inl d)) =
      pairDistinct N i j := by
    funext d
    unfold selectedDiscreteReadout pairDistinct
    congr 1
    exact propext (actual_pair_discrete_view N d i j hij)
  rw [hf] at h
  exact h

/-- The all-three distinct mass uses all three original unordered pair clocks. -/
theorem actual_triple_distinct_survival (N : RootedBinary V E X)
    {sample : Fin 3 → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : Fin 3 → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (t : ℝ≥0) :
    (((sourceTimeKernel N r t s).map (tripleDistinct N)) true).toReal =
      Real.exp (-((coincidentPairRate r (place 0) (place 1) +
        coincidentPairRate r (place 0) (place 2) +
        coincidentPairRate r (place 1) (place 2)) * (t : ℝ))) := by
  have h := actual_selected_discrete_survival N r Finset.univ s hs t
  rw [PMF.map_comp, actual_selected_triple_rate N r s place hloc] at h
  have hf : (selectedDiscreteReadout N Finset.univ ∘
      fun d : Code N sample => joinedProjection N Finset.univ (.inl d)) =
      tripleDistinct N := by
    funext d
    unfold selectedDiscreteReadout tripleDistinct
    congr 1
    have he := actual_discrete_view_iff_injOn N d Finset.univ
    simpa only [Finset.coe_univ, Set.injOn_univ] using propext he
  rw [hf] at h
  exact h

#print axioms actual_pair_distinct_survival
#print axioms actual_triple_distinct_survival
end GProgram.G5.ActualTripleMoments

