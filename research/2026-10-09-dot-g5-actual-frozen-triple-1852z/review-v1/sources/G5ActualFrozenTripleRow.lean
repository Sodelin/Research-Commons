import G5TripleMomentReconstruction

/-!
# Actual frozen triple source row, joined to the checked polynomial kernel

Contributor: dot, 2026-10-09. SOURCE DRAFT / COMPILER UNCHECKED.
The input is an actual admitted original source state with singleton genealogy
and active original populations. The complete five-partition law is derived
from actual pair/triple survival and normalization, including second mergers.
No formula for the desired source row is an input hypothesis.
-/
namespace GProgram.G5.ActualFrozenTripleRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G5.OriginalProgramSurvival
open GProgram.G5.SelectedSingletonRates
open GProgram.G5.TriplePartitionReadout
open GProgram.G5.ActualTripleMoments
open GProgram.G5.TripleMomentReconstruction
open GProgram.G5.FrozenTriplePolynomialKernel
open scoped Classical BigOperators NNReal ENNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- Rate of the unique nonsingleton population block, if any. For the separate
occupancy the positive value is unused by the row. -/
noncomputable def triplePopulationRate (r : PositivePairRates E)
    (place : Fin 3 → Option E) : ℝ :=
  if place 0 = place 1 then pairRate r (place 0)
  else if place 0 = place 2 then pairRate r (place 0)
  else pairRate r (place 1)

theorem triple_population_rate_positive (r : PositivePairRates E)
    (place : Fin 3 → Option E) : 0 < triplePopulationRate r place := by
  unfold triplePopulationRate
  split_ifs <;> exact pairRate_pos r _

lemma exp_three_clock (a t : ℝ) :
    Real.exp (-((a+a+a)*t)) = Real.exp (-(a*t)) ^ 3 := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma polynomial_discrete_clock (r : PositivePairRates E)
    (place : Fin 3 → Option E) (t : ℝ) :
    row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 0 =
      Real.exp (-((coincidentPairRate r (place 0) (place 1) + coincidentPairRate r (place 0) (place 2) + coincidentPairRate r (place 1) (place 2))*t)) := by
  by_cases h01 : place 0 = place 1 <;>
    by_cases h02 : place 0 = place 2 <;>
    by_cases h12 : place 1 = place 2 <;>
    simp_all [ancestorPartition, triplePopulationRate, coincidentPairRate,
      row, discrete3, pair3, together3, exp_three_clock] <;> ring

lemma polynomial_pair01_clock (r : PositivePairRates E)
    (place : Fin 3 → Option E) (t : ℝ) :
    row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 0 + row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 2 + row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 3 =
      Real.exp (-(coincidentPairRate r (place 0) (place 1)*t)) := by
  by_cases h01 : place 0 = place 1 <;>
    by_cases h02 : place 0 = place 2 <;>
    by_cases h12 : place 1 = place 2 <;>
    simp_all [ancestorPartition, triplePopulationRate, coincidentPairRate,
      row, discrete3, pair3, together3, exp_three_clock] <;> ring

lemma polynomial_pair02_clock (r : PositivePairRates E)
    (place : Fin 3 → Option E) (t : ℝ) :
    row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 0 + row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 1 + row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 3 =
      Real.exp (-(coincidentPairRate r (place 0) (place 2)*t)) := by
  by_cases h01 : place 0 = place 1 <;>
    by_cases h02 : place 0 = place 2 <;>
    by_cases h12 : place 1 = place 2 <;>
    simp_all [ancestorPartition, triplePopulationRate, coincidentPairRate,
      row, discrete3, pair3, together3, exp_three_clock] <;> ring

lemma polynomial_pair12_clock (r : PositivePairRates E)
    (place : Fin 3 → Option E) (t : ℝ) :
    row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 0 + row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 1 + row (Real.exp (-(triplePopulationRate r place*t))) (ancestorPartition place) 2 =
      Real.exp (-(coincidentPairRate r (place 1) (place 2)*t)) := by
  by_cases h01 : place 0 = place 1 <;>
    by_cases h02 : place 0 = place 2 <;>
    by_cases h12 : place 1 = place 2 <;>
    simp_all [ancestorPartition, triplePopulationRate, coincidentPairRate,
      row, discrete3, pair3, together3, exp_three_clock] <;> ring

/-- Entire five-partition ACTUAL source row. The same original rates, source
state and elapsed time occur on both sides; occupancy is a hidden parameter. -/
theorem actual_frozen_triple_row (N : RootedBinary V E X)
    {sample : Fin 3 → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : Fin 3 → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (t : ℝ≥0) (gene : Fin 5) :
    (((sourceTimeKernel N r t s).map (actualTriplePartition N)) gene).toReal =
      row (Real.exp (-(triplePopulationRate r place*(t : ℝ))))
        (ancestorPartition place) gene := by
  let mu := (sourceTimeKernel N r t s).map (actualTriplePartition N)
  let q := row (Real.exp (-(triplePopulationRate r place*(t : ℝ))))
    (ancestorPartition place)
  have hq : q 0 + q 1 + q 2 + q 3 + q 4 = 1 := by
    have h := row_sum (Real.exp (-(triplePopulationRate r place*(t : ℝ))))
      (ancestorPartition place)
    simpa [q, Fin.sum_univ_succ, add_assoc] using h
  have hd : (mu 0).toReal = q 0 := by
    have h := actual_triple_distinct_survival N r s hs place hloc t
    have hf : (fun d : Code N sample => decide (actualTriplePartition N d = 0)) =
        tripleDistinct N := by
      funext d; exact actual_partition_discrete_readout N d
    have hm : (mu.map (fun g => decide (g = 0))) true = mu 0 := by
      simp [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ]
    rw [← hm]
    change (((((sourceTimeKernel N r t s).map (actualTriplePartition N)).map
      (fun g => decide (g = 0))) true).toReal) = _
    rw [PMF.map_comp]
    change (((sourceTimeKernel N r t s).map
      (fun d => decide (actualTriplePartition N d = 0))) true).toReal = _
    rw [hf, h]
    exact (polynomial_discrete_clock r place (t : ℝ)).symm
  have h01 : (mu 0).toReal + (mu 2).toReal + (mu 3).toReal =
      q 0 + q 2 + q 3 := by
    rw [← five_pmf_pair01]
    change (((((sourceTimeKernel N r t s).map (actualTriplePartition N)).map
      partitionPair01) true).toReal) = _
    rw [PMF.map_comp]
    have hf : partitionPair01 ∘ actualTriplePartition N = pairDistinct N 0 1 := by
      funext d; exact actual_partition_pair01_readout N d
    rw [hf, actual_pair_distinct_survival N r s hs place hloc 0 1 (by decide) t]
    exact (polynomial_pair01_clock r place (t : ℝ)).symm
  have h02 : (mu 0).toReal + (mu 1).toReal + (mu 3).toReal =
      q 0 + q 1 + q 3 := by
    rw [← five_pmf_pair02]
    change (((((sourceTimeKernel N r t s).map (actualTriplePartition N)).map
      partitionPair02) true).toReal) = _
    rw [PMF.map_comp]
    have hf : partitionPair02 ∘ actualTriplePartition N = pairDistinct N 0 2 := by
      funext d; exact actual_partition_pair02_readout N d
    rw [hf, actual_pair_distinct_survival N r s hs place hloc 0 2 (by decide) t]
    exact (polynomial_pair02_clock r place (t : ℝ)).symm
  have h12 : (mu 0).toReal + (mu 1).toReal + (mu 2).toReal =
      q 0 + q 1 + q 2 := by
    rw [← five_pmf_pair12]
    change (((((sourceTimeKernel N r t s).map (actualTriplePartition N)).map
      partitionPair12) true).toReal) = _
    rw [PMF.map_comp]
    have hf : partitionPair12 ∘ actualTriplePartition N = pairDistinct N 1 2 := by
      funext d; exact actual_partition_pair12_readout N d
    rw [hf, actual_pair_distinct_survival N r s hs place hloc 1 2 (by decide) t]
    exact (polynomial_pair12_clock r place (t : ℝ)).symm
  exact congrFun (five_mass_unique (fun g => (mu g).toReal) q
    (five_pmf_real_sum mu) hq hd h01 h02 h12) gene

#print axioms triple_population_rate_positive
#print axioms polynomial_discrete_clock
#print axioms polynomial_pair01_clock
#print axioms polynomial_pair02_clock
#print axioms polynomial_pair12_clock
#print axioms actual_frozen_triple_row
end GProgram.G5.ActualFrozenTripleRow

