import G5ActualTripleMoments

/-!
# Exact five-partition reconstruction from four actual source moments

Contributor: dot, 2026-10-09. Verification is recorded by the packet's exact-byte build and owned-declaration audit receipt.
The linear step uses only normalization and the three pair-discreteness
events plus the all-three-discrete atom. It retains second mergers.
-/
namespace GProgram.G5.TripleMomentReconstruction
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G5.TriplePartitionReadout
open GProgram.G5.ActualTripleMoments
open scoped Classical BigOperators ENNReal

noncomputable def partitionPair01 (g : Fin 5) : Bool := decide (g = 0 ∨ g = 2 ∨ g = 3)
noncomputable def partitionPair02 (g : Fin 5) : Bool := decide (g = 0 ∨ g = 1 ∨ g = 3)
noncomputable def partitionPair12 (g : Fin 5) : Bool := decide (g = 0 ∨ g = 1 ∨ g = 2)

lemma five_pmf_real_sum (mu : PMF (Fin 5)) :
    (mu 0).toReal + (mu 1).toReal + (mu 2).toReal +
      (mu 3).toReal + (mu 4).toReal = 1 := by
  have h : ∑ i : Fin 5, (mu i).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun i _ => PMF.apply_ne_top mu i)]
    have he : (∑ i : Fin 5, mu i) = 1 := by
      simpa only [tsum_fintype] using mu.tsum_coe
    rw [he, ENNReal.toReal_one]
  simpa [Fin.sum_univ_succ, add_assoc] using h

lemma five_pmf_pair01 (mu : PMF (Fin 5)) :
    ((mu.map partitionPair01) true).toReal =
      (mu 0).toReal + (mu 2).toReal + (mu 3).toReal := by
  simp [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, partitionPair01,
    ENNReal.toReal_add, PMF.apply_ne_top, add_assoc]

lemma five_pmf_pair02 (mu : PMF (Fin 5)) :
    ((mu.map partitionPair02) true).toReal =
      (mu 0).toReal + (mu 1).toReal + (mu 3).toReal := by
  simp [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, partitionPair02,
    ENNReal.toReal_add, PMF.apply_ne_top, add_assoc]

lemma five_pmf_pair12 (mu : PMF (Fin 5)) :
    ((mu.map partitionPair12) true).toReal =
      (mu 0).toReal + (mu 1).toReal + (mu 2).toReal := by
  simp [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ, partitionPair12,
    ENNReal.toReal_add, PMF.apply_ne_top, add_assoc]

/-- The five masses are uniquely determined by the four actual events. -/
theorem five_mass_unique (p q : Fin 5 → ℝ)
    (hp : p 0 + p 1 + p 2 + p 3 + p 4 = 1)
    (hq : q 0 + q 1 + q 2 + q 3 + q 4 = 1)
    (hd : p 0 = q 0)
    (h01 : p 0 + p 2 + p 3 = q 0 + q 2 + q 3)
    (h02 : p 0 + p 1 + p 3 = q 0 + q 1 + q 3)
    (h12 : p 0 + p 1 + p 2 = q 0 + q 1 + q 2) :
    p = q := by
  funext g
  fin_cases g
  · change p 0 = q 0; exact hd
  · change p 1 = q 1; linarith
  · change p 2 = q 2; linarith
  · change p 3 = q 3; linarith
  · change p 4 = q 4; linarith

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma actual_partition_discrete_readout (N : RootedBinary V E X)
    {sample : Fin 3 → X} (s : Code N sample) :
    decide (actualTriplePartition N s = 0) = tripleDistinct N s := by
  unfold actualTriplePartition tripleDistinct
  congr 1
  exact propext (ancestor_partition_zero _)

lemma actual_partition_pair01_readout (N : RootedBinary V E X)
    {sample : Fin 3 → X} (s : Code N sample) :
    partitionPair01 (actualTriplePartition N s) = pairDistinct N 0 1 s := by
  unfold partitionPair01 pairDistinct actualTriplePartition
  congr 1
  exact propext (ancestor_partition_pair01 _).symm

lemma actual_partition_pair02_readout (N : RootedBinary V E X)
    {sample : Fin 3 → X} (s : Code N sample) :
    partitionPair02 (actualTriplePartition N s) = pairDistinct N 0 2 s := by
  unfold partitionPair02 pairDistinct actualTriplePartition
  congr 1
  exact propext (ancestor_partition_pair02 _).symm

lemma actual_partition_pair12_readout (N : RootedBinary V E X)
    {sample : Fin 3 → X} (s : Code N sample) :
    partitionPair12 (actualTriplePartition N s) = pairDistinct N 1 2 s := by
  unfold partitionPair12 pairDistinct actualTriplePartition
  congr 1
  exact propext (ancestor_partition_pair12 _).symm

#print axioms five_pmf_real_sum
#print axioms five_pmf_pair01
#print axioms five_pmf_pair02
#print axioms five_pmf_pair12
#print axioms five_mass_unique
#print axioms actual_partition_discrete_readout
#print axioms actual_partition_pair01_readout
#print axioms actual_partition_pair02_readout
#print axioms actual_partition_pair12_readout
end GProgram.G5.TripleMomentReconstruction

