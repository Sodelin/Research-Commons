import G5ActualFrozenTripleRow
import G5OriginalSelectedPosterior
import G5FrozenTripleAnalyticSupport

/-!
# Actual finite-source posterior mixtures and the accepted analytic germ consumer

Contributor: dot, 2026-10-09. Verification is recorded by the packet's exact-byte build and owned-declaration audit receipt.
The seed carrier is the support of an actual PMF on admitted original-source
codes. Positive seed weights are derived from that PMF. Its future partition
law is derived from the actual source kernel and the source-bound triple row.
The finite-program selected-singleton posterior is then a concrete instance.

The remaining physical-time cut and structural route-support identifications
are stated separately; no equality of observed timed laws is assumed to be an
equality of an unrelated hidden posterior.
-/
namespace GProgram.G5.ActualPosteriorGerm
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourcePoissonExponential
open GProgram.G5.OriginalProgramSurvival
open GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.TriplePartitionReadout
open GProgram.G5.ActualFrozenTripleRow
open GProgram.G5.FrozenTriplePolynomialKernel
open GProgram.G5.FrozenTripleAnalyticSupport
open scoped Classical BigOperators NNReal ENNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

abbrev ActualSeed (N : RootedBinary V E X) {sample : Fin 3 → X}
    (mu : PMF (Code N sample)) := {s : Code N sample // s ∈ mu.support}

noncomputable def actualSeedWeight (N : RootedBinary V E X) {sample : Fin 3 → X}
    (mu : PMF (Code N sample)) (s : ActualSeed N mu) : ℝ := (mu s.val).toReal

theorem actual_seed_weight_positive (N : RootedBinary V E X)
    {sample : Fin 3 → X} (mu : PMF (Code N sample)) (s : ActualSeed N mu) :
    0 < actualSeedWeight N mu s :=
  ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp s.property) (PMF.apply_ne_top _ _)

/-- A source mixture, using its actual supported entering states. Population
assignments merely name their existing active original locations. -/
theorem actual_positive_source_mixture (N : RootedBinary V E X)
    {sample : Fin 3 → X} (r : PositivePairRates E) (mu : PMF (Code N sample))
    (hstart : ∀ s : ActualSeed N mu,
      SingletonSelected Finset.univ (selectedView (state s.val) Finset.univ))
    (place : ActualSeed N mu → Fin 3 → Option E)
    (hloc : ∀ s x, copyLocation (state s.val) x = originalPlace N (place s x))
    (t : ℝ≥0) (gene : Fin 5) :
    ((((mu.bind (sourceTimeKernel N r t)).map (actualTriplePartition N)) gene).toReal) =
      frozenMixture (actualSeedWeight N mu)
        (fun s => triplePopulationRate r (place s))
        (fun s => ancestorPartition (place s)) (t : ℝ) gene := by
  rw [PMF.map_bind, bind_probability_real, tsum_fintype]
  unfold frozenMixture mixture expParameter
  apply Finset.sum_congr_set mu.support
  · intro s hs
    rw [actual_frozen_triple_row N r s (hstart ⟨s,hs⟩) (place ⟨s,hs⟩)
      (hloc ⟨s,hs⟩) t gene]
    simp only [actualSeedWeight, neg_mul]
  · intro s hs
    have hz : mu s = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hs
    simp [hz]

/-- Concrete ORIGINAL finite-program code posterior, restricted to the
selected singleton event before any latent projection. -/
noncomputable def originalTripleCodePosterior (N : RootedBinary V E X)
    (sample : Fin 3 → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N)) : PMF (Code N sample) :=
  (originalProgramLaw N sample p r past).filter
    ((fun d => joinedProjection N Finset.univ (.inl d)) ⁻¹'
      selectedSingletonEvent N sample Finset.univ)
    (actual_full_code_event_witness N sample p r Finset.univ past)

theorem original_triple_posterior_starts_singleton (N : RootedBinary V E X)
    (sample : Fin 3 → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N))
    (s : ActualSeed N (originalTripleCodePosterior N sample p r past)) :
    SingletonSelected Finset.univ (selectedView (state s.val) Finset.univ) := by
  exact ((PMF.mem_support_filter_iff
    (actual_full_code_event_witness N sample p r Finset.univ past)).mp s.property).1

/-- Posterior weights come from one actual original source. They need not
factor across selected roots, routes, shared registers, or original hybrids. -/
theorem actual_original_posterior_mixture (N : RootedBinary V E X)
    (sample : Fin 3 → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (past : List (ProgramStep N))
    (place : ActualSeed N (originalTripleCodePosterior N sample p r past) → Fin 3 → Option E)
    (hloc : ∀ s x, copyLocation (state s.val) x = originalPlace N (place s x))
    (t : ℝ≥0) (gene : Fin 5) :
    (((((originalTripleCodePosterior N sample p r past).bind
      (sourceTimeKernel N r t)).map (actualTriplePartition N)) gene).toReal) =
      frozenMixture (actualSeedWeight N (originalTripleCodePosterior N sample p r past))
        (fun s => triplePopulationRate r (place s))
        (fun s => ancestorPartition (place s)) (t : ℝ) gene :=
  actual_positive_source_mixture N r _ (original_triple_posterior_starts_singleton
    N sample p r past) place hloc t gene

section TwoOriginalSources
variable {V' E' X' : Type*}
variable [DecidableEq V'] [DecidableEq E'] [Fintype V'] [Fintype E'] [Fintype X']

/-- The checked analytic support theorem now consumes genuine actual source
future laws on two possibly different original graphs. The equality premise
is a genealogy-partition germ, not a hidden-population or posterior equation. -/
theorem actual_source_occupancy_support_of_right_germ
    (N : RootedBinary V E X) (N' : RootedBinary V' E' X')
    {sample : Fin 3 → X} {sample' : Fin 3 → X'}
    (r : PositivePairRates E) (r' : PositivePairRates E')
    (mu : PMF (Code N sample)) (nu : PMF (Code N' sample'))
    (hstart : ∀ s : ActualSeed N mu,
      SingletonSelected Finset.univ (selectedView (state s.val) Finset.univ))
    (hstart' : ∀ s : ActualSeed N' nu,
      SingletonSelected Finset.univ (selectedView (state s.val) Finset.univ))
    (place : ActualSeed N mu → Fin 3 → Option E)
    (place' : ActualSeed N' nu → Fin 3 → Option E')
    (hloc : ∀ s x, copyLocation (state s.val) x = originalPlace N (place s x))
    (hloc' : ∀ s x, copyLocation (state s.val) x = originalPlace N' (place' s x))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hgerm : ∀ gene (t : ℝ≥0), (t : ℝ) < epsilon →
      ((((mu.bind (sourceTimeKernel N r t)).map (actualTriplePartition N)) gene).toReal) =
      ((((nu.bind (sourceTimeKernel N' r' t)).map (actualTriplePartition N')) gene).toReal)) :
    ∀ gene, (∃ s : ActualSeed N mu, ancestorPartition (place s) = gene) ↔
      ∃ s : ActualSeed N' nu, ancestorPartition (place' s) = gene := by
  apply occupancy_support_eq_of_right_germ
    (actualSeedWeight N mu) (fun s => triplePopulationRate r (place s))
    (fun s => ancestorPartition (place s))
    (actualSeedWeight N' nu) (fun s => triplePopulationRate r' (place' s))
    (fun s => ancestorPartition (place' s))
    (actual_seed_weight_positive N mu) (actual_seed_weight_positive N' nu)
    (fun s => triple_population_rate_positive r (place s))
    (fun s => triple_population_rate_positive r' (place' s)) hepsilon
  intro gene u hu huE
  have hleft := actual_positive_source_mixture N r mu hstart place hloc ⟨u,hu⟩ gene
  have hright := actual_positive_source_mixture N' r' nu hstart' place' hloc' ⟨u,hu⟩ gene
  exact hleft.symm.trans ((hgerm gene ⟨u,hu⟩ huE).trans hright)

end TwoOriginalSources

#print axioms actual_seed_weight_positive
#print axioms actual_positive_source_mixture
#print axioms original_triple_posterior_starts_singleton
#print axioms actual_original_posterior_mixture
#print axioms actual_source_occupancy_support_of_right_germ
end GProgram.G5.ActualPosteriorGerm

