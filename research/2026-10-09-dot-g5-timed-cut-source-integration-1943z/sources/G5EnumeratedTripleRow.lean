import G5ActualFrozenTripleRow

/-!
# Triple formula on the unchanged actual three-element copy carrier
Contributor: dot, 2026-10-09. Candidate pending build and review.
An equivalence indexes only the readout and population array. No source law,
shared register, current owner or genealogy is replaced by a Fin-3 compiler.
-/
namespace GProgram.G5.EnumeratedTripleRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCopyCarrierTransport
open GProgram.G5.OriginalProgramSurvival GProgram.G5.SelectedSingletonCarrier
open GProgram.G5.SelectedDiscreteSurvival GProgram.G5.SelectedSingletonRates
open GProgram.G5.TriplePartitionReadout GProgram.G5.TripleMomentReconstruction
open GProgram.G5.ActualFrozenTripleRow GProgram.G5.FrozenTriplePolynomialKernel
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def indexedPartition (N : RootedBinary V E X) {sample : Copy → X}
    (e : Fin 3 ≃ Copy) (s : Code N sample) : Fin 5 :=
  ancestorPartition (fun i => (state s).ancestor (e i))

noncomputable def indexedPairDistinct (N : RootedBinary V E X) {sample : Copy → X}
    (i j : Copy) (s : Code N sample) : Bool := decide ((state s).ancestor i ≠ (state s).ancestor j)

noncomputable def indexedTripleDistinct (N : RootedBinary V E X) {sample : Copy → X}
    (e : Fin 3 ≃ Copy) (s : Code N sample) : Bool :=
  decide (Function.Injective (fun i => (state s).ancestor (e i)))

lemma composed_ancestor_injective (N : RootedBinary V E X) {sample : Copy → X}
    (e : Fin 3 ≃ Copy) (s : Code N sample) :
    Function.Injective (fun i => (state s).ancestor (e i)) ↔
      Function.Injective (state s).ancestor := by
  constructor
  · intro h x y he
    obtain ⟨i, rfl⟩ := e.surjective x
    obtain ⟨j, rfl⟩ := e.surjective y
    exact congrArg e (h he)
  · intro h
    exact h.comp e.injective

lemma enumeration_univ (e : Fin 3 ≃ Copy) : (Finset.univ : Finset Copy) = {e 0,e 1,e 2} := by
  ext x
  simp only [Finset.mem_univ, true_iff]
  obtain ⟨i, rfl⟩ := e.surjective x
  fin_cases i <;> simp

lemma actual_enumerated_triple_rate (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (r : PositivePairRates E) (s : Code N sample)
    (place : Copy → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x)) :
    totalRate N r (selectedSingletonCode N Finset.univ s) =
      coincidentPairRate r (place (e 0)) (place (e 1)) +
      coincidentPairRate r (place (e 0)) (place (e 2)) +
      coincidentPairRate r (place (e 1)) (place (e 2)) := by
  rw [actual_selected_singleton_rate]
  simp_rw [hloc, original_place_eq_iff]
  rw [enumeration_univ e]
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have h12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have hd : ∀ i : Option E,
      (((({e 0,e 1,e 2} : Finset Copy).filter (fun x => place x = i)).card *
        (({e 0,e 1,e 2} : Finset Copy).filter (fun x => place x = i)).card -
        (({e 0,e 1,e 2} : Finset Copy).filter (fun x => place x = i)).card : Nat) : ℝ) *
          (pairRate r i / 2) =
      (if place (e 0) = i ∧ place (e 1) = i then pairRate r i else 0) +
      (if place (e 0) = i ∧ place (e 2) = i then pairRate r i else 0) +
      (if place (e 1) = i ∧ place (e 2) = i then pairRate r i else 0) := by
    intro i
    by_cases h0 : place (e 0) = i <;> by_cases h1 : place (e 1) = i <;>
      by_cases h2 : place (e 2) = i <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2, h01, h02, h12] <;> ring
  simp_rw [hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_coincident_pair_rate, sum_coincident_pair_rate, sum_coincident_pair_rate]

theorem actual_enumerated_pair_survival (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : Copy → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (i j : Copy) (hij : i ≠ j) (t : ℝ≥0) :
    (((sourceTimeKernel N r t s).map (indexedPairDistinct N i j)) true).toReal =
      Real.exp (-(coincidentPairRate r (place i) (place j) * (t : ℝ))) := by
  have h := actual_selected_discrete_survival N r {i,j} s
    (actual_all_singleton_restrict N s hs {i,j}) t
  rw [PMF.map_comp, actual_selected_pair_rate N r s place hloc i j hij] at h
  have hf : (selectedDiscreteReadout N {i,j} ∘
      fun d : Code N sample => joinedProjection N {i,j} (.inl d)) =
      indexedPairDistinct N i j := by
    funext d
    change decide (DiscreteView {i,j} (selectedView (state d) {i,j})) =
      decide ((state d).ancestor i ≠ (state d).ancestor j)
    simp only [actual_pair_discrete_view N d i j hij]
  rw [hf] at h
  exact h

/-- The all-three distinct mass uses all three original unordered pair clocks. -/
theorem actual_enumerated_triple_survival (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (r : PositivePairRates E) (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : Copy → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (t : ℝ≥0) :
    (((sourceTimeKernel N r t s).map (indexedTripleDistinct N e)) true).toReal =
      Real.exp (-((coincidentPairRate r (place (e 0)) (place (e 1)) +
        coincidentPairRate r (place (e 0)) (place (e 2)) +
        coincidentPairRate r (place (e 1)) (place (e 2))) * (t : ℝ))) := by
  have h := actual_selected_discrete_survival N r Finset.univ s hs t
  rw [PMF.map_comp, actual_enumerated_triple_rate N e r s place hloc] at h
  have hf : (selectedDiscreteReadout N Finset.univ ∘
      fun d : Code N sample => joinedProjection N Finset.univ (.inl d)) =
      indexedTripleDistinct N e := by
    funext d
    change decide (DiscreteView Finset.univ (selectedView (state d) Finset.univ)) =
      decide (Function.Injective (fun i => (state d).ancestor (e i)))
    simp only [actual_discrete_view_iff_injOn, Finset.coe_univ, Set.injOn_univ, composed_ancestor_injective]
  rw [hf] at h
  exact h

theorem general_partition_zero (a : Fin 3 → Copy) :
    ancestorPartition a = 0 ↔ Function.Injective a := by
  have hi : Function.Injective a ↔ a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 ≠ a 2 := by
    constructor
    · intro h
      exact ⟨fun he => (by decide : (0 : Fin 3) ≠ 1) (h he),
        fun he => (by decide : (0 : Fin 3) ≠ 2) (h he),
        fun he => (by decide : (1 : Fin 3) ≠ 2) (h he)⟩
    · rintro ⟨h01,h02,h12⟩ x y he
      fin_cases x <;> fin_cases y <;> simp_all
  rw [hi]
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

/-- Every actual triple ancestry, regardless of hidden populations, obeys
the exact event table. The impossible nontransitive equality cases vanish. -/
theorem general_partition_pair01 (a : Fin 3 → Copy) :
    a 0 ≠ a 1 ↔ ancestorPartition a = 0 ∨
      ancestorPartition a = 2 ∨ ancestorPartition a = 3 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

theorem general_partition_pair02 (a : Fin 3 → Copy) :
    a 0 ≠ a 2 ↔ ancestorPartition a = 0 ∨
      ancestorPartition a = 1 ∨ ancestorPartition a = 3 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

theorem general_partition_pair12 (a : Fin 3 → Copy) :
    a 1 ≠ a 2 ↔ ancestorPartition a = 0 ∨
      ancestorPartition a = 1 ∨ ancestorPartition a = 2 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]


lemma indexed_partition_discrete_readout (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (s : Code N sample) :
    decide (indexedPartition N e s = 0) = indexedTripleDistinct N e s := by
  unfold indexedPartition indexedTripleDistinct
  congr 1
  exact propext (general_partition_zero _)

lemma indexed_partition_pair01_readout (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (s : Code N sample) :
    partitionPair01 (indexedPartition N e s) = indexedPairDistinct N (e 0) (e 1) s := by
  unfold partitionPair01 indexedPairDistinct indexedPartition
  congr 1
  exact propext (general_partition_pair01 _).symm

lemma indexed_partition_pair02_readout (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (s : Code N sample) :
    partitionPair02 (indexedPartition N e s) = indexedPairDistinct N (e 0) (e 2) s := by
  unfold partitionPair02 indexedPairDistinct indexedPartition
  congr 1
  exact propext (general_partition_pair02 _).symm

lemma indexed_partition_pair12_readout (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (s : Code N sample) :
    partitionPair12 (indexedPartition N e s) = indexedPairDistinct N (e 1) (e 2) s := by
  unfold partitionPair12 indexedPairDistinct indexedPartition
  congr 1
  exact propext (general_partition_pair12 _).symm

theorem actual_enumerated_triple_row (N : RootedBinary V E X)
    {sample : Copy → X} (e : Fin 3 ≃ Copy) (r : PositivePairRates E) (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : Copy → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (t : ℝ≥0) (gene : Fin 5) :
    (((sourceTimeKernel N r t s).map (indexedPartition N e)) gene).toReal =
      row (Real.exp (-(triplePopulationRate r (place ∘ e)*(t : ℝ))))
        (ancestorPartition (place ∘ e)) gene := by
  let mu := (sourceTimeKernel N r t s).map (indexedPartition N e)
  let q := row (Real.exp (-(triplePopulationRate r (place ∘ e)*(t : ℝ))))
    (ancestorPartition (place ∘ e))
  have hq : q 0 + q 1 + q 2 + q 3 + q 4 = 1 := by
    have h := row_sum (Real.exp (-(triplePopulationRate r (place ∘ e)*(t : ℝ))))
      (ancestorPartition (place ∘ e))
    simpa [q, Fin.sum_univ_succ, add_assoc] using h
  have hd : (mu 0).toReal = q 0 := by
    have h := actual_enumerated_triple_survival N e r s hs place hloc t
    have hf : (fun d : Code N sample => decide (indexedPartition N e d = 0)) =
        indexedTripleDistinct N e := by
      funext d; exact indexed_partition_discrete_readout N e d
    have hm : (mu.map (fun g => decide (g = 0))) true = mu 0 := by
      simp [PMF.map_apply, tsum_fintype, Fin.sum_univ_succ]
    rw [← hm]
    change (((((sourceTimeKernel N r t s).map (indexedPartition N e)).map
      (fun g => decide (g = 0))) true).toReal) = _
    rw [PMF.map_comp]
    change (((sourceTimeKernel N r t s).map
      (fun d => decide (indexedPartition N e d = 0))) true).toReal = _
    rw [hf, h]
    exact (polynomial_discrete_clock r (place ∘ e) (t : ℝ)).symm
  have h01 : (mu 0).toReal + (mu 2).toReal + (mu 3).toReal =
      q 0 + q 2 + q 3 := by
    rw [← five_pmf_pair01]
    change (((((sourceTimeKernel N r t s).map (indexedPartition N e)).map
      partitionPair01) true).toReal) = _
    rw [PMF.map_comp]
    have hf : partitionPair01 ∘ indexedPartition N e (sample := sample) = indexedPairDistinct N (e 0) (e 1) := by
      funext d; exact indexed_partition_pair01_readout N e d
    rw [hf, actual_enumerated_pair_survival N r s hs place hloc (e 0) (e 1) (e.injective.ne (by decide)) t]
    exact (polynomial_pair01_clock r (place ∘ e) (t : ℝ)).symm
  have h02 : (mu 0).toReal + (mu 1).toReal + (mu 3).toReal =
      q 0 + q 1 + q 3 := by
    rw [← five_pmf_pair02]
    change (((((sourceTimeKernel N r t s).map (indexedPartition N e)).map
      partitionPair02) true).toReal) = _
    rw [PMF.map_comp]
    have hf : partitionPair02 ∘ indexedPartition N e (sample := sample) = indexedPairDistinct N (e 0) (e 2) := by
      funext d; exact indexed_partition_pair02_readout N e d
    rw [hf, actual_enumerated_pair_survival N r s hs place hloc (e 0) (e 2) (e.injective.ne (by decide)) t]
    exact (polynomial_pair02_clock r (place ∘ e) (t : ℝ)).symm
  have h12 : (mu 0).toReal + (mu 1).toReal + (mu 2).toReal =
      q 0 + q 1 + q 2 := by
    rw [← five_pmf_pair12]
    change (((((sourceTimeKernel N r t s).map (indexedPartition N e)).map
      partitionPair12) true).toReal) = _
    rw [PMF.map_comp]
    have hf : partitionPair12 ∘ indexedPartition N e (sample := sample) = indexedPairDistinct N (e 1) (e 2) := by
      funext d; exact indexed_partition_pair12_readout N e d
    rw [hf, actual_enumerated_pair_survival N r s hs place hloc (e 1) (e 2) (e.injective.ne (by decide)) t]
    exact (polynomial_pair12_clock r (place ∘ e) (t : ℝ)).symm
  exact congrFun (five_mass_unique (fun g => (mu g).toReal) q
    (five_pmf_real_sum mu) hq hd h01 h02 h12) gene

/-- Enumeration of the actual selected-copy subtype, retaining its original
label projection; this is not an independently initialized Fin-3 source. -/
noncomputable def selectedEnumeration (keep : Finset Copy) (hc : keep.card = 3) :
    Fin 3 ≃ SelectedCopy keep :=
  (Fintype.equivFinOfCardEq (show Fintype.card (SelectedCopy keep) = 3 by
    simpa [SelectedCopy] using hc)).symm

/-- The actual G2-selected carrier can feed the closed triple formula directly.
Its current populations, old genealogy and COMMON register remain those in s. -/
theorem actual_selected_panel_triple_row (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) (hc : keep.card = 3)
    (r : PositivePairRates E) (s : Code N (selectedSample sample keep))
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (place : SelectedCopy keep → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (t : ℝ≥0) (gene : Fin 5) :
    (((sourceTimeKernel N r t s).map (indexedPartition N (selectedEnumeration keep hc))) gene).toReal =
      row (Real.exp (-(triplePopulationRate r (place ∘ selectedEnumeration keep hc)*(t : ℝ))))
        (ancestorPartition (place ∘ selectedEnumeration keep hc)) gene :=
  actual_enumerated_triple_row N (selectedEnumeration keep hc) r s hs place hloc t gene

#print axioms actual_enumerated_triple_rate
#print axioms actual_enumerated_triple_row
#print axioms actual_selected_panel_triple_row
end GProgram.G5.EnumeratedTripleRow
