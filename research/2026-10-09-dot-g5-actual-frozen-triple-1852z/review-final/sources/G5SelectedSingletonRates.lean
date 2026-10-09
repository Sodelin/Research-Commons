import G5SelectedSingletonCarrier

/-!
# Current pair rates of the actual selected singleton source

Contributor: dot, 2026-10-09. Verification is recorded by the packet's exact-byte build and owned-declaration audit receipt.
Counts are derived from the actual CURRENT pair catalogue on the selected
original-copy subtype. Each ordered orientation has half the population rate.
Original parallel edge IDs and the original ancestral population stay distinct.
-/
namespace GProgram.G5.SelectedSingletonRates
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCopyCarrierTransport
open GProgram.G5.SelectedSingletonCarrier
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem selected_singleton_population_card (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample)
    (place : Location V E) :
    (populationRoots (state (selectedSingletonCode N keep s)) place).card =
      (keep.filter (fun x => copyLocation (state s) x = place)).card := by
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hp := selected_singleton_code_population N keep s x
    have ha := congrFun (selected_singleton_code_ancestor N keep s) x
    change (state (selectedSingletonCode N keep s)).location
      ((state (selectedSingletonCode N keep s)).ancestor x) = _ at hp
    rw [ha] at hp
    exact Finset.mem_filter.mpr ⟨x.property, hp.symm.trans he⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    have hxk := (Finset.mem_filter.mp hx).1
    refine ⟨⟨x,hxk⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hp := selected_singleton_code_population N keep s ⟨x,hxk⟩
    have ha := congrFun (selected_singleton_code_ancestor N keep s) ⟨x,hxk⟩
    change (state (selectedSingletonCode N keep s)).location
      ((state (selectedSingletonCode N keep s)).ancestor ⟨x,hxk⟩) = _ at hp
    rw [ha] at hp
    exact hp.trans (Finset.mem_filter.mp hx).2

/-- General actual catalogue count, valid for every admitted source code. -/
theorem actual_total_rate_population_count (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    totalRate N r s = ∑ i : Option E,
      (((populationRoots (state s) (originalPlace N i)).card *
        (populationRoots (state s) (originalPlace N i)).card -
        (populationRoots (state s) (originalPlace N i)).card : Nat) : ℝ) *
          (pairRate r i / 2) := by
  unfold totalRate choiceRate
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, Finset.offDiag_card]

/-- The source rate now depends on the original selected population occupancy,
not hidden surviving representative IDs or unselected root counts. -/
theorem actual_selected_singleton_rate (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) :
    totalRate N r (selectedSingletonCode N keep s) = ∑ i : Option E,
      (((keep.filter (fun x => copyLocation (state s) x = originalPlace N i)).card *
        (keep.filter (fun x => copyLocation (state s) x = originalPlace N i)).card -
        (keep.filter (fun x => copyLocation (state s) x = originalPlace N i)).card : Nat) : ℝ) *
          (pairRate r i / 2) := by
  rw [actual_total_rate_population_count]
  simp_rw [selected_singleton_population_card]

lemma original_place_injective (N : RootedBinary V E X) :
    Function.Injective (originalPlace N : Option E → Location V E) := by
  intro a b h
  cases a <;> cases b <;> simp_all [originalPlace]

lemma original_place_eq_iff (N : RootedBinary V E X) (a b : Option E) :
    originalPlace N a = originalPlace N b ↔ a = b :=
  (original_place_injective N).eq_iff

/-- Actual unordered pair clock rate, zero in different original populations. -/
noncomputable def coincidentPairRate (r : PositivePairRates E) (a b : Option E) : ℝ :=
  if a = b then pairRate r a else 0

lemma sum_coincident_pair_rate (r : PositivePairRates E) (a b : Option E) :
    (∑ i : Option E, if a = i ∧ b = i then pairRate r i else 0) =
      coincidentPairRate r a b := by
  unfold coincidentPairRate
  by_cases he : a = b
  · simp [he, eq_comm]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    have hn : ¬ (a = i ∧ b = i) := by
      rintro ⟨ha,hb⟩
      exact he (ha.trans hb.symm)
    simp [hn]

/-- Exact two-selected-copy catalogue evaluation on original active populations. -/
theorem actual_selected_pair_rate (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (place : Copy → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    (a b : Copy) (hab : a ≠ b) :
    totalRate N r (selectedSingletonCode N {a,b} s) =
      coincidentPairRate r (place a) (place b) := by
  rw [actual_selected_singleton_rate]
  simp_rw [hloc, original_place_eq_iff]
  have hd : ∀ i : Option E,
      (((({a,b} : Finset Copy).filter (fun x => place x = i)).card *
        (({a,b} : Finset Copy).filter (fun x => place x = i)).card -
        (({a,b} : Finset Copy).filter (fun x => place x = i)).card : Nat) : ℝ) *
          (pairRate r i / 2) =
      if place a = i ∧ place b = i then pairRate r i else 0 := by
    intro i
    by_cases ha : place a = i <;> by_cases hb : place b = i <;>
      simp [Finset.filter_insert, Finset.filter_singleton, ha, hb, hab] <;> ring
  simp_rw [hd]
  unfold coincidentPairRate
  by_cases he : place a = place b
  · simp [he, eq_comm]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro i _
    have hn : ¬ (place a = i ∧ place b = i) := by
      rintro ⟨ha,hb⟩
      exact he (ha.trans hb.symm)
    simp [hn]

/-- All three unordered CURRENT clocks are counted, with no equal-rate
assumption between distinct original populations. -/
theorem actual_selected_triple_rate (N : RootedBinary V E X)
    {sample : Fin 3 → X} (r : PositivePairRates E) (s : Code N sample)
    (place : Fin 3 → Option E)
    (hloc : ∀ x, copyLocation (state s) x = originalPlace N (place x)) :
    totalRate N r (selectedSingletonCode N Finset.univ s) =
      coincidentPairRate r (place 0) (place 1) +
      coincidentPairRate r (place 0) (place 2) +
      coincidentPairRate r (place 1) (place 2) := by
  rw [actual_selected_singleton_rate]
  simp_rw [hloc, original_place_eq_iff]
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  rw [hu]
  have hd : ∀ i : Option E,
      (((({0,1,2} : Finset (Fin 3)).filter (fun x => place x = i)).card *
        (({0,1,2} : Finset (Fin 3)).filter (fun x => place x = i)).card -
        (({0,1,2} : Finset (Fin 3)).filter (fun x => place x = i)).card : Nat) : ℝ) *
          (pairRate r i / 2) =
      (if place 0 = i ∧ place 1 = i then pairRate r i else 0) +
      (if place 0 = i ∧ place 2 = i then pairRate r i else 0) +
      (if place 1 = i ∧ place 2 = i then pairRate r i else 0) := by
    intro i
    by_cases h0 : place 0 = i <;> by_cases h1 : place 1 = i <;>
      by_cases h2 : place 2 = i <;>
      simp [Finset.filter_insert, Finset.filter_singleton, h0, h1, h2] <;> ring
  simp_rw [hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_coincident_pair_rate, sum_coincident_pair_rate, sum_coincident_pair_rate]

#print axioms selected_singleton_population_card
#print axioms actual_total_rate_population_count
#print axioms actual_selected_singleton_rate
#print axioms actual_selected_pair_rate
#print axioms actual_selected_triple_rate
end GProgram.G5.SelectedSingletonRates

