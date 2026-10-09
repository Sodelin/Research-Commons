import ActualPulseOccupancy

namespace DotG34.ActualBigonRate
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.NativePairClockLaw
open DotG34.ActualPopulationRate DotG34.ActualPulseOccupancy
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma pulse_other_population_empty (N : RootedBinary V E X)
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (hall : ∀ l ∈ s.live, s.location l = .node H.hybrid)
    (coin : AtNode s H.hybrid → Bool) (i : Option E)
    (h0 : i ≠ some H.parent0) (h1 : i ≠ some H.parent1) :
    populationRoots (pulse H s coin) (originalPlace N i) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro l hl
  obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hl
  have he : Location.edge (H.parent (coin ⟨l,hm,hall l hm⟩)) = originalPlace N i := by
    simpa [pulse,transport,hm,hall l hm] using hp
  cases hc : coin ⟨l,hm,hall l hm⟩ <;> cases i <;>
    simp_all [originalPlace,GProgram.G2.OriginalHybridParents.parent]

noncomputable def coinCount {Site : Type*} [Fintype Site] (coin : Site → Bool) (b : Bool) : ℕ :=
  (Finset.univ.filter (fun l => coin l=b)).card

lemma actual_parent_count (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (coin : AtNode (state s) H.hybrid → Bool) (b : Bool) :
    (populationRoots (state (pulseCode H s coin)) (.edge (H.parent b))).card = coinCount coin b := by
  rw [actual_pulse_population_roots, pulse_parent_population N H (state s) hall coin b]
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- No other population contributes after this all-roots private entrance.
The two original rate-bank entries remain distinct and unchanged. -/
theorem actual_bigon_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (coin : AtNode (state s) H.hybrid → Bool) :
    totalRate N r (pulseCode H s coin) =
      pairRate r (some H.parent0) * ((coinCount coin false).choose 2 : ℝ) +
      pairRate r (some H.parent1) * ((coinCount coin true).choose 2 : ℝ) := by
  rw [actual_rate_choose_two]
  have hk0 : (populationRoots (state (pulseCode H s coin))
      (originalPlace N (some H.parent0))).card = coinCount coin false := by
    simpa [originalPlace, GProgram.G2.OriginalHybridParents.parent] using
      actual_parent_count N H s hall coin false
  have hk1 : (populationRoots (state (pulseCode H s coin))
      (originalPlace N (some H.parent1))).card = coinCount coin true := by
    simpa [originalPlace, GProgram.G2.OriginalHybridParents.parent] using
      actual_parent_count N H s hall coin true
  have hother (i : Option E) (h0 : i ≠ some H.parent0) (h1 : i ≠ some H.parent1) :
      (populationRoots (state (pulseCode H s coin)) (originalPlace N i)).card = 0 := by
    rw [actual_pulse_population_roots,
      pulse_other_population_empty N H (state s) hall coin i h0 h1]
    rfl
  calc
    _ = ∑ i : Option E,
        ((if i = some H.parent0 then pairRate r (some H.parent0) *
          ((coinCount coin false).choose 2 : ℝ) else 0) +
        (if i = some H.parent1 then pairRate r (some H.parent1) *
          ((coinCount coin true).choose 2 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h0 : i = some H.parent0
      · subst i
        simp [hk0, H.different]
      · by_cases h1 : i = some H.parent1
        · subst i
          simp [hk1, H.different.symm]
        · simp [h0,h1,hother i h0 h1]
    _ = _ := by simp [Finset.sum_add_distrib]

#print axioms pulse_other_population_empty
#print axioms actual_parent_count
#print axioms actual_bigon_rate
end DotG34.ActualBigonRate
