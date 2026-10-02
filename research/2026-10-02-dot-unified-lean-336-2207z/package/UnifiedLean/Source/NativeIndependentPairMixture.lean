import UnifiedLean.Source.NativePairClockLaw
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Current-owner original-site coins and stopped pair mixture

Contributor: dot, 2026-10-02. Every original hybrid has ONE source parameter;
each still-separate tip owner receives its own Bernoulli coin at that original
site. All potential coins are drawn independently of original holding clocks.
Unused seed bits are latent variables, never declared measured itinerary labels.
The surviving original-route readout marginalizes those unused bits by a finite
sum. This constructs the private/independent two-root law up to its first merger;
full multi-root reset dynamics and the serial-region observation adapter remain
separate obligations.
-/
namespace UnifiedLean.Source.NativeIndependentPairMixture
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- One parameter assignment on the unchanged original hybrid registry. -/
structure HybridProbabilities (N : RootedBinary V E X) where
  gamma : Hybrid N → ℝ
  positive : ∀ h, 0 < gamma h
  below_one : ∀ h, gamma h < 1

abbrev NativeCoinSeed (N : RootedBinary V E X) := (X × Hybrid N) → Bool

noncomputable def originalCoinMass (N : RootedBinary V E X)
    (p : HybridProbabilities N) (a : NativeCoinSeed N) : ℝ :=
  ∏ s : X × Hybrid N, if a s then p.gamma s.2 else 1-p.gamma s.2

lemma originalCoinMass_positive (N : RootedBinary V E X)
    (p : HybridProbabilities N) (a : NativeCoinSeed N) : 0 < originalCoinMass N p a := by
  apply Finset.prod_pos
  intro s _
  split_ifs
  · exact p.positive s.2
  · exact sub_pos.mpr (p.below_one s.2)

lemma originalCoinMass_normalized (N : RootedBinary V E X) (p : HybridProbabilities N) :
    (∑ a : NativeCoinSeed N, originalCoinMass N p a) = 1 := by
  unfold originalCoinMass
  rw [← Fintype.prod_sum (fun (s : X × Hybrid N) (b : Bool) =>
    if b then p.gamma s.2 else 1-p.gamma s.2)]
  have h : ∀ s : X × Hybrid N,
      (∑ b : Bool, if b then p.gamma s.2 else 1-p.gamma s.2) = 1 := by
    intro s
    simp
  simp only [h,Finset.prod_const_one]

noncomputable def originalCoinPMF (N : RootedBinary V E X)
    (p : HybridProbabilities N) : PMF (NativeCoinSeed N) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (originalCoinMass N p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (originalCoinMass_positive N p a).le),
      originalCoinMass_normalized]
    simp)

noncomputable def seededRoutes (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : NativeCoinSeed N) : RouteFamily N :=
  compiledRouteFamily N C H (fun x h => a (x,h))

/-- Actual independent coin × original edge-clock source measure. -/
noncomputable def nativePairMeasure (N : RootedBinary V E X)
    (p : HybridProbabilities N) (r : PositivePairRates E) :
    Measure (NativeCoinSeed N × (Option E → ℝ)) :=
  (originalCoinPMF N p).toMeasure.prod (originalClockMeasure r)

/-- The predicate can depend on traversed ORIGINAL route IDs, not unobserved
coin labels. P=True is total survival; a route-record fiber is a measured
successful record. The observer discards all post-merger root logging. -/
def survivingReadoutEvent (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ)
    (P : NativeCoinSeed N → Prop) : Set (NativeCoinSeed N × (Option E → ℝ)) :=
  ⋃ a : NativeCoinSeed N, {a} ×ˢ
    (if P a then noFirstMerger N C (seededRoutes N C H a) x y t else ∅)

lemma noFirstMerger_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) :
    MeasurableSet (noFirstMerger N C R x y t) := by
  exact MeasurableSet.pi (Set.toFinite Set.univ).countable (fun e _ => measurableSet_Ioi)

lemma survivingReadoutEvent_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ)
    (P : NativeCoinSeed N → Prop) :
    MeasurableSet (survivingReadoutEvent N C H x y t P) := by
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.prod (measurableSet_singleton a)
  split_ifs
  · exact noFirstMerger_measurable N C _ x y t
  · exact MeasurableSet.empty

lemma survivingReadoutEvent_section (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ)
    (P : NativeCoinSeed N → Prop) (a : NativeCoinSeed N) :
    Prod.mk a ⁻¹' survivingReadoutEvent N C H x y t P =
      if P a then noFirstMerger N C (seededRoutes N C H a) x y t else ∅ := by
  ext clock
  simp only [survivingReadoutEvent,Set.mem_preimage,Set.mem_iUnion,Set.mem_prod,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨b,hab,hb⟩
    subst b
    exact hb
  · intro h
    exact ⟨a,rfl,h⟩

/-- Product-measure disintegration over the finite actual source seed. -/
theorem native_surviving_readout_mass (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (t : ℝ) (P : NativeCoinSeed N → Prop) :
    nativePairMeasure N p r (survivingReadoutEvent N C H x y t P) =
      ∑ a : NativeCoinSeed N, (originalCoinPMF N p a) *
        (if P a then originalClockMeasure r
          (noFirstMerger N C (seededRoutes N C H a) x y t) else 0) := by
  letI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  letI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [nativePairMeasure, Measure.prod_apply
    (survivingReadoutEvent_measurable N C H x y t P), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [survivingReadoutEvent_section,PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  split_ifs <;> simp [mul_comm]

/-- The unconditional pair probability is a source-derived finite mixture,
with no posterior replacement of the current-owner original hybrid coins.
Distinct owners enforce private/current-root semantics for this readout. -/
theorem below_root_native_pair_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (x y : X)
    (_different_current_owners : x ≠ y) {t : ℝ} (ht : t ≤ C.age N.root) :
    (nativePairMeasure N p r (survivingReadoutEvent N C H x y t (fun _ => True))).toReal =
      ∑ a : NativeCoinSeed N, originalCoinMass N p a *
        routeSurvival N C r.edge (seededRoutes N C H a) x y t := by
  letI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  letI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [native_surviving_readout_mass]
  simp only [if_true]
  rw [ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_mul,below_root_original_clock_law N C r _ x y ht]
  simp only [originalCoinPMF,PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (originalCoinMass_positive N p a).le]

#print axioms originalCoinMass_positive
#print axioms originalCoinMass_normalized
#print axioms survivingReadoutEvent_section
#print axioms native_surviving_readout_mass
#print axioms below_root_native_pair_probability
end UnifiedLean.Source.NativeIndependentPairMixture
