import UnifiedLean.Source.NativeIndependentPairMixture
import G5UnknownRateSupport

/-!
# Actual native stopped-pair right germ and safe separation coefficient

Contributor: dot, 2026-10-02. The native independent coin × original-clock
probability, not a fitted exponential law, has a finite right-germ expansion.
At an entire-safe-past stage its zero exponent coefficient is the unconditional
current-route separation mass: permanence makes that branch's whole past hazard
zero. No calibrated common rate list or derivative oracle is supplied.
The stage initialization/deletion algorithm and final quartet assembly remain
separate formalization obligations.
-/
namespace UnifiedLean.Source.NativeSafePastGerm
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard GProgram.G5.SafePast
open GProgram.G5.ExponentialGerm
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def nativeSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (t : ℝ) : ℝ :=
  (nativePairMeasure N p r (survivingReadoutEvent N C H x y t (fun _ => True))).toReal

/-- Equal rate values are gathered, rather than artificially made distinct. -/
noncomputable def nativeGermCoefficients (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (t : ℝ) : ℝ →₀ ℝ :=
  ∑ a : NativeCoinSeed N, Finsupp.single
    (-currentPairRate N C r.edge (seededRoutes N C H a) x y t)
    (originalCoinMass N p a * routeSurvival N C r.edge (seededRoutes N C H a) x y t)

lemma nativeGermCoefficients_evaluation (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (t u : ℝ) :
    finiteExpSum (nativeGermCoefficients N C H p r x y t) u =
      ∑ a : NativeCoinSeed N, (originalCoinMass N p a *
        routeSurvival N C r.edge (seededRoutes N C H a) x y t) *
        Real.exp ((-currentPairRate N C r.edge (seededRoutes N C H a) x y t) * u) := by
  unfold nativeGermCoefficients finiteExpSum
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _)
    (fun _ _ _ => add_mul _ _ _)]
  apply Finset.sum_congr rfl
  intro a _
  exact Finsupp.sum_single_index (zero_mul _)

/-- At ANY event-free window below the original root, the actual measure's
right germ equals the constructed intrinsic finite coefficient map. -/
theorem native_probability_right_germ (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (hne : x ≠ y)
    {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε) (hu : 0 ≤ u) (huε : u < ε)
    (hroot : t+u ≤ C.age N.root) :
    nativeSurvival N C H p r x y (t+u) =
      finiteExpSum (nativeGermCoefficients N C H p r x y t) u := by
  rw [nativeSurvival,below_root_native_pair_probability N C H p r x y hne hroot,
    nativeGermCoefficients_evaluation]
  apply Finset.sum_congr rfl
  intro a _
  rw [routeSurvival_add_on_endpoint_gap N C r.edge _ x y hgap hu huε]
  ring

/-- A suitable positive window exists from the finite original clock set;
the observer need not know that set or supply a calibrated grid. -/
theorem native_probability_positive_right_window (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (hne : x ≠ y) {t : ℝ}
    (ht : t < C.age N.root) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℝ, 0 ≤ u → u < ε →
      nativeSurvival N C H p r x y (t+u) =
        finiteExpSum (nativeGermCoefficients N C H p r x y t) u := by
  obtain ⟨δ,hδ,hgap⟩ := positive_endpoint_gap_exists N C t
  refine ⟨min δ (C.age N.root-t),lt_min hδ (sub_pos.mpr ht),?_⟩
  intro u hu huε
  apply native_probability_right_germ N C H p r x y hne hgap hu
  · exact huε.trans_le (min_le_left _ _)
  · have hh := huε.trans_le (min_le_right δ (C.age N.root-t))
    linarith

/-- Actual original-route separation, with the natural unconditioned source
coins. It is not a survival-posterior routing probability. -/
noncomputable def nativeSeparationMass (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (x y : X) (t : ℝ) : ℝ :=
  ∑ a : NativeCoinSeed N, if ¬ CoOccupy N (seededRoutes N C H a) C t x y
    then originalCoinMass N p a else 0

/-- Entire-safe-past permanence removes the hidden survival reweighting on
EVERY zero-current-rate branch. Positive ORIGINAL rates identify that branch
with actual separation. This is the missing stochastic-to-germ source link. -/
theorem safe_native_zero_coefficient (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (B : Finset X) {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    {t : ℝ} (ht : t < C.age N.root) (hsafe : SafeAt N C B t) :
    nativeGermCoefficients N C H p r x y t 0 = nativeSeparationMass N C H p x y t := by
  unfold nativeGermCoefficients nativeSeparationMass
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : ¬ CoOccupy N (seededRoutes N C H a) C t x y
  · have hz := (currentPairRate_zero_iff_separated N C r.edge r.edge_pos _ x y t).mpr hs
    have hv := separated_safe_routeSurvival_one N C r.edge B
      (seededRoutes N C H a) ht hsafe hx hy hne hs
    simp [hz,hv,hs]
  · have hz : currentPairRate N C r.edge (seededRoutes N C H a) x y t ≠ 0 := by
      intro h
      exact hs ((currentPairRate_zero_iff_separated N C r.edge r.edge_pos _ x y t).mp h)
    simp [hz,hs]

/-- Equal actual probability germs identify the intrinsic coefficient map,
without being given its rates. This endpoint does not obtain those germs from
finite/noisy data or claim the deletion algorithm's initialization. -/
theorem native_coefficients_eq_of_probability_germ (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (hne : x ≠ y) {t ε : ℝ}
    (hε : 0 < ε) (hgap : EndpointGap N.graph C t ε) (hroot : t+ε ≤ C.age N.root)
    (d : ℝ →₀ ℝ) (heq : ∀ u : ℝ, 0 ≤ u → u < ε →
      nativeSurvival N C H p r x y (t+u) = finiteExpSum d u) :
    nativeGermCoefficients N C H p r x y t = d := by
  apply finite_coefficients_eq_of_right_germ _ _ hε
  intro u hu huε
  rw [← native_probability_right_germ N C H p r x y hne hgap hu huε
    (by linarith)]
  exact heq u hu huε

#print axioms nativeGermCoefficients_evaluation
#print axioms native_probability_right_germ
#print axioms native_probability_positive_right_window
#print axioms safe_native_zero_coefficient
#print axioms native_coefficients_eq_of_probability_germ
end UnifiedLean.Source.NativeSafePastGerm
