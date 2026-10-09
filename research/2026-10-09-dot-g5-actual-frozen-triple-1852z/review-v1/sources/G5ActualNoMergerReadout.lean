import UnifiedLean.Source.SourceActualHoldingClocks

/-!
# Exact no-loss-of-live-roots readout of the actual source kernel

Contributor: dot, 2026-10-09. SOURCE DRAFT / COMPILER UNCHECKED.
Every genuine source merger drops the actual live-root count. Therefore an
endpoint with the initial count is precisely the unchanged source code on
kernel support, not merely a superset with a positive witness. This binds a
genealogy-count event to the already proved actual exponential holding mass.
-/
namespace GProgram.G5.ActualNoMergerReadout
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_step_same_card_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample)
    (hd : d ∈ (sourceStep N r s).support)
    (hc : liveCard d = liveCard s) : d = s := by
  obtain ⟨p, _, hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  cases p with
  | none => exact hp.symm
  | some p =>
      have hm := merger_destination_card N s p
      rw [hp] at hm
      omega

lemma actual_iteration_same_card_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s d : Code N sample)
    (hd : d ∈ (sourceIteration N r k s).support)
    (hc : liveCard d = liveCard s) : d = s := by
  induction k generalizing s with
  | zero => simpa only [sourceIteration, PMF.mem_support_pure_iff] using hd
  | succ k ih =>
      obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hms := step_support_card_le N r s hm
      have hdmle := iteration_support_card_le N r k m hdm
      have he : liveCard m = liveCard s := by omega
      exact (ih m hdm (by omega)).trans (actual_step_same_card_eq N r s m hm he)

/-- No positive-time source endpoint can hide a merger while retaining the
initial number of CURRENT roots. This includes the zero-duration endpoint. -/
theorem actual_kernel_same_card_eq (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample)
    (hd : d ∈ (sourceTimeKernel N r t s).support)
    (hc : liveCard d = liveCard s) : d = s := by
  obtain ⟨k, _, hkd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_iteration_same_card_eq N r k s d hkd hc

/-- An actual valid source forest has the maximal live-root count exactly
when no two original copy labels share an ancestor. -/
theorem actual_maximal_live_card_iff (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) :
    liveCard s = Fintype.card Copy ↔ Function.Injective (state s).ancestor := by
  have hv := s.property.forest
  have huniv : liveCard s = Fintype.card Copy ↔ (state s).live = Finset.univ := by
    change (state s).live.card = Fintype.card Copy ↔ _
    exact Finset.card_eq_iff_eq_univ _
  rw [huniv]
  constructor
  · intro h
    have hid : (state s).ancestor = id := by
      funext x
      exact hv.representative x (by rw [h]; exact Finset.mem_univ x)
    rw [hid]
    exact Function.injective_id
  · intro hi
    apply Finset.eq_univ_of_forall
    intro x
    have he : (state s).ancestor x = x :=
      hi (hv.representative ((state s).ancestor x) (hv.ancestor_live x))
    rw [← he]
    exact hv.ancestor_live x

/-- The actual genealogy-count atom has exactly the actual holding mass.
This statement is an event readout; it does not require observing the hidden
source code, populations, or once-drawn register. -/
theorem actual_kernel_live_card_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    ((sourceTimeKernel N r t s).map liveCard) (liveCard s) =
      sourceTimeKernel N r t s s := by
  rw [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single s]
  · simp
  · intro d _ hds
    by_cases hc : liveCard d = liveCard s
    · have hz : sourceTimeKernel N r t s d = 0 := by
        by_contra hz
        exact hds (actual_kernel_same_card_eq N r t s d
          ((PMF.mem_support_iff _ _).mpr hz) hc)
      simp [eq_comm, hc, hz]
    · simp [eq_comm, hc]
  · intro hs
    exact False.elim (hs (Finset.mem_univ s))

theorem actual_kernel_live_card_survival (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (((sourceTimeKernel N r t s).map liveCard) (liveCard s)).toReal =
      Real.exp (-(totalRate N r s * (t : ℝ))) := by
  rw [actual_kernel_live_card_mass, actual_source_kernel_no_merger]

/-- Entire-copy discreteness reads only ancestry equality in the actual
forest; the population and shared register remain latent. -/
noncomputable def discreteReadout (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Bool := decide (Function.Injective (state s).ancestor)

theorem actual_discrete_mass_eq_card_mass (N : RootedBinary V E X)
    {sample : Copy → X} (mu : PMF (Code N sample)) :
    (mu.map (discreteReadout N)) true = (mu.map liveCard) (Fintype.card Copy) := by
  simp only [PMF.map_apply]
  apply tsum_congr
  intro d
  have he := actual_maximal_live_card_iff N d
  simp [discreteReadout, eq_comm, ← he]

/-- Exact finite-time genealogy-discreteness probability from a genuine
singleton source state, with its actual current total merger rate. -/
theorem actual_discrete_survival (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (hs : Function.Injective (state s).ancestor) :
    (((sourceTimeKernel N r t s).map (discreteReadout N)) true).toReal =
      Real.exp (-(totalRate N r s * (t : ℝ))) := by
  rw [actual_discrete_mass_eq_card_mass,
    ← (actual_maximal_live_card_iff N s).mpr hs,
    actual_kernel_live_card_survival]

#print axioms actual_step_same_card_eq
#print axioms actual_iteration_same_card_eq
#print axioms actual_kernel_same_card_eq
#print axioms actual_maximal_live_card_iff
#print axioms actual_kernel_live_card_mass
#print axioms actual_kernel_live_card_survival
#print axioms actual_discrete_mass_eq_card_mass
#print axioms actual_discrete_survival
end GProgram.G5.ActualNoMergerReadout

