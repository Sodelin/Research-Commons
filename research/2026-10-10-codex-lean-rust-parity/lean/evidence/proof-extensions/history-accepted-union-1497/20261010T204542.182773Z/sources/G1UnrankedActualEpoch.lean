import G1UnrankedActualGenerator

/-! Genuine original-source epoch laws on the exact UNRANKED causal view.
Contributor: dot, 2026-10-03. Derived from actual source PMFs, not stipulated. -/
namespace G1UnrankedActualEpoch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourcePoissonKernel
open G1UnrankedSourceView G1UnrankedActualGenerator
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def unrankedRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : UnrankedIndex N sample keep) : Code N sample := Classical.choose v.property

lemma unrankedRepresentative_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : UnrankedIndex N sample keep) :
    unrankedView (selectedView (state (unrankedRepresentative N keep v)) keep) = v.val :=
  Classical.choose_spec v.property

noncomputable def unrankedStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (v : UnrankedIndex N sample keep) :
    PMF (UnrankedIndex N sample keep) :=
  (sourceStep N r (unrankedRepresentative N keep v)).map (unrankedProjection N keep)

theorem actual_unranked_source_step (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample) :
    (sourceStep N r s).map (unrankedProjection N keep) = unrankedStep N r keep (unrankedProjection N keep s) := by
  exact actual_unranked_step_row_independent N r keep s _
    (unrankedRepresentative_view N keep (unrankedProjection N keep s)).symm

noncomputable def unrankedIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Nat → UnrankedIndex N sample keep → PMF (UnrankedIndex N sample keep)
  | 0,v => PMF.pure v
  | k+1,v => (unrankedStep N r keep v).bind (unrankedIteration N r keep k)

theorem actual_unranked_iteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (k : Nat) (s : Code N sample) :
    (sourceIteration N r k s).map (unrankedProjection N keep) =
      unrankedIteration N r keep k (unrankedProjection N keep s) := by
  induction k generalizing s with
  | zero => simp [sourceIteration,unrankedIteration,PMF.pure_map]
  | succ k ih =>
      rw [sourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (sourceStep N r s).bind (unrankedIteration N r keep k ∘ unrankedProjection N keep) = _
      rw [← PMF.bind_map,actual_unranked_source_step]
      rfl

noncomputable def unrankedTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (v : UnrankedIndex N sample keep) :
    PMF (UnrankedIndex N sample keep) :=
  (countPMF (globalClockRate (Copy:=Copy) r * t)).bind (fun k => unrankedIteration N r keep k v)

theorem actual_unranked_time_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (unrankedProjection N keep) =
      unrankedTimeKernel N r keep t (unrankedProjection N keep s) := by
  rw [sourceTimeKernel,unrankedTimeKernel,PMF.map_bind]
  simp_rw [actual_unranked_iteration]

theorem actual_unranked_epoch_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0) (s z : Code N sample)
    (h : unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep)) :
    (sourceTimeKernel N r t s).map (unrankedProjection N keep) =
      (sourceTimeKernel N r t z).map (unrankedProjection N keep) := by
  have he : unrankedProjection N keep s = unrankedProjection N keep z := Subtype.ext h
  rw [actual_unranked_time_kernel,actual_unranked_time_kernel,he]

#print axioms actual_unranked_epoch_row_independent
end G1UnrankedActualEpoch
