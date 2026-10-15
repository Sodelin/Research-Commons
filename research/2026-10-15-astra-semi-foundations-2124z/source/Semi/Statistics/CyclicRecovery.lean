import Semi.Statistics.FiniteDecision
import Semi.Diffraction.OrbitHamming

/-!
Classical example binding, not a selected field research goal or a sampling
theorem. SOURCE CANDIDATE. Every action is a source orbit; a fibre restriction
on actions is neither present nor intended.
-/

namespace Semi.Statistics.CyclicRecovery

open Semi.Diffraction
variable {N : ℕ} [NeZero N]

abbrev CyclicRule (N : ℕ) [NeZero N] :=
  DecisionRule (Grid N → ℝ) (SourceOrbit N)

noncomputable def exactIntensityFloor (N : ℕ) [NeZero N] : ℝ :=
  exactDataMinimaxFloor (intensity (N := N)) (orbitLoss (N := N))

theorem orbit_risk_bounds (q : RandomizedAction (SourceOrbit N)) (x : Configuration N) :
    0 ≤ risk orbitLoss q x ∧ risk orbitLoss q x ≤ 1 :=
  ⟨risk_nonneg _ _ _ (fun a => orbitMetric_nonneg a (sourceOrbit x)),
    risk_le_one _ _ _ (fun a => orbitMetric_le_one a (sourceOrbit x))⟩

theorem equal_intensity_lower_bound (rule : CyclicRule N) (x y : Configuration N)
    (same : intensity x = intensity y) :
    orbitMetric (sourceOrbit x) (sourceOrbit y) / 2 ≤
      max (risk orbitLoss (rule (intensity x)) x) (risk orbitLoss (rule (intensity y)) y) :=
  indistinguishable_pair_lower_bound intensity orbitLoss rule x y same _
    (fun a => orbitLoss_pair_bound a x y)

end Semi.Statistics.CyclicRecovery
