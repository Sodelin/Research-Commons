import ActualNoisyAdaptiveSource
import UnifiedLean.G6.ProgramPrefix

/-! Adaptive counterpart of the older fixed-program domination bound.
Known kernel-composition mathematics; source-specific integration is the goal.
Uniform retained mass is explicit, including every action the policy may select.
No claim that an arbitrary physical menu has such a budget. -/
namespace Dot.AdaptiveSourceBudget
open StochasticAbstraction UnifiedLean.G6.ProgramPrefix
open UnifiedLean.G6.FiniteProbability
open scoped Classical ENNReal
noncomputable section
variable {S A B : Type*}

theorem adaptive_domination (K L : A → S → PMF S)
    (alpha : ℝ≥0∞) (h : ∀ a s t, alpha * L a s t ≤ K a s t)
    (policy : Policy S A) (n : Nat) (past : List (S × A)) (s : S)
    (out : List (S × A) × S) :
    alpha^n * experiment L policy n past s out ≤ experiment K policy n past s out := by
  induction n generalizing past s out with
  | zero => simpa only [experiment,pow_zero,one_mul] using (le_refl ((PMF.pure (past,s)) out))
  | succ n ih =>
    simp only [experiment]
    simpa only [one_mul] using
      bind_scaled_domination (policy past s) (policy past s) _ _ 1 (alpha^(n+1))
        (fun _ => by simp) (fun a o => by
          simpa only [pow_succ,mul_comm] using
            bind_scaled_domination (K a s) (L a s)
              (fun t => experiment K policy n (past ++ [(s,a)]) t)
              (fun t => experiment L policy n (past ++ [(s,a)]) t)
              alpha (alpha^n) (h a s) (fun t o => ih _ t o) o) out

theorem adaptive_initial_domination (K L : A → S → PMF S)
    (alpha : ℝ≥0∞) (h : ∀ a s t, alpha * L a s t ≤ K a s t)
    (policy : Policy S A) (n : Nat) (mu : PMF S)
    (out : List (S × A) × S) :
    alpha^n * experimentLaw L policy n mu out ≤ experimentLaw K policy n mu out := by
  simpa only [one_mul,experimentLaw] using
    bind_scaled_domination mu mu (experiment K policy n []) (experiment L policy n [])
      1 (alpha^n) (fun _ => by simp)
      (fun s o => adaptive_domination K L alpha h policy n [] s o) out

theorem adaptive_readout_tv [Fintype B] (K L : A → S → PMF S)
    (alpha : ℝ≥0∞) (ha : alpha ≤ 1)
    (h : ∀ a s t, alpha * L a s t ≤ K a s t)
    (policy : Policy S A) (n : Nat) (mu : PMF S)
    (readout : List (S × A) × S → B) :
    pmfTV ((experimentLaw K policy n mu).map readout)
      ((experimentLaw L policy n mu).map readout) ≤ 1-(alpha^n).toReal := by
  apply pmf_scaled_domination_tv
  · exact (ENNReal.toReal_mono ENNReal.one_ne_top (pow_le_one₀ (show 0 ≤ alpha from bot_le) ha)).trans_eq
      ENNReal.toReal_one
  · intro b
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (PMF.apply_ne_top _ b)
      (map_scaled_domination _ _ _
        (adaptive_initial_domination K L alpha h policy n mu) readout b)

open Dot.ActualNoisyAdaptiveSource

theorem sensed_domination (K L : A → S → PMF S) {R O : Type*}
    (q : S → R) (sensor : A → R → R → PMF O)
    (alpha : ℝ≥0∞) (h : ∀ a s t, alpha * L a s t ≤ K a s t)
    (a : A) (s : S) (out : S × O) :
    alpha * sensed L q sensor a s out ≤ sensed K q sensor a s out := by
  simpa only [sensed,mul_one] using
    bind_scaled_domination (K a s) (L a s)
      (fun t => (sensor a (q s) (q t)).map fun o => (t,o))
      (fun t => (sensor a (q s) (q t)).map fun o => (t,o))
      alpha 1 (h a s) (fun _ _ => by simp) out

open Nanuq.Source UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
variable {V E Copy X O : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Adaptive count truncation of the ACTUAL source with the same noisy sensor.
The count cutoff can depend on the chosen action; its uniform retained mass
over this declared menu is an explicit obligation. Initial source/reading
correlation and the original register are retained. -/
theorem actual_noisy_adaptive_budget [Fintype B]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy)
    (op : A → ProgramStep N) (cutoff : A → Nat)
    (alpha : ℝ≥0∞) (ha : alpha ≤ 1)
    (budget : ∀ a, alpha ≤ stepMass (Copy := Copy) N r (cutoff a) (op a))
    (sensor : A → SelectedIndex N sample keep → SelectedIndex N sample keep → PMF O)
    (policy : Policy O A) (n : Nat) (mu : PMF (Code N sample × O))
    (readout : List ((Code N sample × O) × A) × (Code N sample × O) → B) :
    let K := fun a => sourceProgramStep N r (op a)
    let L := fun a => finiteProgramStep N r (cutoff a) (op a)
    pmfTV ((experimentLaw (sensorStep (sensed K (projection N keep) sensor))
      (observationPolicy Prod.snd policy) n mu).map readout)
      ((experimentLaw (sensorStep (sensed L (projection N keep) sensor))
      (observationPolicy Prod.snd policy) n mu).map readout) ≤ 1-(alpha^n).toReal := by
  dsimp only
  apply adaptive_readout_tv _ _ alpha ha
  intro a s d
  apply sensed_domination
  intro a s d
  exact (mul_le_mul' (budget a) le_rfl).trans
    (actual_step_domination N r (cutoff a) (op a) s d)

end
end Dot.AdaptiveSourceBudget

#print axioms Dot.AdaptiveSourceBudget.adaptive_domination
#print axioms Dot.AdaptiveSourceBudget.adaptive_readout_tv
#print axioms Dot.AdaptiveSourceBudget.actual_noisy_adaptive_budget
