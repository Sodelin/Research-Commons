import UnifiedLean.G6.SourcePrefix
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
UNCHECKED draft until a pinned compiler receipt says otherwise.
Positive ratio-tail certificate for the actual normalized Poisson prefix.
The rational expression is computable for rational a; hidden physical source
parameters are not restricted to rationals. This file does not establish
positive source reconstruction or the timed-bin lift.
-/
namespace UnifiedLean.G6.TaylorCertificate
open UnifiedLean.G6.SourcePrefix
open scoped BigOperators NNReal

lemma taylorTerm_nonneg {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : 0 ≤ taylorTerm a k := by
  unfold taylorTerm
  positivity

lemma taylorTerm_succ (a : ℝ) (k : ℕ) :
    taylorTerm a (k + 1) = taylorTerm a k * (a / (k + 1)) := by
  simp only [taylorTerm, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  have hf : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hf, hk] <;> ring

set_option backward.isDefEq.respectTransparency false in
lemma taylor_hasSum (a : ℝ) : HasSum (taylorTerm a) (Real.exp a) := by
  change HasSum (fun k : ℕ => a ^ k / (k.factorial : ℝ)) (Real.exp a)
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp a

lemma taylor_tail_geometric {a : ℝ} (ha : 0 ≤ a) (K : ℕ)
    (hK : 2 * a ≤ (K : ℝ) + 2) (j : ℕ) :
    taylorTerm a (K + 1 + j) ≤ taylorTerm a (K + 1) * (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hidx : K + 1 + (j + 1) = (K + 1 + j) + 1 := by omega
    have hd : (0 : ℝ) < (K + 1 + j : ℕ) + 1 := by positivity
    have hratio : a / ((K + 1 + j : ℕ) + 1 : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ hd).mpr
      have hj : (0 : ℝ) ≤ j := by positivity
      push_cast
      nlinarith
    calc
      taylorTerm a (K + 1 + (j + 1)) =
          taylorTerm a (K + 1 + j) * (a / ((K + 1 + j : ℕ) + 1 : ℝ)) := by
            rw [hidx, taylorTerm_succ]
      _ ≤ taylorTerm a (K + 1 + j) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hratio (taylorTerm_nonneg ha _)
      _ ≤ (taylorTerm a (K + 1) * (1 / 2 : ℝ) ^ j) * (1 / 2) :=
        mul_le_mul_of_nonneg_right ih (by norm_num)
      _ = taylorTerm a (K + 1) * (1 / 2 : ℝ) ^ (j + 1) := by
        rw [pow_succ, mul_assoc]

theorem taylor_tail_bound {a : ℝ} (ha : 0 ≤ a) (K : ℕ)
    (hK : 2 * a ≤ (K : ℝ) + 2) :
    (∑' j : ℕ, taylorTerm a (K + 1 + j)) ≤ 2 * taylorTerm a (K + 1) := by
  have ht : Summable (fun j : ℕ => taylorTerm a (K + 1 + j)) :=
    (taylor_hasSum a).summable.comp_injective (by
      intro i j hij
      omega)
  have hg : Summable (fun j : ℕ => taylorTerm a (K + 1) * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  calc
    (∑' j : ℕ, taylorTerm a (K + 1 + j)) ≤
        ∑' j : ℕ, taylorTerm a (K + 1) * (1 / 2 : ℝ) ^ j :=
      ht.tsum_le_tsum (taylor_tail_geometric ha K hK) hg
    _ = 2 * taylorTerm a (K + 1) := by
      rw [tsum_mul_left, tsum_geometric_two]
      ring

theorem exp_le_taylor_enclosure {a : ℝ} (ha : 0 ≤ a) (K : ℕ)
    (hK : 2 * a ≤ (K : ℝ) + 2) :
    Real.exp a ≤ taylorPrefix a K + 2 * taylorTerm a (K + 1) := by
  have heq : taylorPrefix a K + (∑' j : ℕ, taylorTerm a (K + 1 + j)) = Real.exp a := by
    simpa only [taylorPrefix, Nat.add_comm, (taylor_hasSum a).tsum_eq] using
      (taylor_hasSum a).summable.sum_add_tsum_nat_add (K + 1)
  have ht := taylor_tail_bound ha K hK
  linarith

noncomputable def errorBound (a : ℝ) (K : ℕ) : ℝ :=
  2 * taylorTerm a (K + 1) / (taylorPrefix a K + 2 * taylorTerm a (K + 1))

theorem prefix_deficit_le_certificate (a : ℝ≥0) (K : ℕ)
    (hK : 2 * (a : ℝ) ≤ (K : ℝ) + 2) :
    1 - prefixMass a K ≤ errorBound (a : ℝ) K := by
  have hS := taylorPrefix_pos a K
  have hT := taylorTerm_nonneg a.coe_nonneg (K + 1)
  have hU : 0 < taylorPrefix (a : ℝ) K + 2 * taylorTerm (a : ℝ) (K + 1) := by
    linarith
  have hlower : taylorPrefix (a : ℝ) K /
      (taylorPrefix (a : ℝ) K + 2 * taylorTerm (a : ℝ) (K + 1)) ≤ prefixMass a K := by
    rw [prefixMass_taylor, Real.exp_neg]
    simpa only [div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_left hS.le (Real.exp_pos (a : ℝ))
        (exp_le_taylor_enclosure a.coe_nonneg K hK)
  have hsplit : taylorPrefix (a : ℝ) K /
      (taylorPrefix (a : ℝ) K + 2 * taylorTerm (a : ℝ) (K + 1)) + errorBound (a : ℝ) K = 1 := by
    unfold errorBound
    rw [← add_div, div_self (ne_of_gt hU)]
  linarith

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.FiniteProbability
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Numerical enclosure bound for the unchanged actual source mixture. -/
theorem actual_source_prefix_tv_certificate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample)
    (hK : 2 * ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) ≤ (K : ℝ) + 2) :
    pmfTV (sourceTimeKernel N r t s) (finiteSourcePrefix N r t K s) ≤
      errorBound ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K :=
  (actual_source_prefix_tv N r t K s).trans
    (prefix_deficit_le_certificate _ K hK)

/-- One joint endpoint readout incurs the same certificate, without a coordinate factor. -/
theorem actual_source_joint_readout_tv_certificate {O : Type*} [Fintype O]
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (K : ℕ) (s : Code N sample)
    (readout : Code N sample → O)
    (hK : 2 * ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) ≤ (K : ℝ) + 2) :
    pmfTV ((sourceTimeKernel N r t s).map readout) ((finiteSourcePrefix N r t K s).map readout) ≤
      errorBound ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ) K :=
  (actual_source_joint_readout_tv N r t K s readout).trans
    (prefix_deficit_le_certificate _ K hK)

#print axioms taylor_tail_bound
#print axioms exp_le_taylor_enclosure
#print axioms prefix_deficit_le_certificate
#print axioms actual_source_prefix_tv_certificate
#print axioms actual_source_joint_readout_tv_certificate
end UnifiedLean.G6.TaylorCertificate
