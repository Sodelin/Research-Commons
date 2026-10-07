import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
Countable-coordinate first-age observation.
Contributor: dot (OpenAI), 7 October 2026.

This generic measurable reader recovers an explicitly proved threshold.
It does not assume or establish a source-specific threshold or matrix law.
-/
namespace GProgram.G2.RationalAgeReadout
open MeasureTheory Set
open scoped Classical NNReal ENNReal
variable {Q : Type*} [MeasurableSpace Q]

noncomputable def rationalAge (P : Q → Prop) (path : ℝ≥0 → Q) : ℝ≥0∞ :=
  ⨅ q : ℚ, if 0 ≤ (q : ℝ) ∧ P (path (Real.toNNReal (q : ℝ)))
    then ENNReal.ofReal (q : ℝ) else ⊤

lemma rational_age_measurable (P : Q → Prop) (hP : MeasurableSet {z | P z}) :
    Measurable (rationalAge P) := by
  unfold rationalAge
  apply Measurable.iInf
  intro q
  by_cases hq : 0 ≤ (q : ℝ)
  · simp only [hq, true_and]
    exact Measurable.ite (hP.preimage (measurable_pi_apply _))
      measurable_const measurable_const
  · simp only [hq, false_and, if_false]
    exact measurable_const

lemma rational_age_congr (P P' : Q → Prop) (path path' : ℝ≥0 → Q)
    (h : ∀ q : ℚ, P (path (Real.toNNReal (q : ℝ))) ↔
      P' (path' (Real.toNNReal (q : ℝ)))) :
    rationalAge P path = rationalAge P' path' := by
  unfold rationalAge
  congr 1
  funext q
  rw [h q]

lemma rational_age_le_at (P : Q → Prop) (path : ℝ≥0 → Q)
    (q : ℚ) (hq : 0 ≤ (q : ℝ)) (hp : P (path (Real.toNNReal (q : ℝ)))) :
    rationalAge P path ≤ ENNReal.ofReal (q : ℝ) := by
  exact (iInf_le _ q).trans_eq (if_pos ⟨hq,hp⟩)

lemma rational_age_eq_top (P : Q → Prop) (path : ℝ≥0 → Q)
    (h : ∀ q : ℚ, 0 ≤ (q : ℝ) → ¬ P (path (Real.toNNReal (q : ℝ)))) :
    rationalAge P path = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro q
  rw [if_neg (fun hq => h q hq.1 hq.2)]

/-- The value at the threshold itself is irrelevant to the rational infimum.
The before/after hypotheses must be supplied by an actual path argument. -/
theorem rational_age_of_threshold (P : Q → Prop) (path : ℝ≥0 → Q)
    (a : ℝ) (ha : 0 ≤ a)
    (hbefore : ∀ t : ℝ≥0, (t : ℝ) < a → ¬ P (path t))
    (hafter : ∀ t : ℝ≥0, a < (t : ℝ) → P (path t)) :
    rationalAge P path = ENNReal.ofReal a := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro b hab
    obtain ⟨q,hq,haq,hqb⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hab
    have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
    change ENNReal.ofReal a < ENNReal.ofReal (q : ℝ) at haq
    have haqR : a < (q : ℝ) := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mp haq
    have hp := hafter (Real.toNNReal (q : ℝ)) (by simpa only [Real.coe_toNNReal _ hqR] using haqR)
    exact (rational_age_le_at P path q hqR hp).trans_lt hqb
  · apply le_iInf
    intro q
    by_cases hq : 0 ≤ (q : ℝ) ∧ P (path (Real.toNNReal (q : ℝ)))
    · rw [if_pos hq]
      apply ENNReal.ofReal_le_ofReal
      by_contra hnot
      have hlt : (q : ℝ) < a := lt_of_not_ge hnot
      exact hbefore (Real.toNNReal (q : ℝ))
        (by simpa only [Real.coe_toNNReal _ hq.1] using hlt) hq.2
    · rw [if_neg hq]
      exact le_top

#print axioms rational_age_measurable
#print axioms rational_age_congr
#print axioms rational_age_le_at
#print axioms rational_age_eq_top
#print axioms rational_age_of_threshold
end GProgram.G2.RationalAgeReadout
