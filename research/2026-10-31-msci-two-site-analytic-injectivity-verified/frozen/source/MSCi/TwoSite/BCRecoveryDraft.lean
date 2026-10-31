import MSCi.TwoSite.BCExcessDraft
import MSCi.TwoSite.CRecoveryDraft

/-!
Uncompiled candidate pulse-time and probability recovery for the transcribed
analytic map. This composes the candidate BC excess, kernel-ratio, root and
C-rate results. It is not a Lean-checked proof or a derivation of the moments
from the six-sample process or the shared-genealogy observation law.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

def bcExcess (p : Parameters) (z : ℝ) : ℝ :=
  pairTransform p .BC z - rootMoment p.t0 p.rR z

def bcExcessRatio (p : Parameters) (c : ℝ) : ℝ :=
  bcExcess p (2 * c) / bcExcess p c

theorem bc_excess_eq_integral (p : Parameters) (z : ℝ)
    (hr : 0 < p.rC) (hz : 0 < z) :
    bcExcess p z = p.g * (p.rC * Real.exp (p.rC * p.h) *
      (∫ t in p.h..p.t0, pulseKernel p.t0 p.rR p.rC z t)) := by
  unfold bcExcess
  rw [bc_transform_split]
  calc
    (1 - p.g) * rootMoment p.t0 p.rR z +
        p.g * pulseShiftedMoment p.t0 p.rR p.rC z p.h - rootMoment p.t0 p.rR z =
        p.g * (pulseShiftedMoment p.t0 p.rR p.rC z p.h - rootMoment p.t0 p.rR z) := by
      ring
    _ = p.g * (p.rC * Real.exp (p.rC * p.h) *
        (∫ t in p.h..p.t0, pulseKernel p.t0 p.rR p.rC z t)) := by
      rw [pulse_excess_integral p.t0 p.rR p.rC z p.h hr hz]

theorem pulse_weight_integral_pos (T R r c h : ℝ)
    (hR : 0 < R) (hc : 0 < c) (hhT : h < T) :
    0 < ∫ t in h..T, pulseWeight T R r c t := by
  apply intervalIntegral.integral_pos hhT (pulse_weight_continuous T R r c).continuousOn
  · intro t ht
    exact le_of_lt (pulse_weight_positive T R r c t hR hc ht.2)
  · exact ⟨h, ⟨le_rfl, le_of_lt hhT⟩,
      pulse_weight_positive T R r c h hR hc (le_of_lt hhT)⟩

/-- In the strict domain the common positive factors cancel in the BC ratio. -/
theorem bc_excess_ratio_eq_kernel_ratio (p : Parameters) (c : ℝ)
    (hp : Admissible p) (hc : 0 < c) :
    bcExcessRatio p c =
      (∫ t in p.h..p.t0, pulseKernelTwo p.t0 p.rR p.rC c t) /
        (∫ t in p.h..p.t0, pulseWeight p.t0 p.rR p.rC c t) := by
  have hhT : p.h < p.t0 := lt_trans hp.2.1 hp.2.2.1
  have hg : 0 < p.g := by rcases hp with ⟨_, _, _, hg, _⟩; exact hg
  have hr : 0 < p.rC := by rcases hp with ⟨_, _, _, _, _, _, _, hr, _, _⟩; exact hr
  have hR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hR⟩; exact hR
  have h2c : 0 < 2 * c := by positivity
  have hI : 0 < ∫ t in p.h..p.t0, pulseWeight p.t0 p.rR p.rC c t :=
    pulse_weight_integral_pos p.t0 p.rR p.rC c p.h hR hc hhT
  have hg0 : p.g ≠ 0 := ne_of_gt hg
  have hr0 : p.rC ≠ 0 := ne_of_gt hr
  have he0 : Real.exp (p.rC * p.h) ≠ 0 := ne_of_gt (Real.exp_pos _)
  unfold bcExcessRatio
  rw [bc_excess_eq_integral p (2 * c) hr h2c, bc_excess_eq_integral p c hr hc]
  change p.g * (p.rC * Real.exp (p.rC * p.h) *
        (∫ t in p.h..p.t0, pulseKernelTwo p.t0 p.rR p.rC c t)) /
      (p.g * (p.rC * Real.exp (p.rC * p.h) *
        (∫ t in p.h..p.t0, pulseWeight p.t0 p.rR p.rC c t))) = _
  field_simp [hg0, hr0, he0, ne_of_gt hI] <;> ring

theorem bc_excess_ratio_eq_of_bc_eq (p q : Parameters) (c : ℝ)
    (ht : p.t0 = q.t0) (hR : p.rR = q.rR)
    (h1 : pairTransform p .BC c = pairTransform q .BC c)
    (h2 : pairTransform p .BC (2 * c) = pairTransform q .BC (2 * c)) :
    bcExcessRatio p c = bcExcessRatio q c := by
  unfold bcExcessRatio bcExcess
  rw [h1, h2, ht, hR]

/-- Equality of BC moments identifies pulse time after the root and C rate. -/
theorem pulse_time_eq_of_bc_eq (p q : Parameters) (c : ℝ)
    (hp : Admissible p) (hq : Admissible q) (hc : 0 < c)
    (ht : p.t0 = q.t0) (hR : p.rR = q.rR) (hC : p.rC = q.rC)
    (h1 : pairTransform p .BC c = pairTransform q .BC c)
    (h2 : pairTransform p .BC (2 * c) = pairTransform q .BC (2 * c)) :
    p.h = q.h := by
  have hpR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hpR⟩; exact hpR
  have hpt : p.h < p.t0 := lt_trans hp.2.1 hp.2.2.1
  have hqt : q.h < p.t0 := by
    have h : q.h < q.t0 := lt_trans hq.2.1 hq.2.2.1
    simpa [ht] using h
  have heq := bc_excess_ratio_eq_of_bc_eq p q c ht hR h1 h2
  rw [bc_excess_ratio_eq_kernel_ratio p c hp hc,
    bc_excess_ratio_eq_kernel_ratio q c hq hc, ← ht, ← hR, ← hC] at heq
  rcases lt_trichotomy p.h q.h with hlt | hequal | hgt
  · have hstrict := pulse_kernel_ratio_strict p.t0 p.rR p.rC c p.h q.h hpR hc hlt hqt
    linarith
  · exact hequal
  · have hstrict := pulse_kernel_ratio_strict p.t0 p.rR p.rC c q.h p.h hpR hc hgt hpt
    linarith

/-- With the root, C rate and pulse time fixed, one BC moment identifies g. -/
theorem pulse_probability_eq_of_bc_eq (p q : Parameters) (c : ℝ)
    (hp : Admissible p) (hc : 0 < c)
    (ht : p.t0 = q.t0) (hR : p.rR = q.rR) (hC : p.rC = q.rC)
    (hh : p.h = q.h)
    (h1 : pairTransform p .BC c = pairTransform q .BC c) : p.g = q.g := by
  have hr : 0 < p.rC := by rcases hp with ⟨_, _, _, _, _, _, _, hr, _, _⟩; exact hr
  have hpR : 0 < p.rR := by rcases hp with ⟨_, _, _, _, _, _, _, _, _, hpR⟩; exact hpR
  have hpt : p.h < p.t0 := lt_trans hp.2.1 hp.2.2.1
  have hI : 0 < ∫ t in p.h..p.t0, pulseKernel p.t0 p.rR p.rC c t := by
    change 0 < ∫ t in p.h..p.t0, pulseWeight p.t0 p.rR p.rC c t
    exact pulse_weight_integral_pos p.t0 p.rR p.rC c p.h hpR hc hpt
  have hshift : 0 < pulseShiftedMoment p.t0 p.rR p.rC c p.h -
      rootMoment p.t0 p.rR c := by
    rw [pulse_excess_integral p.t0 p.rR p.rC c p.h hr hc]
    exact mul_pos (mul_pos hr (Real.exp_pos _)) hI
  rw [bc_transform_split p, bc_transform_split q, ← ht, ← hR, ← hC, ← hh] at h1
  have hprod : (p.g - q.g) * (pulseShiftedMoment p.t0 p.rR p.rC c p.h -
      rootMoment p.t0 p.rR c) = 0 := by nlinarith
  have hdiff : p.g - q.g = 0 := (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hshift)
  linarith

/-- Candidate composition with the previously recovered root and C rate. -/
theorem pulse_parameters_eq_of_nineRawFeatures_eq (p q : Parameters)
    (hp : Admissible p) (hq : Admissible q)
    (hF : nineRawFeatures p = nineRawFeatures q) : p.h = q.h ∧ p.g = q.g := by
  have ht := rootTime_eq_of_nineRawFeatures_eq p q hp hq hF
  have hR := rootRate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hC := c_rate_eq_of_nineRawFeatures_eq p q hp hq hF
  have hc : 0 < jcPairExponent := by norm_num [jcPairExponent]
  have h1 : pairTransform p .BC jcPairExponent = pairTransform q .BC jcPairExponent := by
    have h := congrFun hF (3 : Fin 9)
    simpa [nineRawFeatures] using h
  have h2 : pairTransform p .BC (2 * jcPairExponent) =
      pairTransform q .BC (2 * jcPairExponent) := by
    have h := congrFun hF (4 : Fin 9)
    simpa [nineRawFeatures] using h
  have hh := pulse_time_eq_of_bc_eq p q jcPairExponent hp hq hc ht hR hC h1 h2
  exact ⟨hh, pulse_probability_eq_of_bc_eq p q jcPairExponent hp hc ht hR hC hh h1⟩

end MSCi.TwoSite
