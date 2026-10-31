import MSCi.TwoSite.PulseKernelDraft

/-!
Uncompiled candidate BC moment-to-integral correspondence.

The formulas below concern the transcribed analytic map. They do not prove
that map is the law of the six-sample process, or finish pulse-parameter
identification. No Lean compiler or integral calculation has been run.
-/

noncomputable section

open MeasureTheory intervalIntegral

namespace MSCi.TwoSite

def pulseKernel (T R r z t : ℝ) : ℝ :=
  Real.exp (-r * t) * (Real.exp (-z * t) - rootMoment T R z)

def pulseShiftedMoment (T R r z h : ℝ) : ℝ :=
  Real.exp (-z * h) * (r / (r + z)) *
      (1 - Real.exp (-(r + z) * (T - h))) +
    Real.exp (-r * (T - h)) * rootMoment T R z

/-- The BC formula splits into the root baseline and shifted C route. -/
theorem bc_transform_split (p : Parameters) (z : ℝ) :
    pairTransform p .BC z = (1 - p.g) * rootMoment p.t0 p.rR z +
      p.g * pulseShiftedMoment p.t0 p.rR p.rC z p.h := by
  have hv : p.t1 - p.h + (p.t0 - p.t1) = p.t0 - p.h := by ring
  simp [pairTransform, pulseShiftedMoment, rootMoment, hv] <;> ring

theorem integral_exp_linear (k a b : ℝ) (hk : k ≠ 0) :
    (∫ t in a..b, Real.exp (k * t)) =
      (Real.exp (k * b) - Real.exp (k * a)) / k := by
  rw [intervalIntegral.integral_comp_mul_left Real.exp hk, integral_exp]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem pulse_kernel_integral_closed (T R r z h : ℝ) (hr : 0 < r) (hz : 0 < z) :
    (∫ t in h..T, pulseKernel T R r z t) =
      (Real.exp (-(r + z) * T) - Real.exp (-(r + z) * h)) / (-(r + z)) -
        rootMoment T R z * (Real.exp (-r * T) - Real.exp (-r * h)) / (-r) := by
  have hnrz : -(r + z) ≠ 0 := ne_of_lt (neg_lt_zero.mpr (by positivity))
  have hnr : -r ≠ 0 := ne_of_lt (neg_lt_zero.mpr hr)
  have hAcont : Continuous (fun t : ℝ => Real.exp (-(r + z) * t)) := by fun_prop
  have hBcont : Continuous (fun t : ℝ => Real.exp (-r * t)) := by fun_prop
  have hA : IntervalIntegrable (fun t => Real.exp (-(r + z) * t)) volume h T :=
    hAcont.intervalIntegrable h T
  have hB : IntervalIntegrable (fun t => Real.exp (-r * t)) volume h T :=
    hBcont.intervalIntegrable h T
  calc
    (∫ t in h..T, pulseKernel T R r z t) =
        ∫ t in h..T, (Real.exp (-(r + z) * t) -
          Real.exp (-r * t) * rootMoment T R z) := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold pulseKernel
      have he : Real.exp (-r * t + -z * t) = Real.exp (-(r + z) * t) := by
        congr 1
        ring
      rw [mul_sub, ← Real.exp_add, he]
    _ = (Real.exp (-(r + z) * T) - Real.exp (-(r + z) * h)) / (-(r + z)) -
          rootMoment T R z * (Real.exp (-r * T) - Real.exp (-r * h)) / (-r) := by
      rw [intervalIntegral.integral_sub hA (hB.mul_const (rootMoment T R z)),
        intervalIntegral.integral_mul_const,
        integral_exp_linear (-(r + z)) h T hnrz, integral_exp_linear (-r) h T hnr]
      ring

/-- The shifted-route excess is a positive factor times the kernel integral. -/
theorem pulse_excess_integral (T R r z h : ℝ) (hr : 0 < r) (hz : 0 < z) :
    pulseShiftedMoment T R r z h - rootMoment T R z =
      r * Real.exp (r * h) * (∫ t in h..T, pulseKernel T R r z t) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrz0 : r + z ≠ 0 := ne_of_gt (by positivity)
  have h0 : Real.exp (r * h) * Real.exp (-r * h) = 1 := by
    rw [← Real.exp_add]
    have hz0 : r * h + -r * h = 0 := by ring
    rw [hz0, Real.exp_zero]
  have h1 : Real.exp (r * h) * Real.exp (-(r + z) * h) = Real.exp (-z * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (r * h) * Real.exp (-(r + z) * T) =
      Real.exp (-z * h) * Real.exp (-(r + z) * (T - h)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (r * h) * Real.exp (-r * T) = Real.exp (-r * (T - h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  symm
  calc
    r * Real.exp (r * h) * (∫ t in h..T, pulseKernel T R r z t) =
        r * Real.exp (r * h) *
          ((Real.exp (-(r + z) * T) - Real.exp (-(r + z) * h)) / (-(r + z)) -
            rootMoment T R z * (Real.exp (-r * T) - Real.exp (-r * h)) / (-r)) := by
      rw [pulse_kernel_integral_closed T R r z h hr hz]
    _ = r / (r + z) *
          (Real.exp (r * h) * Real.exp (-(r + z) * h) -
            Real.exp (r * h) * Real.exp (-(r + z) * T)) +
        rootMoment T R z *
          (Real.exp (r * h) * Real.exp (-r * T) - Real.exp (r * h) * Real.exp (-r * h)) := by
      field_simp [hr0, hrz0] <;> ring
    _ = pulseShiftedMoment T R r z h - rootMoment T R z := by
      rw [h1, h2, h3, h0]
      unfold pulseShiftedMoment
      ring

end MSCi.TwoSite
