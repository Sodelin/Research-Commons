import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum


open MeasureTheory Set

namespace P5OriginalGenerator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- An upper half-interval indicator includes one irrelevant endpoint. -/
theorem upper_triangle_section (f : ℝ → E) {T u : ℝ}
    (hu : u ∈ Icc 0 T) :
    (∫ s in 0..T, if u ≤ s then f s else 0) = ∫ s in u..T, f s := by
  have hT : 0 ≤ T := hu.1.trans hu.2
  have hset : Ioi u ∩ Ioc 0 T = Ioc u T := by
    ext x
    constructor
    · rintro ⟨hux,h0x,hxT⟩
      exact ⟨hux,hxT⟩
    · rintro ⟨hux,hxT⟩
      exact ⟨hux,lt_of_le_of_lt hu.1 hux,hxT⟩
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hu.2]
  calc
    _ = ∫ s in Ioc 0 T, (Ioi u).indicator f s := by
      apply setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [volume.ae_ne u] with s hs hmem
      by_cases h : u < s
      · simp [h, h.le]
      · have hsu : s < u := lt_of_le_of_ne (le_of_not_gt h) hs
        simp [h, not_le_of_gt hsu]
    _ = ∫ s in Ioi u ∩ Ioc 0 T, f s := by
      rw [MeasureTheory.integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi]
    _ = _ := by rw [hset]

omit [CompleteSpace E] in
/-- Exchange the lower triangle by a rectangular Fubini theorem. No
two-dimensional change of variables or extra endpoint observation is used. -/
theorem lower_triangle_swap (f : ℝ → ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hf : IntegrableOn f.uncurry (uIoc 0 T ×ˢ uIoc 0 T)) :
    (∫ s in 0..T, ∫ t in 0..s, f s t) =
      ∫ u in 0..T, ∫ s in u..T, f s u := by
  let g : ℝ → ℝ → E := fun s t => if t ≤ s then f s t else 0
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hg : IntegrableOn g.uncurry (uIoc 0 T ×ˢ uIoc 0 T) := by
    have hid : g.uncurry = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator f.uncurry := by
      funext p
      simp [g, Function.uncurry, Set.indicator_apply]
    rw [hid]
    exact hf.indicator hmeas
  calc
    _ = ∫ s in 0..T, ∫ t in 0..T, g s t := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using hs
      symm
      simpa only [g, Set.indicator_apply, Set.mem_ofPred_eq] using
        (intervalIntegral.integral_indicator (f := f s) hs')
    _ = ∫ u in 0..T, ∫ s in 0..T, g s u :=
      MeasureTheory.intervalIntegral_intervalIntegral_swap hg
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using hu
      exact upper_triangle_section (fun s => f s u) hu'

omit [CompleteSpace E] in
/-- The square-to-two-triangles geometry for an arbitrary L1 Bochner kernel.
Only null endpoints, product Fubini and one-dimensional translation are used. -/
theorem square_to_triangles (f : ℝ → ℝ → E) {T : ℝ} (hT : 0 ≤ T)
    (hf : IntegrableOn f.uncurry (uIoc 0 T ×ˢ uIoc 0 T)) :
    (∫ s in 0..T, ∫ t in 0..T, f s t) =
      ∫ u in 0..T, ∫ r in 0..(T-u), (f (u+r) u + f u (u+r)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 T)
  let D : (ℝ → ℝ → E) → E := fun a => ∫ s in 0..T, ∫ t in 0..T, a s t
  let g : ℝ → ℝ → E := fun s t => if t ≤ s then f s t else 0
  let h : ℝ → ℝ → E := fun s t => if s < t then f s t else 0
  let q : ℝ → ℝ → E := fun s t => g t s
  have hfprod : Integrable f.uncurry (μ.prod μ) := by
    dsimp [μ]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    simpa only [uIoc_of_le hT, IntegrableOn] using hf
  have hg : Integrable g.uncurry (μ.prod μ) := by
    have hid : g.uncurry = {p : ℝ × ℝ | p.2 ≤ p.1}.indicator f.uncurry := by
      funext p
      simp [g, Function.uncurry, Set.indicator_apply]
    rw [hid]
    exact hfprod.indicator (measurableSet_le measurable_snd measurable_fst)
  have hh : Integrable h.uncurry (μ.prod μ) := by
    have hid : h.uncurry = {p : ℝ × ℝ | p.1 < p.2}.indicator f.uncurry := by
      funext p
      simp [h, Function.uncurry, Set.indicator_apply]
    rw [hid]
    exact hfprod.indicator (measurableSet_lt measurable_fst measurable_snd)
  have hq : Integrable q.uncurry (μ.prod μ) := hg.swap
  have dadd (a b : ℝ → ℝ → E)
      (ha : Integrable a.uncurry (μ.prod μ)) (hb : Integrable b.uncurry (μ.prod μ)) :
      D (fun s t => a s t + b s t) = D a + D b := by
    dsimp [D]
    simp_rw [intervalIntegral.integral_of_le hT]
    exact MeasureTheory.integral_integral_add ha hb
  have hswap : D g = D q := by
    dsimp [D, q]
    simp_rw [intervalIntegral.integral_of_le hT]
    exact MeasureTheory.integral_integral_swap hg
  calc
    _ = D (fun s t => g s t + h s t) := by
      apply congrArg D
      funext s t
      by_cases hts : t ≤ s
      · simp [g,h,hts,not_lt_of_ge hts]
      · simp [g,h,hts,lt_of_not_ge hts]
    _ = D g + D h := dadd g h hg hh
    _ = D q + D h := congrArg (fun x => x+D h) hswap
    _ = D (fun s t => q s t+h s t) := (dadd q h hq hh).symm
    _ = ∫ u in 0..T, ∫ s in u..T, (f s u+f u s) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using hu
      calc
        _ = ∫ s in 0..T, if u ≤ s then (f s u+f u s) else 0 := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [volume.ae_ne u] with s hs hmem
          by_cases hus : u ≤ s
          · have hus' : u < s := lt_of_le_of_ne hus (Ne.symm hs)
            simp [q,g,h,hus,hus']
          · have hsu : s < u := lt_of_not_ge hus
            simp [q,g,h,hus,not_lt_of_ge hsu.le]
        _ = _ := upper_triangle_section (fun s => f s u+f u s) hu'
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      simpa only [add_zero, add_sub_cancel] using
        (intervalIntegral.integral_comp_add_left
          (f := fun s => f s u+f u s) (a := 0) (b := T-u) u).symm

omit [CompleteSpace E] in
/-- The exact covariance signs/order in P5 equation(B), for a supplied square
kernel integrability witness. Omega is fixed before either variable is chosen. -/
theorem bath_square_to_triangles [NormedSpace ℂ E]
    (A : ℝ → E) (Phi : ℝ → ℂ) (Omega : E → E → E)
    {T : ℝ} (hT : 0 ≤ T)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => Phi (p.2-p.1) • Omega (A p.1) (A p.2))
      (uIoc 0 T ×ˢ uIoc 0 T)) :
    (∫ s in 0..T, ∫ t in 0..T, Phi (t-s) • Omega (A s) (A t)) =
      ∫ u in 0..T, ∫ r in 0..(T-u),
        (Phi (-r) • Omega (A (u+r)) (A u) +
          Phi r • Omega (A u) (A (u+r))) := by
  have h := square_to_triangles (fun s t => Phi (t-s) • Omega (A s) (A t)) hT hf
  convert h using 1
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [show u-(u+r) = -r by ring, show (u+r)-u = r by ring]

end P5OriginalGenerator


open MeasureTheory Set

namespace P5OriginalGenerator

variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

noncomputable def omega (F B C : E) : E :=
  B*F*C - (1/2 : ℂ) • (B*C*F+F*(B*C))

theorem omega_unit_bound (F B C : E) (hB : ‖B‖ ≤ 1) (hC : ‖C‖ ≤ 1) :
    ‖omega F B C‖ ≤ 2*‖F‖ := by
  have hBC : ‖B*C‖ ≤ 1 := by
    calc
      _ ≤ ‖B‖*‖C‖ := norm_mul_le B C
      _ ≤ 1*1 := mul_le_mul hB hC (norm_nonneg C) (by norm_num)
      _ = 1 := by ring
  have hBF : ‖B*F‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖B‖*‖F‖ := norm_mul_le B F
      _ ≤ 1*‖F‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg F)
      _ = ‖F‖ := one_mul _
  have hBFC : ‖B*F*C‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖B*F‖*‖C‖ := norm_mul_le (B*F) C
      _ ≤ ‖F‖*1 := mul_le_mul hBF hC (norm_nonneg C) (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  have hBCF : ‖B*C*F‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖B*C‖*‖F‖ := norm_mul_le (B*C) F
      _ ≤ 1*‖F‖ := mul_le_mul_of_nonneg_right hBC (norm_nonneg F)
      _ = ‖F‖ := one_mul _
  have hFBC : ‖F*(B*C)‖ ≤ ‖F‖ := by
    calc
      _ ≤ ‖F‖*‖B*C‖ := norm_mul_le F (B*C)
      _ ≤ ‖F‖*1 := mul_le_mul_of_nonneg_left hBC (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  have hsum : ‖B*C*F+F*(B*C)‖ ≤ 2*‖F‖ := by
    have h := norm_add_le (B*C*F) (F*(B*C))
    linarith
  have hhalf : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num
  calc
    _ ≤ ‖B*F*C‖ + ‖(1/2 : ℂ) • (B*C*F+F*(B*C))‖ := norm_sub_le _ _
    _ = ‖B*F*C‖ + (1/2 : ℝ)*‖B*C*F+F*(B*C)‖ := by rw [norm_smul,hhalf]
    _ ≤ _ := by linarith

/-- The actual fixed-F ordered Omega kernel has a square L1 witness. Its
continuous operator factor has separable range because its DOMAIN is R x R. -/
theorem omega_square_integrable (F : E) (A : ℝ → E) (Phi : ℝ → ℂ)
    (T C0 : ℝ) (hT : 0 ≤ T) (hC0 : 0 ≤ C0) (hA : Continuous A)
    (hAnorm : ∀ t, ‖A t‖ ≤ 1) (hPhi : Measurable Phi)
    (hPhinorm : ∀ t, ‖Phi t‖ ≤ C0) :
    IntegrableOn
      (fun p : ℝ × ℝ => Phi (p.2-p.1) • omega F (A p.1) (A p.2))
      (uIoc 0 T ×ˢ uIoc 0 T) := by
  have hq : Continuous (fun p : ℝ × ℝ => omega F (A p.1) (A p.2)) := by
    unfold omega
    fun_prop
  have hb : StronglyMeasurable (fun p : ℝ × ℝ => Phi (p.2-p.1)) :=
    (hPhi.comp (measurable_snd.sub measurable_fst)).stronglyMeasurable
  have hk := hb.smul hq.stronglyMeasurable
  have hfinite : volume (uIoc 0 T ×ˢ uIoc 0 T) < ⊤ := by
    rw [uIoc_of_le hT]
    exact lt_of_le_of_lt
      (measure_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict (uIoc 0 T ×ˢ uIoc 0 T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite⟩
  apply (integrable_const (2*C0*‖F‖)).mono' hk.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  change ‖Phi (p.2-p.1) • omega F (A p.1) (A p.2)‖ ≤ 2*C0*‖F‖
  rw [norm_smul]
  calc
    _ ≤ C0*(2*‖F‖) := mul_le_mul (hPhinorm _) (omega_unit_bound F _ _ (hAnorm _) (hAnorm _))
      (norm_nonneg _) hC0
    _ = _ := by ring

theorem omega_square_to_triangles (F : E) (A : ℝ → E) (Phi : ℝ → ℂ)
    (T C0 : ℝ) (hT : 0 ≤ T) (hC0 : 0 ≤ C0) (hA : Continuous A)
    (hAnorm : ∀ t, ‖A t‖ ≤ 1) (hPhi : Measurable Phi)
    (hPhinorm : ∀ t, ‖Phi t‖ ≤ C0) :
    (∫ s in 0..T, ∫ t in 0..T, Phi (t-s) • omega F (A s) (A t)) =
      ∫ u in 0..T, ∫ r in 0..(T-u),
        (Phi (-r) • omega F (A (u+r)) (A u) + Phi r • omega F (A u) (A (u+r))) :=
  bath_square_to_triangles A Phi (omega F) hT
    (omega_square_integrable F A Phi T C0 hT hC0 hA hAnorm hPhi hPhinorm)

end P5OriginalGenerator
