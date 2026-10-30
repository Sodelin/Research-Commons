import Mathlib.Topology.Instances.AddCircle.Real
set_option debug.skipKernelTC false
namespace Nanuq.CircleLoop
open Set
variable {P : Type*} [TopologicalSpace P]

/-- Parameter conversion for the actual source's embedded AddCircle.
The full trace is retained, including the closing endpoint. -/
theorem interval_loop (r : AddCircle (1 : ℝ) → P)
    (hc : Continuous r) (hi : Function.Injective r) :
    ∃ f : ℝ → P, Continuous f ∧ f 0 = f 1 ∧
      InjOn f (Ico 0 1) ∧ f '' Icc 0 1 = range r := by
  refine ⟨fun t => r (t : AddCircle (1 : ℝ)),
    hc.comp (AddCircle.continuous_mk' _), ?_, ?_, ?_⟩
  · change r ((0:ℝ) : AddCircle (1:ℝ)) = r ((1:ℝ) : AddCircle (1:ℝ))
    rw [AddCircle.coe_period]
    rfl
  · intro x hx y hy he
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1:ℝ)) (a := 0) (by simpa using hx) (by simpa using hy)).mp (hi he)
  · change (r ∘ ((↑) : ℝ → AddCircle (1:ℝ))) '' Icc 0 1 = range r
    rw [Set.image_comp]
    have h : ((↑) : ℝ → AddCircle (1:ℝ)) '' Icc 0 1 = univ := by
      simpa using AddCircle.coe_image_Icc_eq (1:ℝ) (0:ℝ)
    rw [h, image_univ]

#print axioms interval_loop
end Nanuq.CircleLoop
