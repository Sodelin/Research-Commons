import FiniteSimplexAttainment
import ActualSourceCorruptionClasses

/-!
UNCHECKED source consumer, outside179. A competing actual native source
supplies nonemptiness; finite-simplex compactness constructs the minimizer.
Faithful biological image/TV-closure/effectivity/statistical bridges remain.
-/
namespace CloudG6.ActualSourceClosestCorruption

open MeasureTheory CloudG3.ActualCutJointLaw
open CloudG6.ActualSourceCorruptionClasses
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.CorruptionClasses
open UnifiedLean.G6.FiniteSimplexAttainment

universe u v w x y z
variable {Copy : Type w} {X : Type x} {Tag : Type y} {O : Type z}
variable [Fintype Copy] [DecidableEq Copy] [Fintype X]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
variable [Fintype O] {sample : Copy → X}

/-- Closest wrong-law attainment and sharp class boundary are derived for
the same actual native source image, with original Q/S labels and one fixed
observable-only reader. The closest law may be a limiting source law. -/
theorem actual_wrong_native_closest_boundary {Answer : Type*}
    (answer : OriginalTarget X → Answer) (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (beta : ℝ)
    (hwrong : ∃ r : OriginalParameters.{u,v,w,x} Copy X sample,
      answer (sourceTarget r) ≠ answer (sourceTarget s)) :
    ∃ closest ∈ coordinateClosedClass
        (wrongNativeImage answer (answer (sourceTarget s)) mode bin hbin reader),
      (∀ q ∈ coordinateClosedClass
          (wrongNativeImage answer (answer (sourceTarget s)) mode bin hbin reader),
        pmfTV (nativeLaw mode bin hbin reader s) closest ≤
          pmfTV (nativeLaw mode bin hbin reader s) q) ∧
      (allCorruptionsSeparated (nativeLaw mode bin hbin reader s)
          (coordinateClosedClass
            (wrongNativeImage answer (answer (sourceTarget s)) mode bin hbin reader)) beta ↔
        2 * beta < pmfTV (nativeLaw mode bin hbin reader s) closest) := by
  have hne : (wrongNativeImage answer (answer (sourceTarget s))
      mode bin hbin reader).Nonempty := by
    obtain ⟨r, hr⟩ := hwrong
    exact ⟨nativeLaw mode bin hbin reader r, r, hr, rfl⟩
  exact coordinate_class_corruption_boundary (nativeLaw mode bin hbin reader s)
    (wrongNativeImage answer (answer (sourceTarget s)) mode bin hbin reader) hne beta

#print axioms actual_wrong_native_closest_boundary

end CloudG6.ActualSourceClosestCorruption
