import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Module

/-
P5 equation (6), pure noncommutative algebra only.
Source: P5 GENERATOR-COMPARISON.md SHA256
74e821c317819bbac9a42fed61630b7e23685d3d657d8b837bf910deb8f71034.
This preserves the ordered Lamb-shift contribution and its minus sign.
No integral, bath, response estimate or P5 master conclusion is supplied.
-/
namespace P5OriginalGenerator

theorem ordered_triangle_identity {A : Type*} [Ring A] [Algebra ℂ A]
    (B C F : A) (zeta w : ℂ) :
    zeta • (B * F * C - (1 / 2 : ℂ) • (B * C * F + F * (B * C))) +
      w • (C * F * B - (1 / 2 : ℂ) • (C * B * F + F * (C * B))) -
      (1 / 2 : ℂ) •
        (zeta • (B * C * F - F * (B * C)) -
          w • (C * B * F - F * (C * B))) =
      w • ((C * F - F * C) * B) - zeta • (B * (C * F - F * C)) := by
  simp only [smul_sub, smul_add, mul_sub, sub_mul, mul_assoc]
  module

end P5OriginalGenerator
