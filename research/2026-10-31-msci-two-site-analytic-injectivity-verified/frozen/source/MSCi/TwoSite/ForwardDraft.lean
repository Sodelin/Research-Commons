import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
Preliminary source transcription for the fixed MSci two-site manuscript.

This file has NOT been compiled or kernel checked. It transcribes the pair
transforms from the retained 330-feature source, not a construction of the
six-sample genealogy or a proof that sequences have these expectations. The
existing cloud task owns compilation. See the accompanying README and
LEAN-OBLIGATIONS.md for source pins, obligations and limits.
-/

noncomputable section

namespace MSCi.TwoSite

/-- Times and pair rates in mutation-scaled units. -/
structure Parameters where
  h : ℝ
  t1 : ℝ
  t0 : ℝ
  rA : ℝ
  rB : ℝ
  rC : ℝ
  rAB : ℝ
  rR : ℝ
  g : ℝ

/-- The exact open fixed-family parameter domain. -/
def Admissible (p : Parameters) : Prop :=
  0 < p.h ∧ p.h < p.t1 ∧ p.t1 < p.t0 ∧
  0 < p.g ∧ p.g < 1 ∧
  0 < p.rA ∧ 0 < p.rB ∧ 0 < p.rC ∧ 0 < p.rAB ∧ 0 < p.rR

/-- Labels for the six pair transforms in the retained forward interface. -/
inductive Pair where
  | AC | AB | BC | AA | CC | BB
  deriving DecidableEq, Repr

/--
Transcribed analytic pair transform at `z`. Its intended correspondence to
the actual pair-coalescence law remains a separate, unproved obligation.
In particular, the B rate occurs on both sides of the pulse and the C rate
persists along the migrated C route. No rate-inequality case split is used.
-/
def pairTransform (p : Parameters) (pair : Pair) (z : ℝ) : ℝ :=
  let u := p.t1 - p.h
  let v := p.t0 - p.t1
  let E : ℝ → ℝ := fun t => Real.exp (-z * t)
  let S : ℝ → ℝ → ℝ := fun r l => Real.exp (-r * l)
  let H : ℝ → ℝ → ℝ := fun r l =>
    r / (r + z) * (1 - Real.exp (-(r + z) * l))
  let root := p.rR / (p.rR + z)
  let s := S p.rB p.h
  let b := S p.rB u
  let a := S p.rAB v
  let c1 := S p.rC (u + v)
  let a0 := S p.rA p.t1
  let c0 := S p.rC p.t0
  match pair with
  | .AC => E p.t0 * root
  | .AB =>
      (1 - p.g) * E p.t1 * H p.rAB v +
        (p.g + (1 - p.g) * a) * E p.t0 * root
  | .BC =>
      p.g * E p.h * H p.rC (u + v) +
        (1 - p.g + p.g * c1) * E p.t0 * root
  | .AA =>
      H p.rA p.t1 + a0 * E p.t1 * H p.rAB v +
        a0 * a * E p.t0 * root
  | .CC => H p.rC p.t0 + c0 * E p.t0 * root
  | .BB =>
      H p.rB p.h + s *
        ((1 - p.g) ^ 2 * E p.h * H p.rB u +
          p.g ^ 2 * E p.h * H p.rC (u + v) +
          (1 - p.g) ^ 2 * b * E p.t1 * H p.rAB v +
          ((1 - p.g) ^ 2 * b * a + p.g ^ 2 * c1 +
            2 * p.g * (1 - p.g)) * E p.t0 * root)

/-- The constant determined by the normalized JC observation channel. -/
def jcPairExponent : ℝ := 8 / 3

/-- Raw pair moments in the manuscript's specified nine-coordinate order. -/
def nineRawFeatures (p : Parameters) : Fin 9 → ℝ :=
  ![pairTransform p .AC jcPairExponent,
    pairTransform p .AC (2 * jcPairExponent),
    pairTransform p .CC jcPairExponent,
    pairTransform p .BC jcPairExponent,
    pairTransform p .BC (2 * jcPairExponent),
    pairTransform p .AB jcPairExponent,
    pairTransform p .AB (2 * jcPairExponent),
    pairTransform p .AA jcPairExponent,
    pairTransform p .BB jcPairExponent]

/--
Algebra used by the retained root-recovery argument: its ratio is strictly
above one for positive root rate and positive JC exponent. This candidate
proof has not been compiled or kernel checked.
-/
theorem rootRatio_gt_one (r c : ℝ) (hr : 0 < r) (hc : 0 < c) :
    (1 : ℝ) < (r + c) ^ 2 / (r * (r + 2 * c)) := by
  have hd : 0 < r * (r + 2 * c) := by positivity
  apply (lt_div_iff₀ hd).2
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  nlinarith

end MSCi.TwoSite
