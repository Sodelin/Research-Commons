import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Finite alternating-tail and I/COMMON pair algebra

Codex, 2026-10-14. SOURCE AUTHORED; COMPILATION UNVERIFIED.
No compiler, build, Lean query or integration materialization was executed.

The alternating result quantifies over every finite list, but its entries are
supplied real numbers. Identifying actual all-arity logarithm coefficients,
proving their ratio/monotonicity bounds, analytic logarithm and Newton-series
adapters, physical source admission, and the G4 master conclusion remain outside
this file. The pair definitions are the explicit I/COMMON pair polynomials;
their correspondence to an actual forest evaluator is a separate adapter.
-/

namespace G4LogGuardAlgebra

/-- The first sign is positive and each subsequent sign alternates. -/
def alternatingSum : List ℝ → ℝ
  | [] => 0
  | a :: terms => a - alternatingSum terms

/-- Zero for an empty tail, avoiding any nonempty-list premise. -/
def firstTerm : List ℝ → ℝ
  | [] => 0
  | a :: _ => a

/-- All-length finite bound for weakly decreasing, nonnegative terms.
`Pairwise` is oriented so every later term is at most every earlier term. -/
theorem alternatingSum_bounds (terms : List ℝ) :
    (∀ a ∈ terms, 0 ≤ a) →
    terms.Pairwise (fun a b => b ≤ a) →
    0 ≤ alternatingSum terms ∧ alternatingSum terms ≤ firstTerm terms := by
  induction terms with
  | nil =>
      intro _ _
      simp only [alternatingSum, firstTerm, le_refl, and_self]
  | cons a terms ih =>
      intro hNonneg hDecreasing
      have hFirstNonneg : 0 ≤ a := hNonneg a (by simp)
      obtain ⟨hAhead, hTailDecreasing⟩ := List.pairwise_cons.mp hDecreasing
      have hTailNonneg : ∀ b ∈ terms, 0 ≤ b := by
        intro b hb
        exact hNonneg b (by simp only [List.mem_cons]; exact Or.inr hb)
      have hTailBounds := ih hTailNonneg hTailDecreasing
      cases terms with
      | nil =>
          simpa only [alternatingSum, firstTerm, sub_zero] using
            (show 0 ≤ a ∧ a ≤ a from ⟨hFirstNonneg, le_rfl⟩)
      | cons b rest =>
          have hNextLe : b ≤ a := hAhead b (by simp)
          have hTailUpper : alternatingSum (b :: rest) ≤ b := by
            simpa only [firstTerm] using hTailBounds.2
          change 0 ≤ a - alternatingSum (b :: rest) ∧
            a - alternatingSum (b :: rest) ≤ a
          constructor
          · linarith [hTailUpper]
          · linarith [hTailBounds.1]

theorem alternatingSum_bounds_of_positive (terms : List ℝ)
    (hPositive : ∀ a ∈ terms, 0 < a)
    (hDecreasing : terms.Pairwise (fun a b => b ≤ a)) :
    0 ≤ alternatingSum terms ∧ alternatingSum terms ≤ firstTerm terms := by
  exact alternatingSum_bounds terms (fun a ha => le_of_lt (hPositive a ha)) hDecreasing

/-- Strictness comes from the leading coefficient and the explicit tail bound. -/
theorem negative_pair_plus_tail (t1 t2 tail : ℝ) (hFirst : 0 < t1)
    (hSecond : t2 = 2 * t1) (hTail : tail ≤ (2 / 3 : ℝ) * t1) :
    t1 - t2 + tail < 0 := by
  linarith

/-- Every finite decreasing tail is covered, including the empty list.
No claim that a physical logarithm supplies these hypotheses is implicit. -/
theorem negative_pair_with_decreasing_tail (t1 t2 : ℝ) (terms : List ℝ)
    (hFirst : 0 < t1) (hSecond : t2 = 2 * t1)
    (hNonneg : ∀ a ∈ terms, 0 ≤ a)
    (hDecreasing : terms.Pairwise (fun a b => b ≤ a))
    (hTailFirst : firstTerm terms ≤ (2 / 3 : ℝ) * t1) :
    t1 - t2 + alternatingSum terms < 0 := by
  have hBounds := alternatingSum_bounds terms hNonneg hDecreasing
  exact negative_pair_plus_tail t1 t2 (alternatingSum terms) hFirst hSecond
    (le_trans hBounds.2 hTailFirst)

/-- Independent parent choices, with merger-free cross-parent contribution. -/
def independentPairCoefficient (g x y : ℝ) : ℝ :=
  g ^ 2 * x + 2 * g * (1 - g) + (1 - g) ^ 2 * y

/-- One COMMON parent choice for the pair. -/
def commonPairCoefficient (g x y : ℝ) : ℝ := g * x + (1 - g) * y

theorem independent_common_gap (g x y : ℝ) :
    independentPairCoefficient g x y - commonPairCoefficient g x y =
      g * (1 - g) * (2 - x - y) := by
  unfold independentPairCoefficient commonPairCoefficient
  ring

theorem independent_exceeds_common (g x y : ℝ)
    (hgPositive : 0 < g) (hgBelow : g < 1) (hxBelow : x < 1) (hyBelow : y < 1) :
    commonPairCoefficient g x y < independentPairCoefficient g x y := by
  apply sub_pos.mp
  rw [independent_common_gap]
  exact mul_pos (mul_pos hgPositive (sub_pos.mpr hgBelow)) (by linarith)

theorem commonPairCoefficient_positive (g x y : ℝ)
    (hgPositive : 0 < g) (hgBelow : g < 1) (hxPositive : 0 < x)
    (hyPositive : 0 < y) : 0 < commonPairCoefficient g x y := by
  unfold commonPairCoefficient
  exact add_pos (mul_pos hgPositive hxPositive)
    (mul_pos (sub_pos.mpr hgBelow) hyPositive)

theorem independentPairCoefficient_positive (g x y : ℝ)
    (hgPositive : 0 < g) (hgBelow : g < 1)
    (hxPositive : 0 < x) (hxBelow : x < 1)
    (hyPositive : 0 < y) (hyBelow : y < 1) :
    0 < independentPairCoefficient g x y := by
  exact lt_trans
    (commonPairCoefficient_positive g x y hgPositive hgBelow hxPositive hyPositive)
    (independent_exceeds_common g x y hgPositive hgBelow hxBelow hyBelow)

/-- `q` is the product of the two endpoint pair-survival factors. -/
def paddedIndependentPair (q g x y : ℝ) : ℝ := q * independentPairCoefficient g x y

def paddedCommonPair (q g x y : ℝ) : ℝ := q * commonPairCoefficient g x y

/-- Endpoint factors are kept on the same tuple in both forcing regimes. -/
def endpointIndependentPair (a r g x y : ℝ) : ℝ :=
  a * independentPairCoefficient g x y * r

def endpointCommonPair (a r g x y : ℝ) : ℝ := a * commonPairCoefficient g x y * r

theorem endpoint_padding_is_product (a r g x y : ℝ) :
    endpointIndependentPair a r g x y = paddedIndependentPair (a * r) g x y ∧
    endpointCommonPair a r g x y = paddedCommonPair (a * r) g x y := by
  unfold endpointIndependentPair endpointCommonPair paddedIndependentPair paddedCommonPair
  constructor <;> ring

theorem padded_pair_gap (q g x y : ℝ) :
    paddedIndependentPair q g x y - paddedCommonPair q g x y =
      q * (g * (1 - g) * (2 - x - y)) := by
  unfold paddedIndependentPair paddedCommonPair independentPairCoefficient commonPairCoefficient
  ring

theorem padded_independent_exceeds_common (q g x y : ℝ) (hqPositive : 0 < q)
    (hgPositive : 0 < g) (hgBelow : g < 1) (hxBelow : x < 1) (hyBelow : y < 1) :
    paddedCommonPair q g x y < paddedIndependentPair q g x y := by
  exact mul_lt_mul_of_pos_left
    (independent_exceeds_common g x y hgPositive hgBelow hxBelow hyBelow) hqPositive

theorem padding_strictly_decreases_common (q g x y : ℝ) (hqBelow : q < 1)
    (hCommonPositive : 0 < commonPairCoefficient g x y) :
    paddedCommonPair q g x y < commonPairCoefficient g x y := by
  unfold paddedCommonPair
  simpa only [one_mul] using mul_lt_mul_of_pos_right hqBelow hCommonPositive

/-- A concrete aggregate padding matches the supplied positive I target,
places COMMON strictly below that same target, and strictly decreases COMMON
on exactly the same `(g,x,y)` tuple. The target must
be strictly smaller than this tuple's raw I pair coefficient. This theorem
does not choose new physical body parameters or split `q` into endpoints. -/
theorem ratio_padding_same_tuple (g x y target : ℝ)
    (hgPositive : 0 < g) (hgBelow : g < 1)
    (hxPositive : 0 < x) (hxBelow : x < 1)
    (hyPositive : 0 < y) (hyBelow : y < 1)
    (hTargetPositive : 0 < target)
    (hTargetBelow : target < independentPairCoefficient g x y) :
    let q := target / independentPairCoefficient g x y
    0 < q ∧ q < 1 ∧ paddedIndependentPair q g x y = target ∧
      paddedCommonPair q g x y < target ∧
      paddedCommonPair q g x y < commonPairCoefficient g x y := by
  have hCommonPositive :=
    commonPairCoefficient_positive g x y hgPositive hgBelow hxPositive hyPositive
  have hIndependentPositive := independentPairCoefficient_positive g x y
    hgPositive hgBelow hxPositive hxBelow hyPositive hyBelow
  have hIndependentNonzero : independentPairCoefficient g x y ≠ 0 :=
    ne_of_gt hIndependentPositive
  have hExact : (target / independentPairCoefficient g x y) *
      independentPairCoefficient g x y = target := by
    field_simp [hIndependentNonzero]
  have hPaddingPositive : 0 < target / independentPairCoefficient g x y :=
    div_pos hTargetPositive hIndependentPositive
  have hPaddingBelow : target / independentPairCoefficient g x y < 1 := by
    nlinarith
  change 0 < target / independentPairCoefficient g x y ∧
    target / independentPairCoefficient g x y < 1 ∧
    paddedIndependentPair (target / independentPairCoefficient g x y) g x y = target ∧
    paddedCommonPair (target / independentPairCoefficient g x y) g x y < target ∧
    paddedCommonPair (target / independentPairCoefficient g x y) g x y <
      commonPairCoefficient g x y
  refine ⟨hPaddingPositive, hPaddingBelow, ?_, ?_, ?_⟩
  · exact hExact
  · have hGap := padded_independent_exceeds_common
      (target / independentPairCoefficient g x y) g x y hPaddingPositive
      hgPositive hgBelow hxBelow hyBelow
    simpa only [paddedIndependentPair, hExact] using hGap
  · exact padding_strictly_decreases_common
      (target / independentPairCoefficient g x y) g x y hPaddingBelow hCommonPositive

end G4LogGuardAlgebra
