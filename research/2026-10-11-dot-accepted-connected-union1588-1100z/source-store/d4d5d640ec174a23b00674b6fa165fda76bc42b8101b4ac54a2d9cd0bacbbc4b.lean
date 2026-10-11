import G1OuterLabelledMultigraphCurves

/-! Concatenating two simple arcs with only their common endpoint in
common gives a simple arc. This is the actual splice/root-suppression
curve primitive; no straight-edge or all-vertices-outer assumption is used. -/
namespace G1SimpleCurveConcatenation
open Set
variable {P : Type*} [TopologicalSpace P] {a b c : P}

theorem actual_simple_path_concatenation (first : Path a b) (last : Path b c)
    (hf : Function.Injective first) (hl : Function.Injective last)
    (hmeet : ∀ t u, first t = last u → first t = b) : Function.Injective (first.trans last) := by
  intro t u he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with ht hu hu
  · have hv := congrArg Subtype.val (hf he)
    apply Subtype.ext
    change 2 * (t : ℝ) = 2 * (u : ℝ) at hv
    linarith
  · have hb := hmeet _ _ he
    have hfOne := hf (hb.trans first.target.symm)
    have hlZero := hl (he.symm.trans (hb.trans last.source.symm))
    have hv := congrArg Subtype.val hlZero
    have huval : 2 * (u : ℝ) - 1 = 0 := hv
    exfalso
    exact hu (by linarith)
  · have hb := hmeet _ _ he.symm
    have hlZero := hl (he.trans (hb.trans last.source.symm))
    have hv := congrArg Subtype.val hlZero
    have htval : 2 * (t : ℝ) - 1 = 0 := hv
    exfalso
    exact ht (by linarith)
  · have hv := congrArg Subtype.val (hl he)
    apply Subtype.ext
    change 2 * (t : ℝ) - 1 = 2 * (u : ℝ) - 1 at hv
    linarith

#print axioms actual_simple_path_concatenation
end G1SimpleCurveConcatenation
