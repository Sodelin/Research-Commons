import GParity.Chart
import G6NaturalCellOrderedCompiler

/-!
Value-level affine-form correspondence for the EXISTING CHART emitter.
This relates its coefficients/bounds/strictness to the source-typed row
constructors. It does not prove Rust execution, parser admission or the
complete original-source/ordered-emission relation.
-/
namespace Astra.NativeCellFormReflection

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler

variable {n : ℕ}

def encodeForm (f : Affine n) : GParity.Chart.Form :=
  ⟨List.ofFn f.coeff, f.constant⟩

theorem encodeForm_const (q : ℚ) :
    encodeForm (Affine.const (n := n) q) = GParity.Chart.Form.const n q := by
  apply congrArg₂ GParity.Chart.Form.mk
  · simp [encodeForm, Affine.const, GParity.Chart.Form.const]
  · rfl

theorem encodeForm_variable (i : Fin n) :
    encodeForm (Affine.variable i) = GParity.Chart.Form.variable n i.val := by
  apply congrArg₂ GParity.Chart.Form.mk
  · change List.ofFn (fun k : Fin n => if k = i then (1 : ℚ) else 0) =
      (List.range n).map (fun k => if i.val == k then (1 : ℚ) else 0)
    apply List.ext_getElem
    · simp
    · intro j hj hk
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      by_cases h : j = i.val
      · simp [Fin.ext_iff, h]
      · have hi : i.val ≠ j := Ne.symm h
        simp [Fin.ext_iff, h, hi]
  · rfl

theorem encodeForm_sub (f g : Affine n) :
    encodeForm (f.sub g) = (encodeForm f).sub (encodeForm g) := by
  apply congrArg₂ GParity.Chart.Form.mk
  · apply List.ext_getElem
    · simp [encodeForm, Affine.sub, GParity.Chart.Form.sub]
    · intro j hj hk
      simp_all [encodeForm, Affine.sub, GParity.Chart.Form.sub]
  · rfl

theorem encodeForm_scale (q : ℚ) (f : Affine n) :
    encodeForm (f.scale q) = (encodeForm f).scale q := by
  apply congrArg₂ GParity.Chart.Form.mk
  · apply List.ext_getElem
    · simp [encodeForm, Affine.scale, GParity.Chart.Form.scale]
    · intro j hj hk
      simp_all [encodeForm, Affine.scale, GParity.Chart.Form.scale]
  · rfl

theorem affineRow_correspondence (s : Bool) (f g : Affine n) :
    GParity.Chart.affineRow s (encodeForm f) (encodeForm g) =
      encodeRow (affineRow s f g) := by
  apply congrArg (fun coeff : List Rat =>
    (⟨coeff, g.constant - f.constant, s, []⟩ : GParity.Affine.Row))
  exact (congrArg GParity.Chart.Form.coeff (encodeForm_sub f g)).symm

def encodeComparison : AgeComparison → GParity.Chart.Comparison
  | .strict => .strict
  | .weak => .weak
  | .equal => .equal

def encodeBound (b : RationalBound) : GParity.Chart.Bound :=
  ⟨b.value, b.strict⟩

def encodeInterval (c : RationalInterval) : GParity.Chart.Interval :=
  ⟨c.lower.map encodeBound, c.upper.map encodeBound⟩

theorem comparison_correspondence (cmp : AgeComparison) (f g : Affine n) :
    GParity.Chart.comparisonRows (encodeComparison cmp) (encodeForm f) (encodeForm g) =
      encodeRows (comparisonList cmp f g) := by
  cases cmp with
  | strict =>
    change [GParity.Chart.affineRow true (encodeForm f) (encodeForm g)] =
      [encodeRow (affineRow true f g)]
    rw [affineRow_correspondence]
  | weak =>
    change [GParity.Chart.affineRow false (encodeForm f) (encodeForm g)] =
      [encodeRow (affineRow false f g)]
    rw [affineRow_correspondence]
  | equal =>
    change [GParity.Chart.affineRow false (encodeForm f) (encodeForm g),
      GParity.Chart.affineRow false (encodeForm g) (encodeForm f)] =
      [encodeRow (affineRow false f g), encodeRow (affineRow false g f)]
    rw [affineRow_correspondence, affineRow_correspondence]

theorem scaled_correspondence (c : RationalInterval) (d u : Affine n) :
    GParity.Chart.scaledRows (encodeInterval c) (encodeForm d) (encodeForm u) =
      encodeRows (scaledList c d u) := by
  rcases c with ⟨lo, hi⟩
  cases lo <;> cases hi <;>
    simp [encodeInterval, encodeBound, GParity.Chart.scaledRows,
      scaledList, encodeRows, ← encodeForm_scale, affineRow_correspondence]

end Astra.NativeCellFormReflection
