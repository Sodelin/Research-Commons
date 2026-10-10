import G6RationalNaturalCellWitness
import G6WireContradictionRefinement

/-!
# Ordered source-cell emission preserves the exact inherited compiler

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
The caller supplies effective complete lists of the original registries and
the original bijective bank layout. Lists may repeat entries; their finite-set
erasure is exactly `compileCell`. Row weights are absent from affine semantics.
This supplies a source-typed interface; automatic raw graph admission, active
exposure coverage and nonlinear law recognition are separate obligations.
-/
namespace UnifiedLean.G6.NaturalCellOrderedCompiler

open Nanuq.Source GProgram.G5
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.RationalNaturalCellWitness
open UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.WireContradictionRefinement
open UnifiedLean.Source.NativeParentRouting

def comparisonList {n : ℕ} (cmp : AgeComparison) (f g : Affine n) : List (Row n) :=
  match cmp with
  | .strict => [affineRow true f g]
  | .weak => [affineRow false f g]
  | .equal => [affineRow false f g, affineRow false g f]

theorem comparisonList_toFinset {n : ℕ} (cmp : AgeComparison) (f g : Affine n) :
    (comparisonList cmp f g).toFinset = comparisonRows cmp f g := by
  cases cmp <;> simp [comparisonList, comparisonRows]

def scaledList {n : ℕ} (c : RationalInterval) (d u : Affine n) : List (Row n) :=
  (match c.lower with | none => [] | some b => [affineRow b.strict (u.scale b.value) d]) ++
  (match c.upper with | none => [] | some b => [affineRow b.strict d (u.scale b.value)])

theorem scaledList_toFinset {n : ℕ} (c : RationalInterval) (d u : Affine n) :
    (scaledList c d u).toFinset = scaledRows c d u := by
  rcases c with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp [scaledList, scaledRows]

theorem flatMap_toFinset_univ {A B : Type*} [Fintype A] [DecidableEq B]
    (xs : List A) (hxs : ∀ a, a ∈ xs) (f : A → List B) :
    (xs.flatMap f).toFinset = Finset.univ.biUnion (fun a => (f a).toFinset) := by
  ext b
  simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, _, hb⟩
    exact ⟨a, hb⟩
  · rintro ⟨a, hb⟩
    exact ⟨a, hxs a, hb⟩

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)

def compileCellList (edges : List E) (leaves : List X) (populations : List (Option E))
    (hybrids : List (Hybrid N)) (chronologyIds : List C) (exposureIds : List I)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : List (Row n) :=
  edges.flatMap (fun e => comparisonList .strict
    (ageForm N layout (.node (N.graph.target e)))
    (ageForm N layout (.node (N.graph.source e)))) ++
  leaves.flatMap (fun x => comparisonList .equal
    (ageForm N layout (.node (N.leaf x))) (.const 0)) ++
  populations.flatMap (fun e => comparisonList .strict (.const 0) (inverseForm N layout e)) ++
  hybrids.flatMap (fun h => comparisonList .strict (.const 0) (coinForm N layout h)) ++
  hybrids.flatMap (fun h => comparisonList .strict (coinForm N layout h) (.const 1)) ++
  chronologyIds.flatMap (fun j => comparisonList (chronology j).comparison
    (ageForm N layout (chronology j).left) (ageForm N layout (chronology j).right)) ++
  exposureIds.flatMap (fun i => scaledList (rows i).cell (durationForm N layout (rows i))
    (inverseForm N layout (rows i).population)) ++
  hybrids.flatMap (fun h => scaledList (coins h) (coinForm N layout h) (.const 1))

/-- This fixes the emitted matrix mathematically, without assigning the
inherited finite set a fictitious canonical list order. -/
theorem compileCellList_toFinset (edges : List E) (leaves : List X)
    (populations : List (Option E)) (hybrids : List (Hybrid N))
    (chronologyIds : List C) (exposureIds : List I)
    (hedges : ∀ e, e ∈ edges) (hleaves : ∀ x, x ∈ leaves)
    (hpopulations : ∀ e, e ∈ populations) (hhybrids : ∀ h, h ∈ hybrids)
    (hchronology : ∀ j, j ∈ chronologyIds) (hexposures : ∀ i, i ∈ exposureIds)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) :
    (compileCellList N layout edges leaves populations hybrids chronologyIds exposureIds
      chronology rows coins).toFinset = compileCell N layout chronology rows coins := by
  simp only [compileCellList, List.toFinset_append,
    flatMap_toFinset_univ edges hedges, flatMap_toFinset_univ leaves hleaves,
    flatMap_toFinset_univ populations hpopulations,
    flatMap_toFinset_univ hybrids hhybrids,
    flatMap_toFinset_univ chronologyIds hchronology,
    flatMap_toFinset_univ exposureIds hexposures,
    comparisonList_toFinset, scaledList_toFinset, compileCell, chronologyRows]

def encodeRow {n : ℕ} (r : Row n) : GParity.Affine.Row :=
  ⟨List.ofFn r.coeff, r.bound, r.strict, []⟩

def encodeRows {n : ℕ} (rows : List (Row n)) : List GParity.Affine.Row :=
  rows.map encodeRow

theorem decodeVector_ofFn {n : ℕ} (x : Fin n → ℚ) :
    decodeVector n (List.ofFn x) = x := by
  funext i
  simp [decodeVector, List.getElem?_ofFn, i.isLt]

theorem decode_encodeRow {n : ℕ} (r : Row n) :
    decodeRow n (encodeRow r) = r := by
  cases r
  simp only [decodeRow, encodeRow, decodeVector_ofFn]

theorem decode_encodeRows {n : ℕ} (rows : List (Row n)) :
    decodeRows n (encodeRows rows) = rows := by
  simp only [decodeRows, encodeRows, List.map_map, Function.comp_def, decode_encodeRow,
    List.map_id_fun']
  rfl

theorem encodedRows_wellFormed {n : ℕ} (rows : List (Row n)) :
    RowsWellFormed n (encodeRows rows) := by
  intro r hr
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
  exact List.length_ofFn

/-- Any actual native positive checker success realizes the shared original
bank whenever the emitted typed rows erase to the inherited compiler. -/
theorem nativeCompiledWitness_checked (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval)
    (emitted : List (Row n))
    (hemit : emitted.toFinset = compileCell N layout chronology rows coins)
    (x : List Rat) (hx : GParity.Affine.checkWitness n (encodeRows emitted) x = true) :
    checkOriginalCellWitness N layout chronology rows coins (decodeVector n x) = true := by
  apply (UnifiedLean.G6.RationalAffineWitness.checkRationalWitness_correct _ _).mpr
  have h := ((checkWitness_correct n (encodeRows emitted) (encodedRows_wellFormed emitted) x).mp hx).2
  simpa only [decode_encodeRows, hemit] using h

noncomputable def nativeCompiledBank (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval)
    (emitted : List (Row n))
    (hemit : emitted.toFinset = compileCell N layout chronology rows coins)
    (x : List Rat) (hx : GParity.Affine.checkWitness n (encodeRows emitted) x = true) :
    OriginalCellBank N chronology rows coins :=
  checkedOriginalCellBank N layout chronology rows coins (decodeVector n x)
    (nativeCompiledWitness_checked N layout chronology rows coins emitted hemit x hx)

/-- Native exclusion transfers to the supplied original cell through exact
row emission. It supplies no exclusion for unenumerated sources or charts. -/
theorem nativeCompiledContradiction_excludes (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval)
    (emitted : List (Row n))
    (hemit : emitted.toFinset = compileCell N layout chronology rows coins)
    (weights : List Rat) (hw : weights.length = (encodeRows emitted).length)
    (h : GParity.Affine.checkContradiction n (encodeRows emitted) weights = true) :
    ¬ originalCellFeasible N chronology rows coins := by
  have hn := checkedWireContradiction_excludes_real n (encodeRows emitted)
    (encodedRows_wellFormed emitted) weights hw h
  intro ho
  apply hn
  rw [decode_encodeRows, hemit]
  exact (inverse_cell_iff_compiled N layout chronology rows coins).mp
    ((original_cell_iff_inverse N chronology rows coins).mp ho)

#print axioms compileCellList_toFinset
#print axioms decode_encodeRows
#print axioms nativeCompiledWitness_checked
#print axioms nativeCompiledBank
#print axioms nativeCompiledContradiction_excludes

end UnifiedLean.G6.NaturalCellOrderedCompiler
