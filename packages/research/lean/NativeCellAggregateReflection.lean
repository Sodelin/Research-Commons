import NativeCellFormReflection

/-!
Aggregate the existing CHART emitter into the existing source-typed compiler.
All input relations below concern individual fields, occurrence lists and
coordinate positions. No emitted-matrix equality is an input premise.
The captured request/parser/source admission and physical readout remain
separate obligations. Internal unit bookkeeping weights are erased explicitly.
-/
namespace Astra.NativeCellAggregateReflection

open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler
open UnifiedLean.G6.WireAffineRefinement
open Astra.NativeCellFormReflection

def eraseWeights (rows : List GParity.Affine.Row) : List GParity.Affine.Row :=
  rows.map (fun r => {r with weights := []})

theorem eraseWeights_append (a b : List GParity.Affine.Row) :
    eraseWeights (a ++ b) = eraseWeights a ++ eraseWeights b := by
  simp [eraseWeights]

theorem eraseWeights_flatMap {A : Type*} (xs : List A)
    (f : A → List GParity.Affine.Row) :
    eraseWeights (xs.flatMap f) = xs.flatMap (fun x => eraseWeights (f x)) := by
  simp [eraseWeights, List.map_flatMap]

theorem eraseWeights_comparison (cmp : GParity.Chart.Comparison)
    (f g : GParity.Chart.Form) :
    eraseWeights (GParity.Chart.comparisonRows cmp f g) =
      GParity.Chart.comparisonRows cmp f g := by
  cases cmp <;> rfl

theorem eraseWeights_scaled (c : GParity.Chart.Interval)
    (d u : GParity.Chart.Form) :
    eraseWeights (GParity.Chart.scaledRows c d u) =
      GParity.Chart.scaledRows c d u := by
  rcases c with ⟨lo,hi⟩
  cases lo <;> cases hi <;> rfl

theorem eraseWeights_bookkeeping (rows : List GParity.Affine.Row) :
    eraseWeights (rows.zipIdx.map (fun (r,i) =>
      {r with weights := (List.range rows.length).map (fun j => if i == j then 1 else 0)})) =
      eraseWeights rows := by
  apply List.ext_getElem
  · simp [eraseWeights]
  · intro i hi hj
    simp [eraseWeights]

theorem decodeRows_eraseWeights (n : ℕ) (rows : List GParity.Affine.Row) :
    decodeRows n (eraseWeights rows) = decodeRows n rows := by
  simp [decodeRows, eraseWeights, List.map_map, decodeRow]

theorem wellFormed_eraseWeights_iff (n : ℕ) (rows : List GParity.Affine.Row) :
    RowsWellFormed n (eraseWeights rows) ↔ RowsWellFormed n rows := by
  simp [RowsWellFormed, eraseWeights]

def reflectAge {V : Type*} (vertex : V → ℕ) : AgeAtom V → GParity.Chart.AgeAtom
  | .node v => .node (vertex v)
  | .fixed q => .fixed q

def reflectChronology {V : Type*} (vertex : V → ℕ) (c : AgeConstraint V) :
    GParity.Chart.AgeConstraint :=
  ⟨encodeComparison c.comparison, reflectAge vertex c.left, reflectAge vertex c.right⟩

def reflectExposure {V E : Type*} (vertex : V → ℕ) (edge : E → ℕ)
    (r : Exposure V E) : GParity.Chart.Exposure :=
  ⟨r.population.map edge, reflectAge vertex r.younger,
    reflectAge vertex r.older, encodeInterval r.cell⟩

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)
variable (input : GParity.Chart.Input)
variable (edges : List E) (leaves : List X) (populations : List (Option E))
variable (hybrids : List (Hybrid N)) (chronologyIds : List C) (exposureIds : List I)
variable (chronology : C → AgeConstraint V) (exposures : I → Exposure V E)
variable (coins : Hybrid N → RationalInterval)

structure FieldReflection where
  vertex : V → ℕ
  edge : E → ℕ
  hybrid : Hybrid N → ℕ
  dimension : input.source.dimension = n
  age_position : ∀ v, (layout (.inl v)).val = vertex v
  inverse_position : ∀ e, (layout (.inr (.inl e))).val =
    input.source.vertices + (e.map edge).getD input.source.edges.length
  coin_position : ∀ h, (layout (.inr (.inr h))).val =
    input.source.vertices + input.source.edges.length + 1 + hybrid h
  edge_fields : input.source.edges =
    edges.map (fun e => ⟨vertex (N.graph.source e), vertex (N.graph.target e)⟩)
  leaf_fields : input.source.leaves = leaves.map (fun x => vertex (N.leaf x))
  population_order : List.range (input.source.edges.length + 1) =
    populations.map (fun e => (e.map edge).getD input.source.edges.length)
  hybrid_order : List.range input.source.hybrids.length = hybrids.map hybrid
  chronology_fields : input.chronology =
    chronologyIds.map (fun j => reflectChronology vertex (chronology j))
  exposure_fields : input.exposures =
    exposureIds.map (fun i => reflectExposure vertex edge (exposures i))
  coin_fields : input.coins.zipIdx =
    hybrids.map (fun h => (encodeInterval (coins h), hybrid h))

variable {N layout input edges leaves populations hybrids chronologyIds exposureIds chronology exposures coins}
variable (h : FieldReflection N layout input edges leaves populations hybrids
  chronologyIds exposureIds chronology exposures coins)

theorem age_correspondence (a : AgeAtom V) :
    GParity.Chart.ageForm input.source (reflectAge h.vertex a) =
      encodeForm (ageForm N layout a) := by
  cases a with
  | node v => simp only [reflectAge, GParity.Chart.ageForm, ageForm,
      h.dimension, encodeForm_variable, h.age_position]
  | fixed q => simp only [reflectAge, GParity.Chart.ageForm, ageForm,
      h.dimension, encodeForm_const]

theorem inverse_correspondence (e : Option E) :
    GParity.Chart.Form.variable input.source.dimension
      (input.source.vertices + (e.map h.edge).getD input.source.edges.length) =
      encodeForm (inverseForm N layout e) := by
  simp only [inverseForm, encodeForm_variable, h.dimension, h.inverse_position]

theorem coin_correspondence (a : Hybrid N) :
    GParity.Chart.Form.variable input.source.dimension
      (input.source.vertices + input.source.edges.length + 1 + h.hybrid a) =
      encodeForm (coinForm N layout a) := by
  simp only [coinForm, encodeForm_variable, h.dimension, h.coin_position]

include h

theorem erase_emitRows_eq_encoded :
    eraseWeights (GParity.Chart.emitRows input) =
      encodeRows (compileCellList N layout edges leaves populations hybrids
        chronologyIds exposureIds chronology exposures coins) := by
  have he : input.source.edges.flatMap (fun e => GParity.Chart.comparisonRows .strict
      (GParity.Chart.Form.variable input.source.dimension e.target)
      (GParity.Chart.Form.variable input.source.dimension e.source)) =
      edges.flatMap (fun e => encodeRows (comparisonList .strict
        (ageForm N layout (.node (N.graph.target e)))
        (ageForm N layout (.node (N.graph.source e))))) := by
    rw [h.edge_fields]
    simp only [List.flatMap_map]
    congr 1
    funext e
    rw [← comparison_correspondence]
    simp only [encodeComparison, ageForm, encodeForm_variable, h.dimension, h.age_position]
  have hl : input.source.leaves.flatMap (fun v => GParity.Chart.comparisonRows .equal
      (GParity.Chart.Form.variable input.source.dimension v)
      (GParity.Chart.Form.const input.source.dimension 0)) =
      leaves.flatMap (fun x => encodeRows (comparisonList .equal
        (ageForm N layout (.node (N.leaf x))) (.const 0))) := by
    rw [h.leaf_fields]
    simp only [List.flatMap_map]
    congr 1
    funext x
    rw [← comparison_correspondence]
    simp only [encodeComparison, ageForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.age_position]
  have hp : (List.range (input.source.edges.length + 1)).flatMap (fun e =>
      GParity.Chart.comparisonRows .strict (GParity.Chart.Form.const input.source.dimension 0)
        (GParity.Chart.Form.variable input.source.dimension (input.source.vertices + e))) =
      populations.flatMap (fun e => encodeRows (comparisonList .strict
        (.const 0) (inverseForm N layout e))) := by
    rw [h.population_order]
    simp only [List.flatMap_map]
    congr 1
    funext e
    rw [← comparison_correspondence]
    simp only [encodeComparison, inverseForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.inverse_position]
  have h0 : (List.range input.source.hybrids.length).flatMap (fun a =>
      GParity.Chart.comparisonRows .strict (GParity.Chart.Form.const input.source.dimension 0)
        (GParity.Chart.Form.variable input.source.dimension
          (input.source.vertices + input.source.edges.length + 1 + a))) =
      hybrids.flatMap (fun a => encodeRows (comparisonList .strict (.const 0) (coinForm N layout a))) := by
    rw [h.hybrid_order]
    simp only [List.flatMap_map]
    congr 1
    funext a
    rw [← comparison_correspondence]
    simp only [encodeComparison, coinForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.coin_position]
  have h1 : (List.range input.source.hybrids.length).flatMap (fun a =>
      GParity.Chart.comparisonRows .strict
        (GParity.Chart.Form.variable input.source.dimension
          (input.source.vertices + input.source.edges.length + 1 + a))
        (GParity.Chart.Form.const input.source.dimension 1)) =
      hybrids.flatMap (fun a => encodeRows (comparisonList .strict (coinForm N layout a) (.const 1))) := by
    rw [h.hybrid_order]
    simp only [List.flatMap_map]
    congr 1
    funext a
    rw [← comparison_correspondence]
    simp only [encodeComparison, coinForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.coin_position]
  have hc : input.chronology.flatMap (fun c => GParity.Chart.comparisonRows c.kind
      (GParity.Chart.ageForm input.source c.left) (GParity.Chart.ageForm input.source c.right)) =
      chronologyIds.flatMap (fun j => encodeRows (comparisonList (chronology j).comparison
        (ageForm N layout (chronology j).left) (ageForm N layout (chronology j).right))) := by
    rw [h.chronology_fields]
    simp only [List.flatMap_map]
    congr 1
    funext j
    rw [← comparison_correspondence]
    simp only [reflectChronology, age_correspondence h]
  have hx : input.exposures.flatMap (fun e => GParity.Chart.scaledRows e.interval
      ((GParity.Chart.ageForm input.source e.older).sub (GParity.Chart.ageForm input.source e.younger))
      (GParity.Chart.Form.variable input.source.dimension
        (input.source.vertices + e.population.getD input.source.edges.length))) =
      exposureIds.flatMap (fun i => encodeRows (scaledList (exposures i).cell
        (durationForm N layout (exposures i)) (inverseForm N layout (exposures i).population))) := by
    rw [h.exposure_fields]
    simp only [List.flatMap_map]
    congr 1
    funext i
    rw [← scaled_correspondence]
    simp only [reflectExposure, age_correspondence h, inverse_correspondence h,
      durationForm, encodeForm_sub]
  have hb : input.coins.zipIdx.flatMap (fun (c,a) => GParity.Chart.scaledRows c
      (GParity.Chart.Form.variable input.source.dimension
        (input.source.vertices + input.source.edges.length + 1 + a))
      (GParity.Chart.Form.const input.source.dimension 1)) =
      hybrids.flatMap (fun a => encodeRows (scaledList (coins a)
        (coinForm N layout a) (.const 1))) := by
    rw [h.coin_fields]
    simp only [List.flatMap_map]
    congr 1
    funext a
    rw [← scaled_correspondence]
    rw [coin_correspondence h, encodeForm_const, h.dimension]
  unfold GParity.Chart.emitRows
  rw [eraseWeights_bookkeeping]
  simp only [eraseWeights_append, eraseWeights_flatMap,
    eraseWeights_comparison, eraseWeights_scaled]
  rw [he, hl, hp, h0, h1, hc, hx, hb]
  simp only [compileCellList, encodeRows, List.map_append, List.map_flatMap]

theorem decoded_emitRows_eq_compileCellList :
    decodeRows n (GParity.Chart.emitRows input) =
      compileCellList N layout edges leaves populations hybrids
        chronologyIds exposureIds chronology exposures coins := by
  rw [← decodeRows_eraseWeights n, erase_emitRows_eq_encoded h, decode_encodeRows]

theorem emitted_coefficient_lengths :
    RowsWellFormed n (GParity.Chart.emitRows input) := by
  apply (wellFormed_eraseWeights_iff n _).mp
  rw [erase_emitRows_eq_encoded h]
  exact encodedRows_wellFormed _

theorem decoded_emitRows_toFinset
    (hedges : ∀ e, e ∈ edges) (hleaves : ∀ x, x ∈ leaves)
    (hpopulations : ∀ e, e ∈ populations) (hhybrids : ∀ a, a ∈ hybrids)
    (hchronology : ∀ j, j ∈ chronologyIds) (hexposures : ∀ i, i ∈ exposureIds) :
    (decodeRows n (GParity.Chart.emitRows input)).toFinset =
      compileCell N layout chronology exposures coins := by
  rw [decoded_emitRows_eq_compileCellList h]
  exact compileCellList_toFinset N layout edges leaves populations hybrids
    chronologyIds exposureIds hedges hleaves hpopulations hhybrids
    hchronology hexposures chronology exposures coins

end Astra.NativeCellAggregateReflection
