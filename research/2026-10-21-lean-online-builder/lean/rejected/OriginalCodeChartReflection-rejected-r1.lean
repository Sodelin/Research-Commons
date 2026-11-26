import OriginalCodeBankLayout
import NativeCellAggregateReflection

/-!
Use the EXISTING finite Code/decoder/registry directly for the existing CHART
value records. This supplies no byte-parser/native validator refinement or
new graph/admission factory. BinaryValid/RegistryValid remain real premises.
All original edges and parent occurrences retain their literal Fin positions.
-/
namespace Astra.OriginalCodeChartReflection

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler UnifiedLean.G6.WireAffineRefinement
open Astra.NativeCellFormReflection Astra.NativeCellAggregateReflection

theorem mapped_ofFn_eq_range {A : Type*} {k : ℕ}
    (f : Fin k → A) (g : A → ℕ) (h : ∀ i, g (f i) = i.val) :
    (List.ofFn f).map g = List.range k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range, h]

theorem zipIdx_ofFn_pairs {A : Type*} {k : ℕ} (f : Fin k → A) :
    (List.ofFn f).zipIdx = List.ofFn (fun i => (f i, i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
variable {nt nh nc ni : ℕ}

def edgeOrder (c : Code X ID) : List (NE (X:=X) (ID:=ID)) := List.ofFn id

def leafOrder (taxonOrder : X ≃ Fin nt) : List X := List.ofFn taxonOrder.symm

def populationOrder (c : Code X ID) : List (Option (NE (X:=X) (ID:=ID))) :=
  (edgeOrder c).map some ++ [none]

noncomputable def hybridOrder (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) : List (Hybrid (sourceOfValid c hb)) :=
  List.ofFn (fun i => decodedIDs c hb hr (idOrder.symm i))

def sourceOfCode (c : Code X ID) (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh) :
    GParity.Chart.Source where
  vertices := vertexCount (Fintype.card X) (Fintype.card ID)
  root := (codeRoot c).val
  edges := List.ofFn (fun e : NE (X:=X) (ID:=ID) =>
    ⟨((codeGraph c).source e).val, ((codeGraph c).target e).val⟩)
  leaves := List.ofFn (fun i => (codeLeaf c (taxonOrder.symm i)).val)
  hybrids := List.ofFn (fun i => ⟨(codeSite c (idOrder.symm i)).val,
    (codeParent c (idOrder.symm i) false).val,
    (codeParent c (idOrder.symm i) true).val⟩)

noncomputable def inputOfCode (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh)
    (chronology : Fin nc → AgeConstraint (NV (X:=X) (ID:=ID)))
    (exposures : Fin ni → Exposure (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)))
    (coins : Hybrid (sourceOfValid c hb) → RationalInterval) (cap : ℕ) :
    GParity.Chart.Input where
  source := sourceOfCode c taxonOrder idOrder
  chronology := List.ofFn (fun i => reflectChronology Fin.val (chronology i))
  exposures := List.ofFn (fun i => reflectExposure Fin.val Fin.val (exposures i))
  coins := List.ofFn (fun i => encodeInterval (coins (decodedIDs c hb hr (idOrder.symm i))))
  cap := cap

theorem edge_values (c : Code X ID) :
    (edgeOrder c).map Fin.val = List.range (edgeCount (Fintype.card X) (Fintype.card ID)) :=
  mapped_ofFn_eq_range id Fin.val (by intro i; rfl)

variable (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
variable (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh)
variable (chronology : Fin nc → AgeConstraint (NV (X:=X) (ID:=ID)))
variable (exposures : Fin ni → Exposure (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)))
variable (coins : Hybrid (sourceOfValid c hb) → RationalInterval) (cap : ℕ)

/-- Every relation is constructed from the literal Code and exact occurrence
orders, rather than supplied as a claimed emitted-matrix equality. -/
noncomputable def fieldReflection :
    FieldReflection (sourceOfValid c hb) (Astra.OriginalCodeBankLayout.layout c hb hr idOrder)
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)
      (edgeOrder c) (leafOrder taxonOrder) (populationOrder c)
      (hybridOrder c hb hr idOrder) (List.ofFn id) (List.ofFn id)
      chronology exposures coins where
  vertex := Fin.val
  edge := Fin.val
  hybrid := fun h => (idOrder ((decodedIDs c hb hr).symm h)).val
  dimension := by simp [inputOfCode, sourceOfCode, GParity.Chart.Source.dimension]
  age_position v := Astra.OriginalCodeBankLayout.age_position c hb hr idOrder v
  inverse_position e := by
    cases e with
    | none => simp [inputOfCode, sourceOfCode, Astra.OriginalCodeBankLayout.ancestral_position]
    | some e => simp [inputOfCode, sourceOfCode, Astra.OriginalCodeBankLayout.edge_position]
  coin_position h := by
    have p := Astra.OriginalCodeBankLayout.hybrid_position c hb hr idOrder
      ((decodedIDs c hb hr).symm h)
    simpa [inputOfCode, sourceOfCode] using p
  edge_fields := by
    apply List.ext_getElem
    · simp [inputOfCode, sourceOfCode, edgeOrder]
    · intro i hi hj
      simp [inputOfCode, sourceOfCode, edgeOrder, sourceOfValid, codeGraph]
  leaf_fields := by
    apply List.ext_getElem
    · simp [inputOfCode, sourceOfCode, leafOrder]
    · intro i hi hj
      simp [inputOfCode, sourceOfCode, leafOrder, sourceOfValid]
  population_order := by
    simpa [inputOfCode, sourceOfCode, populationOrder, List.map_map, edge_values]
      using (List.range_succ (edgeCount (Fintype.card X) (Fintype.card ID)))
  hybrid_order := by
    simp only [inputOfCode, sourceOfCode, List.length_ofFn]
    symm
    exact mapped_ofFn_eq_range _ _ (by intro i; simp)
  chronology_fields := by simp [inputOfCode, List.map_ofFn]
  exposure_fields := by simp [inputOfCode, List.map_ofFn]
  coin_fields := by simp [inputOfCode, hybridOrder, zipIdx_ofFn_pairs, List.map_ofFn]

theorem edgeOrder_complete : ∀ e, e ∈ edgeOrder c := by
  intro e
  exact List.mem_ofFn.mpr ⟨e,rfl⟩

theorem leafOrder_complete : ∀ x, x ∈ leafOrder taxonOrder := by
  intro x
  exact List.mem_ofFn.mpr ⟨taxonOrder x, by simp⟩

theorem populationOrder_complete : ∀ e, e ∈ populationOrder c := by
  intro e
  cases e with
  | none => simp [populationOrder]
  | some e =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨e, edgeOrder_complete c e, rfl⟩

theorem hybridOrder_complete : ∀ h, h ∈ hybridOrder c hb hr idOrder := by
  intro h
  exact List.mem_ofFn.mpr ⟨idOrder ((decodedIDs c hb hr).symm h), by simp⟩

theorem decoded_emitRows_of_code :
    decodeRows _ (GParity.Chart.emitRows
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)) =
      compileCellList (sourceOfValid c hb) (Astra.OriginalCodeBankLayout.layout c hb hr idOrder)
        (edgeOrder c) (leafOrder taxonOrder) (populationOrder c) (hybridOrder c hb hr idOrder)
        (List.ofFn id) (List.ofFn id) chronology exposures coins :=
  decoded_emitRows_eq_compileCellList (fieldReflection c hb hr taxonOrder idOrder
    chronology exposures coins cap)

theorem coefficient_lengths_of_code :
    RowsWellFormed _ (GParity.Chart.emitRows
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)) :=
  emitted_coefficient_lengths (fieldReflection c hb hr taxonOrder idOrder
    chronology exposures coins cap)

theorem decoded_emitRows_toFinset_of_code :
    (decodeRows _ (GParity.Chart.emitRows
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap))).toFinset =
      compileCell (sourceOfValid c hb) (Astra.OriginalCodeBankLayout.layout c hb hr idOrder)
        chronology exposures coins := by
  apply decoded_emitRows_toFinset (fieldReflection c hb hr taxonOrder idOrder
    chronology exposures coins cap)
  · exact edgeOrder_complete c
  · exact leafOrder_complete taxonOrder
  · exact populationOrder_complete c
  · exact hybridOrder_complete c hb hr idOrder
  · intro i; exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · intro i; exact List.mem_ofFn.mpr ⟨i,rfl⟩

end Astra.OriginalCodeChartReflection
