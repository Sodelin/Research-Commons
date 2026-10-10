import G6NaturalCellOrderedCompiler
import GParity.Chart
import G6WireAffineCapSemantics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# An actual typed two-tip source binds the native CHART matrix

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
This fixture proves source admission for this concrete `RootedBinary`, uses
the explicit original-ID BankVar layout, and compares the actual native
`emitRows` result with the inherited source compiler. No general parser,
reachability-validator or active-chart completeness theorem follows.
-/
namespace UnifiedLean.G6.TwoTipChartFixture

open Nanuq.Source GProgram.G5
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler
open UnifiedLean.G6.RationalNaturalCellWitness
open UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.Source.NativeParentRouting

def graph : EdgeGraph (Fin 3) (Fin 2) :=
  ⟨fun _ => 0, fun e => e.succ⟩

def leaf : Fin 2 ↪ Fin 3 :=
  ⟨Fin.succ, by intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)⟩

theorem step_rank {a b : Fin 3} (h : graph.DStep a b) : a.val < b.val := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [graph]

theorem path_rank {a b : Fin 3} (h : Relation.TransGen graph.DStep a b) :
    a.val < b.val := by
  induction h with
  | single h => exact step_rank h
  | tail _ h ih => exact lt_trans ih (step_rank h)

theorem graph_acyclic : graph.Acyclic := by
  intro a ha
  exact (lt_irrefl _) (path_rank ha)

theorem graph_rooted : ∀ a, graph.DReach 0 a := by
  intro a
  fin_cases a
  · exact .refl
  · exact .single ⟨0, rfl, rfl⟩
  · exact .single ⟨1, rfl, rfl⟩

theorem graph_least_stable :
    ∀ a, (∀ x, graph.Dominates 0 a (leaf x)) → a = 0 := by
  intro a h
  fin_cases a
  · rfl
  · exact False.elim (h 1 ⟨by decide, by decide,
      .single ⟨⟨1, rfl, rfl⟩, by decide, by decide⟩⟩)
  · exact False.elim (h 0 ⟨by decide, by decide,
      .single ⟨⟨0, rfl, rfl⟩, by decide, by decide⟩⟩)

def source : RootedBinary (Fin 3) (Fin 2) (Fin 2) where
  graph := graph
  root := 0
  leaf := leaf
  at_least_two_taxa := by decide
  root_degrees := by decide
  leaf_degrees := by decide
  internal_degrees := by
    intro a hroot hleaf
    fin_cases a
    · exact False.elim (hroot rfl)
    · exact False.elim (hleaf 0 rfl)
    · exact False.elim (hleaf 1 rfl)
  acyclic := graph_acyclic
  rooted := graph_rooted
  least_stable := graph_least_stable

theorem noHybrid (h : Hybrid source) : False := by
  have hn : ∀ v : Fin 3, ¬ graph.IsHybrid v := by
    intro v
    unfold EdgeGraph.IsHybrid
    fin_cases v <;> decide
  exact hn h.val h.property

def encodeVar : BankVar source → Fin 6
  | .inl v => ⟨v.val, by omega⟩
  | .inr (.inl (some e)) => ⟨3 + e.val, by omega⟩
  | .inr (.inl none) => 5
  | .inr (.inr h) => False.elim (noHybrid h)

def decodeIndex (i : Fin 6) : BankVar source :=
  if h : i.val < 3 then .inl ⟨i.val, h⟩
  else if h' : i.val < 5 then .inr (.inl (some ⟨i.val - 3, by omega⟩))
  else .inr (.inl none)

def layout : BankVar source ≃ Fin 6 where
  toFun := encodeVar
  invFun := decodeIndex
  left_inv := by
    intro b
    cases b with
    | inl v => fin_cases v <;> rfl
    | inr b =>
      cases b with
      | inl e =>
        cases e with
        | none => rfl
        | some e => fin_cases e <;> rfl
      | inr h => exact False.elim (noHybrid h)
  right_inv := by intro i; fin_cases i <;> rfl

def chronology : Fin 0 → AgeConstraint (Fin 3) := Fin.elim0
def exposures : Fin 0 → Exposure (Fin 3) (Fin 2) := Fin.elim0
def coins : Hybrid source → RationalInterval := fun h => False.elim (noHybrid h)

def emitted : List (Row 6) :=
  compileCellList source layout [0, 1] [0, 1] [some 0, some 1, none]
    [] [] [] chronology exposures coins

theorem emitted_toFinset :
    emitted.toFinset = compileCell source layout chronology exposures coins := by
  apply compileCellList_toFinset
  · intro e; fin_cases e <;> simp
  · intro x; fin_cases x <;> simp
  · intro e
    cases e with
    | none => simp
    | some e => fin_cases e <;> simp
  · intro h; exact False.elim (noHybrid h)
  · intro j; exact Fin.elim0 j
  · intro i; exact Fin.elim0 i

def nativeSource : GParity.Chart.Source :=
  ⟨3, 0, [⟨0, 1⟩, ⟨0, 2⟩], [1, 2], []⟩

def nativeInput : GParity.Chart.Input :=
  ⟨nativeSource, [], [], [], 4096⟩

theorem nativeSource_valid : nativeSource.valid = true := by decide

theorem affineRow_ext {n : Nat} {a b : Row n}
    (hc : a.coeff = b.coeff) (hb : a.bound = b.bound) (hs : a.strict = b.strict) :
    a = b := by
  cases a
  cases b
  cases hc
  cases hb
  cases hs
  rfl

/-- Native multiplier bookkeeping is erased only after actual row emission.
Every coefficient, bound and strictness bit is compared with the typed source
compiler at the explicit original-ID bank layout. -/
theorem nativeRows_eq_emitted :
    decodeRows 6 (GParity.Chart.emitRows nativeInput) = emitted := by
  apply List.ext_getElem
  · decide
  · intro i hi hj
    have hlen : (decodeRows 6 (GParity.Chart.emitRows nativeInput)).length = 9 := by decide
    have hi9 : i < 9 := by omega
    interval_cases i <;>
      apply affineRow_ext <;>
      try (funext j; fin_cases j) <;>
      rfl

theorem nativeRows_toFinset :
    (decodeRows 6 (GParity.Chart.emitRows nativeInput)).toFinset =
      compileCell source layout chronology exposures coins := by
  rw [nativeRows_eq_emitted, emitted_toFinset]

theorem nativeRows_wellFormed :
    RowsWellFormed 6 (GParity.Chart.emitRows nativeInput) := by
  unfold RowsWellFormed
  decide

/-- For this admitted original source, the actual native certificate is a
certificate of its original shared bank, not merely a stand-alone matrix. -/
theorem nativeWitness_checked (x : List Rat)
    (hx : GParity.Affine.checkWitness 6 (GParity.Chart.emitRows nativeInput) x = true) :
    checkOriginalCellWitness source layout chronology exposures coins (decodeVector 6 x) = true := by
  apply (UnifiedLean.G6.RationalAffineWitness.checkRationalWitness_correct _ _).mpr
  have h := ((checkWitness_correct 6 _ nativeRows_wellFormed x).mp hx).2
  simpa only [nativeRows_toFinset] using h

noncomputable def nativeWitnessBank (x : List Rat)
    (hx : GParity.Affine.checkWitness 6 (GParity.Chart.emitRows nativeInput) x = true) :
    OriginalCellBank source chronology exposures coins :=
  checkedOriginalCellBank source layout chronology exposures coins (decodeVector 6 x)
    (nativeWitness_checked x hx)

/-- The second shared fixture is `chart_two_tip_typed_cells.req`: one literal
root-age tie, two original edge hazard cells, and the shared ancestral cell. -/
def weakInterval (lo hi : ℚ) : RationalInterval :=
  ⟨some ⟨lo, false⟩, some ⟨hi, false⟩⟩

def typedChronology : Fin 1 → AgeConstraint (Fin 3) :=
  fun _ => ⟨.node 0, .fixed 2, .equal⟩

def typedExposures (i : Fin 3) : Exposure (Fin 3) (Fin 2) :=
  if i = 0 then ⟨some 0, .node 1, .node 0, weakInterval 1 4⟩
  else if i = 1 then ⟨some 1, .node 2, .node 0, weakInterval 1 4⟩
  else ⟨none, .fixed 2, .fixed 3, weakInterval 1 2⟩

def typedEmitted : List (Row 6) :=
  compileCellList source layout [0, 1] [0, 1] [some 0, some 1, none]
    [] [0] [0, 1, 2] typedChronology typedExposures coins

theorem typedEmitted_toFinset :
    typedEmitted.toFinset = compileCell source layout typedChronology typedExposures coins := by
  apply compileCellList_toFinset
  · intro e; fin_cases e <;> simp
  · intro x; fin_cases x <;> simp
  · intro e
    cases e with
    | none => simp
    | some e => fin_cases e <;> simp
  · intro h; exact False.elim (noHybrid h)
  · intro j; fin_cases j <;> simp
  · intro i; fin_cases i <;> simp

def nativeWeakInterval (lo hi : Rat) : GParity.Chart.Interval :=
  ⟨some ⟨lo, false⟩, some ⟨hi, false⟩⟩

def nativeTypedInput : GParity.Chart.Input :=
  ⟨nativeSource, [⟨.equal, .node 0, .fixed 2⟩],
    [⟨some 0, .node 1, .node 0, nativeWeakInterval 1 4⟩,
     ⟨some 1, .node 2, .node 0, nativeWeakInterval 1 4⟩,
     ⟨none, .fixed 2, .fixed 3, nativeWeakInterval 1 2⟩], [], 4096⟩

theorem nativeTypedRows_eq_emitted :
    decodeRows 6 (GParity.Chart.emitRows nativeTypedInput) = typedEmitted := by
  apply List.ext_getElem
  · decide
  · intro i hi hj
    have hlen : (decodeRows 6 (GParity.Chart.emitRows nativeTypedInput)).length = 17 := by decide
    have hi17 : i < 17 := by omega
    interval_cases i <;>
      apply affineRow_ext <;>
      try (funext j; fin_cases j) <;>
      rfl

theorem nativeTypedRows_toFinset :
    (decodeRows 6 (GParity.Chart.emitRows nativeTypedInput)).toFinset =
      compileCell source layout typedChronology typedExposures coins := by
  rw [nativeTypedRows_eq_emitted, typedEmitted_toFinset]

theorem nativeTypedRows_wellFormed :
    RowsWellFormed 6 (GParity.Chart.emitRows nativeTypedInput) := by
  unfold RowsWellFormed
  decide

theorem nativeTypedWitness_checked (x : List Rat)
    (hx : GParity.Affine.checkWitness 6 (GParity.Chart.emitRows nativeTypedInput) x = true) :
    checkOriginalCellWitness source layout typedChronology typedExposures coins
      (decodeVector 6 x) = true := by
  apply (UnifiedLean.G6.RationalAffineWitness.checkRationalWitness_correct _ _).mpr
  have h := ((checkWitness_correct 6 _ nativeTypedRows_wellFormed x).mp hx).2
  simpa only [nativeTypedRows_toFinset] using h

noncomputable def nativeTypedWitnessBank (x : List Rat)
    (hx : GParity.Affine.checkWitness 6 (GParity.Chart.emitRows nativeTypedInput) x = true) :
    OriginalCellBank source typedChronology typedExposures coins :=
  checkedOriginalCellBank source layout typedChronology typedExposures coins (decodeVector 6 x)
    (nativeTypedWitness_checked x hx)

#eval GParity.Chart.matrix nativeInput (GParity.Chart.emitRows nativeInput)
#eval (solveOriginalCell source layout chronology exposures coins).map List.ofFn
#eval GParity.Chart.matrix nativeTypedInput (GParity.Chart.emitRows nativeTypedInput)
#eval (solveOriginalCell source layout typedChronology typedExposures coins).map List.ofFn
#eval UnifiedLean.G6.WireAffineCapSemantics.requiredCap 6 (GParity.Chart.emitRows nativeTypedInput)

#print axioms source
#print axioms layout
#print axioms nativeSource_valid
#print axioms nativeRows_eq_emitted
#print axioms nativeRows_toFinset
#print axioms nativeWitness_checked
#print axioms nativeWitnessBank
#print axioms nativeTypedRows_eq_emitted
#print axioms nativeTypedRows_toFinset
#print axioms nativeTypedWitness_checked
#print axioms nativeTypedWitnessBank

end UnifiedLean.G6.TwoTipChartFixture
