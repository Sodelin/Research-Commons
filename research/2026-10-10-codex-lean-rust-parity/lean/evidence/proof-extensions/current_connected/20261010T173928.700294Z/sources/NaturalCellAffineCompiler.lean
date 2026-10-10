import StrictAffineElimination
import G6NaturalCellInverseRates

/-! Source-rooted finite natural-cell compiler, contributed by dot, 2026-10-09.
The original typed calendar/rate/inheritance constraints are emitted as a finite
rational matrix and recognized by the proved arithmetic decider. Inputs include
an effective finite chart and explicit bijective variable layout; graph admission,
complete chart generation, and full G6 image assembly remain separate.
Exact review and compiler status are recorded in accompanying receipts. -/
namespace UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open scoped BigOperators

structure Affine (n : ℕ) where
  coeff : Fin n → ℚ
  constant : ℚ

def Affine.eval {n : ℕ} (f : Affine n) (x : Fin n → ℝ) : ℝ :=
  (f.constant : ℝ) + ∑ i, (f.coeff i : ℝ)*x i

def Affine.const {n : ℕ} (q : ℚ) : Affine n := ⟨fun _ => 0,q⟩
def Affine.variable {n : ℕ} (i : Fin n) : Affine n :=
  ⟨fun j => if j=i then 1 else 0,0⟩
def Affine.sub {n : ℕ} (f g : Affine n) : Affine n :=
  ⟨fun i => f.coeff i-g.coeff i,f.constant-g.constant⟩
def Affine.scale {n : ℕ} (q : ℚ) (f : Affine n) : Affine n :=
  ⟨fun i => q*f.coeff i,q*f.constant⟩

@[simp] theorem Affine.eval_const {n : ℕ} (q : ℚ) (x : Fin n → ℝ) :
    (Affine.const q).eval x = q := by simp [Affine.eval, Affine.const]
@[simp] theorem Affine.eval_variable {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (Affine.variable i).eval x = x i := by
  simp only [Affine.eval, Affine.variable, Rat.cast_zero, zero_add]
  calc
    (∑ j, (↑(if j=i then (1 : ℚ) else 0) : ℝ)*x j) =
        ∑ j, if j=i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp_all
    _ = x i := by simp
@[simp] theorem Affine.eval_sub {n : ℕ} (f g : Affine n) (x : Fin n → ℝ) :
    (f.sub g).eval x = f.eval x-g.eval x := by
  simp only [Affine.eval, Affine.sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring
@[simp] theorem Affine.eval_scale {n : ℕ} (q : ℚ) (f : Affine n) (x : Fin n → ℝ) :
    (f.scale q).eval x = (q : ℝ)*f.eval x := by
  simp only [Affine.eval, Affine.scale, Rat.cast_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def affineRow {n : ℕ} (s : Bool) (f g : Affine n) : Row n :=
  ⟨fun i => f.coeff i-g.coeff i,g.constant-f.constant,s⟩

@[simp] theorem affineRow_holds {n : ℕ} (s : Bool) (f g : Affine n) (x : Fin n → ℝ) :
    (affineRow s f g).Holds x ↔ StrictAffineElimination.Rel s (f.eval x) (g.eval x) := by
  simp only [Row.Holds, Row.eval, affineRow, Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib, Affine.eval]
  cases s <;> simp only [StrictAffineElimination.Rel, Bool.false_eq_true, if_false, if_true]
  all_goals constructor <;> intro h <;> linarith

def comparisonRows {n : ℕ} (cmp : AgeComparison) (f g : Affine n) : Finset (Row n) :=
  match cmp with
  | .strict => {affineRow true f g}
  | .weak => {affineRow false f g}
  | .equal => {affineRow false f g,affineRow false g f}

@[simp] theorem comparisonRows_holds {n : ℕ} (cmp : AgeComparison)
    (f g : Affine n) (x : Fin n → ℝ) :
    (∀ r ∈ comparisonRows cmp f g, r.Holds x) ↔ cmp.holds (f.eval x) (g.eval x) := by
  cases cmp <;> simp [comparisonRows, AgeComparison.holds, StrictAffineElimination.Rel]
  exact le_antisymm_iff.symm

def scaledRows {n : ℕ} (c : RationalInterval) (d u : Affine n) : Finset (Row n) :=
  (match c.lower with | none => ∅ | some b => {affineRow b.strict (u.scale b.value) d}) ∪
  (match c.upper with | none => ∅ | some b => {affineRow b.strict d (u.scale b.value)})

@[simp] theorem scaledRows_holds {n : ℕ} (c : RationalInterval) (d u : Affine n)
    (x : Fin n → ℝ) :
    (∀ r ∈ scaledRows c d u, r.Holds x) ↔ c.scaled (d.eval x) (u.eval x) := by
  rcases c with ⟨lo,hi⟩
  cases lo <;> cases hi <;> simp [scaledRows, RationalInterval.scaled, StrictAffineElimination.Rel]

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]

abbrev BankVar (N : RootedBinary V E X) := V ⊕ (Option E ⊕ Hybrid N)
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)

instance hybridPredicateDecidable : DecidablePred (N.graph.IsHybrid) := by
  intro v
  unfold Nanuq.Source.EdgeGraph.IsHybrid
  infer_instance

def agesOf (x : Fin n → ℝ) (v : V) : ℝ := x (layout (Sum.inl v))
def inverseRatesOf (x : Fin n → ℝ) (e : Option E) : ℝ := x (layout (Sum.inr (Sum.inl e)))
def coinsOf (x : Fin n → ℝ) (h : Hybrid N) : ℝ := x (layout (Sum.inr (Sum.inr h)))

def bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) (i : Fin n) : ℝ :=
  match layout.symm i with
  | .inl v => a v
  | .inr (.inl e) => u e
  | .inr (.inr h) => g h

@[simp] theorem agesOf_bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) :
    agesOf N layout (bankVector N layout a u g) = a := by
  funext v
  simp [agesOf, bankVector]
@[simp] theorem inverseRatesOf_bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) :
    inverseRatesOf N layout (bankVector N layout a u g) = u := by
  funext e
  simp [inverseRatesOf, bankVector]
@[simp] theorem coinsOf_bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) :
    coinsOf N layout (bankVector N layout a u g) = g := by
  funext h
  simp [coinsOf, bankVector]

def ageForm (atom : AgeAtom V) : Affine n :=
  match atom with
  | .node v => .variable (layout (.inl v))
  | .fixed q => .const q

def inverseForm (e : Option E) : Affine n := .variable (layout (.inr (.inl e)))
def coinForm (h : Hybrid N) : Affine n := .variable (layout (.inr (.inr h)))
def durationForm (e : Exposure V E) : Affine n :=
  (ageForm N layout e.older).sub (ageForm N layout e.younger)

@[simp] theorem ageForm_eval (atom : AgeAtom V) (x : Fin n → ℝ) :
    (ageForm N layout atom).eval x = atom.eval (agesOf N layout x) := by
  cases atom <;> simp [ageForm, AgeAtom.eval, agesOf]
@[simp] theorem inverseForm_eval (e : Option E) (x : Fin n → ℝ) :
    (inverseForm N layout e).eval x = inverseRatesOf N layout x e := by
  simp [inverseForm, inverseRatesOf]
@[simp] theorem coinForm_eval (h : Hybrid N) (x : Fin n → ℝ) :
    (coinForm N layout h).eval x = coinsOf N layout x h := by
  simp [coinForm, coinsOf]
@[simp] theorem durationForm_eval (e : Exposure V E) (x : Fin n → ℝ) :
    (durationForm N layout e).eval x = e.duration (agesOf N layout x) := by
  simp [durationForm, Exposure.duration]

def chronologyRows (c : AgeConstraint V) : Finset (Row n) :=
  comparisonRows c.comparison (ageForm N layout c.left) (ageForm N layout c.right)

@[simp] theorem chronologyRows_holds (c : AgeConstraint V) (x : Fin n → ℝ) :
    (∀ r ∈ chronologyRows N layout c, r.Holds x) ↔ c.holds (agesOf N layout x) := by
  simp [chronologyRows, AgeConstraint.holds]

lemma scaled_one_iff (c : RationalInterval) (g : ℝ) : c.scaled g 1 ↔ c.contains g := by
  simp [RationalInterval.scaled, RationalInterval.contains]

/-- Finite syntactic compilation. The layout is an explicit bijection of the
original variable registry, never a rowwise parameter duplication. -/
def compileCell (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Finset (Row n) :=
  (Finset.univ.biUnion fun e : E =>
    comparisonRows .strict (ageForm N layout (.node (N.graph.target e)))
      (ageForm N layout (.node (N.graph.source e)))) ∪
  (Finset.univ.biUnion fun v : X =>
    comparisonRows .equal (ageForm N layout (.node (N.leaf v))) (.const 0)) ∪
  (Finset.univ.biUnion fun e : Option E =>
    comparisonRows .strict (.const 0) (inverseForm N layout e)) ∪
  (Finset.univ.biUnion fun h : Hybrid N =>
    comparisonRows .strict (.const 0) (coinForm N layout h)) ∪
  (Finset.univ.biUnion fun h : Hybrid N =>
    comparisonRows .strict (coinForm N layout h) (.const 1)) ∪
  (Finset.univ.biUnion fun j : C => chronologyRows N layout (chronology j)) ∪
  (Finset.univ.biUnion fun i : I =>
    scaledRows (rows i).cell (durationForm N layout (rows i))
      (inverseForm N layout (rows i).population)) ∪
  (Finset.univ.biUnion fun h : Hybrid N =>
    scaledRows (coins h) (coinForm N layout h) (.const 1))

def BankConditions (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval)
    (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) : Prop :=
    (∀ e, a (N.graph.target e) < a (N.graph.source e)) ∧
    (∀ x, a (N.leaf x) = 0) ∧
    (∀ e, 0 < u e) ∧
    (∀ h, 0 < g h) ∧ (∀ h, g h < 1) ∧
    (∀ j, (chronology j).holds a) ∧
    (∀ h, (coins h).contains (g h)) ∧
    (∀ i, (rows i).cell.scaled ((rows i).duration a) (u (rows i).population))

@[simp] theorem forall_univ_biUnion {A B : Type*} [Fintype A]
    [DecidableEq B] (f : A → Finset B) (P : B → Prop) :
    (∀ r ∈ Finset.univ.biUnion f, P r) ↔ ∀ i, ∀ r ∈ f i, P r := by
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index]
  exact forall_comm

/-- Every compiled row is equivalent to its source constraint, jointly on one
bank. This is a theorem about the actual emitted finite matrix, not a provider
field asserting source-completeness. -/
theorem compileCell_correct (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (x : Fin n → ℝ) :
    (∀ r ∈ compileCell N layout chronology rows coins, r.Holds x) ↔
    BankConditions N chronology rows coins (agesOf N layout x)
      (inverseRatesOf N layout x) (coinsOf N layout x) := by
  simp only [compileCell, Finset.forall_mem_union, forall_univ_biUnion,
    comparisonRows_holds, chronologyRows_holds, scaledRows_holds,
    Affine.eval_const, ageForm_eval, inverseForm_eval, coinForm_eval,
    durationForm_eval, AgeAtom.eval, AgeComparison.holds,
    Rat.cast_zero, Rat.cast_one, scaled_one_iff, BankConditions]
  tauto

/-- Existence of an original inverse bank is exactly finite matrix feasibility.
The proof explicitly encodes and decodes the one shared bank through layout. -/
theorem inverse_cell_iff_compiled (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    inverseCellFeasible N chronology rows coins ↔
      Feasible ℝ (compileCell N layout chronology rows coins) := by
  constructor
  · rintro ⟨a,u,g,h⟩
    refine ⟨bankVector N layout a u g, (compileCell_correct N layout chronology rows coins _).mpr ?_⟩
    simpa only [agesOf_bankVector, inverseRatesOf_bankVector, coinsOf_bankVector,
      BankConditions] using h
  · rintro ⟨x,hx⟩
    refine ⟨agesOf N layout x, inverseRatesOf N layout x, coinsOf N layout x, ?_⟩
    exact (compileCell_correct N layout chronology rows coins x).mp hx

/-- An actual total executable finite-chart decision, entirely rational. -/
def decideOriginalCell (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) : Bool :=
  decideFeasible n (compileCell N layout chronology rows coins)

/-- Source-rooted completeness and soundness. Arbitrary real calendars/rates
and inheritance are recognized through the exact compiled finite matrix. -/
theorem decideOriginalCell_correct (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    decideOriginalCell N layout chronology rows coins = true ↔
      originalCellFeasible N chronology rows coins := by
  rw [decideOriginalCell, decideFeasible_correct (K := ℝ)]
  exact (inverse_cell_iff_compiled N layout chronology rows coins).symm.trans
    (original_cell_iff_inverse N chronology rows coins).symm

#print axioms compileCell_correct
#print axioms inverse_cell_iff_compiled
#print axioms decideOriginalCell_correct
end UnifiedLean.G6.NaturalCellAffineCompiler
