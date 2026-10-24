import G6TwoTipChartFixture
import G7EffectiveCoefficientSupport
import Lean.Data.Json

/-!
# Native literal original-source population coefficients

Contributor: Codex / lean_reuse_successor, 10 October 2026.
Every fixture starts in the actual inherited encodeActual image of a proved
source-valid state of the admitted two-tip source. The original coefficients,
Choice and merger are used unchanged. Local labels, original populations and
all original register bits are retained in literal rows. The test serializer
then sums entire literal destination fibres under an explicit global-label
unordered forest quotient. This is a finite executable fixture, not a general
Code-to-native LAW quotient or universal Rust refinement theorem.
-/
namespace UnifiedLean.G7.OriginalPopulationFixture

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients

abbrev N := UnifiedLean.G6.TwoTipChartFixture.source

def sample (n : Nat) (i : Option (Fin 2)) (x : Fin n) : Fin 2 :=
  match i with
  | none => if x.val % 2 = 0 then 0 else 1
  | some e => e

def initialState (n : Nat) (i : Option (Fin 2)) (register : Fin 3 → Bool) :
    State (Fin 3) (Fin 2) (Fin n) where
  live := Finset.univ
  ancestor := fun x => x
  genealogy := Genealogy.leaf
  location := fun _ => place N i
  register := register
  history := []

theorem initialState_valid (n : Nat) (i : Option (Fin 2)) (register : Fin 3 → Bool) :
    Valid (initialState n i register) := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l _; rfl
  · intro l _ x; simp [initialState, Genealogy.leaves]
  · intro l _; trivial

theorem initialState_sourceValid (n : Nat) (i : Option (Fin 2))
    (register : Fin 3 → Bool) : SourceValid N (sample n i) (initialState n i register) := by
  refine ⟨initialState_valid n i register, ?_⟩
  intro x
  cases i with
  | none =>
      change N.root = N.root ∧ N.graph.DReach N.root (N.leaf (sample n none x))
      exact ⟨rfl, N.rooted _⟩
  | some e =>
      change N.graph.DReach (N.graph.target e) (N.leaf e)
      exact .refl

def initialCode (n : Nat) (i : Option (Fin 2)) (register : Fin 3 → Bool) :
    Code N (sample n i) :=
  encodeActual N (sample n i) (initialState n i register)
    (initialState_sourceValid n i register)

theorem initialCode_coLocated (n : Nat) (i : Option (Fin 2))
    (register : Fin 3 → Bool) : CoLocated N (initialCode n i register) i := by
  intro x
  change copyLocation (decodeSnapshot N.root
    (encodeSnapshot (initialState n i register) (initialState_valid n i register))) x = _
  rw [decode_encode_copyLocation]
  cases i <;> rfl

/-- A valid entering forest with a carried subtree and nonminimum live owner.
It is an entering-state fixture; no reachability from singleton tips is claimed. -/
def carriedState : State (Fin 3) (Fin 2) (Fin 4) where
  live := {2, 3}
  ancestor x := if x = 3 then 3 else 2
  genealogy x := if x = 2 then .graft (.graft (.leaf 0) (.leaf 1)) (.leaf 2) else .leaf x
  location := fun _ => .rootPopulation N.root
  register := fun _ => false
  history := []

theorem carriedState_valid : Valid carriedState := by
  letI := forestValidDecidable carriedState
  exact of_decide_eq_true (by decide)

theorem carriedState_sourceValid : SourceValid N (sample 4 none) carriedState := by
  refine ⟨carriedState_valid, ?_⟩
  intro x
  change N.root = N.root ∧ N.graph.DReach N.root (N.leaf (sample 4 none x))
  exact ⟨rfl, N.rooted _⟩

def carriedCode : Code N (sample 4 none) :=
  encodeActual N (sample 4 none) carriedState carriedState_sourceValid

theorem carriedCode_coLocated : CoLocated N carriedCode none := by
  intro x
  change copyLocation (decodeSnapshot N.root
    (encodeSnapshot carriedState carriedState_valid)) x = _
  rw [decode_encode_copyLocation]
  rfl

def normalizedTerms (p : Expr) : List (Nat × Rat) :=
  let powers := (p.map Prod.fst).eraseDups.mergeSort (fun a b => decide (a ≤ b))
  (powers.map fun m => (m, p.foldl (fun a z => if z.1 = m then a + z.2 else a) 0))
    |>.filter (fun z => z.2 != 0)

def rationalText (q : Rat) : String := toString q.num ++ "/" ++ toString q.den

def termsJson (p : Expr) : Lean.Json :=
  Lean.Json.arr (p.map (fun z =>
    Lean.Json.arr #[Lean.toJson z.1, Lean.Json.str (rationalText z.2)])).toArray

def treeJson {n : Nat} : Genealogy (Fin n) → Lean.Json
  | .leaf x => Lean.toJson x.val
  | .graft a b => Lean.Json.arr #[treeJson a, treeJson b]

def locationJson (p : Location (Fin 3) (Fin 2)) : Lean.Json :=
  match p with
  | .node v => Lean.Json.arr #[Lean.Json.str "N", Lean.toJson v.val]
  | .edge e => Lean.Json.arr #[Lean.Json.str "E", Lean.toJson e.val]
  | .rootPopulation v => Lean.Json.arr #[Lean.Json.str "A", Lean.toJson v.val]

def snapshotFields {n : Nat} {i : Option (Fin 2)}
    (s : Code N (sample n i)) : List (String × Lean.Json) :=
  let ids := FinEnum.toList (Fin n)
  [ ("live", Lean.toJson ((ids.filter fun x => decide (x ∈ s.val.live)).map Fin.val)),
    ("ancestor", Lean.toJson (ids.map fun x => (s.val.ancestor x).val)),
    ("genealogy", Lean.Json.arr ((ids.map fun x =>
      match s.val.genealogy x with | none => Lean.Json.null | some g => treeJson g.val).toArray)),
    ("location", Lean.Json.arr ((ids.map fun x =>
      match s.val.population x with | none => Lean.Json.null | some p => locationJson p).toArray)),
    ("register", Lean.toJson ((FinEnum.toList (Fin 3)).map s.val.register)) ]

def treeMin : Genealogy Nat → Nat
  | .leaf x => x
  | .graft a b => min (treeMin a) (treeMin b)

/-- Explicit finite fixture quotient, including the supplied label embedding. -/
def canonicalTree {n : Nat} (labels : Fin n → Nat) :
    Genealogy (Fin n) → Genealogy Nat
  | .leaf x => .leaf (labels x)
  | .graft a b =>
      let ca := canonicalTree labels a
      let cb := canonicalTree labels b
      if treeMin ca ≤ treeMin cb then .graft ca cb else .graft cb ca

def canonicalForest {n : Nat} {i : Option (Fin 2)} (labels : Fin n → Nat)
    (s : Code N (sample n i)) : List (Genealogy Nat) :=
  (((FinEnum.toList (Fin n)).filter fun x => decide (x ∈ s.val.live)).map
    (fun x => canonicalTree labels ((sourceState s).genealogy x))).mergeSort
      (fun a b => decide (treeMin a ≤ treeMin b))

def globalTreeJson : Genealogy Nat → Lean.Json
  | .leaf x => Lean.toJson x
  | .graft a b => Lean.Json.arr #[globalTreeJson a, globalTreeJson b]

def coefficientTable {n : Nat} {i : Option (Fin 2)} (s : Code N (sample n i)) :
    List (Code N (sample n i) × Expr) :=
  ((GProgram.G7.EffectiveCoefficientSupport.destinations N n s).eraseDups.map fun d =>
    (d, normalizedTerms (coefficients N n s d))).filter (fun row => !row.2.isEmpty)

/-- Aggregate every literal destination row in a quotient fibre, not one row
times an orientation factor. -/
def quotientRows {n : Nat} {i : Option (Fin 2)} (labels : Fin n → Nat)
    (table : List (Code N (sample n i) × Expr)) : Lean.Json :=
  let forests := (table.map fun row => canonicalForest labels row.1).eraseDups
  Lean.Json.arr (forests.map fun forest =>
    let terms := normalizedTerms (table.flatMap fun row =>
      if canonicalForest labels row.1 = forest then row.2 else [])
    Lean.Json.mkObj [
      ("forest", Lean.Json.arr (forest.map globalTreeJson).toArray),
      ("coefficients", termsJson terms)]).toArray

def fixtureJson (name : String) {n : Nat} (i : Option (Fin 2))
    (labels : Fin n → Nat) (s : Code N (sample n i)) : Lean.Json :=
  let table := coefficientTable s
  let context := Lean.Json.mkObj [
    ("vertices", Lean.toJson (3 : Nat)), ("root", Lean.toJson (0 : Nat)),
    ("edges", Lean.toJson ([(0,1),(0,2)] : List (Nat × Nat))),
    ("leaves", Lean.toJson ([1,2] : List Nat)), ("hybrids", Lean.toJson ([] : List Nat)),
    ("global_labels", Lean.toJson ((FinEnum.toList (Fin n)).map labels)),
    ("local_samples", Lean.toJson ((FinEnum.toList (Fin n)).map fun x => (sample n i x).val)),
    ("population", locationJson (place N i)),
    ("register", Lean.toJson ((FinEnum.toList (Fin 3)).map s.val.register)),
    ("start", Lean.Json.mkObj (snapshotFields s))]
  Lean.Json.mkObj [
    ("schema", Lean.Json.str "source_population_probe_v1"), ("fixture", Lean.Json.str name),
    ("context", context),
    ("rows", Lean.Json.arr (table.map fun row =>
      Lean.Json.mkObj (snapshotFields row.1 ++ [("coefficients", termsJson row.2)])).toArray),
    ("unordered", quotientRows labels table)]

def initialFixture (name : String) (n : Nat) (i : Option (Fin 2))
    (labels : Fin n → Nat) (register : Fin 3 → Bool) : Lean.Json :=
  fixtureJson name i labels (initialCode n i register)

def fixtureNamed (name : String) : Option Lean.Json :=
  match name with
  | "emptyEdge0" => some (initialFixture name 0 (some 0) Fin.val (fun _ => false))
  | "oneAncestral" => some (initialFixture name 1 none Fin.val (fun _ => false))
  | "twoAncestral" => some (initialFixture name 2 none Fin.val (fun _ => false))
  | "threeEdge0" => some (initialFixture name 3 (some 0) Fin.val (fun v => v == 1))
  | "fourAncestral" => some (initialFixture name 4 none Fin.val (fun _ => false))
  | "carriedNonminimum" => some (fixtureJson name none Fin.val carriedCode)
  | "permutedRestrictedEdge0" => some (initialFixture name 3 (some 0)
      (fun x => if x = 0 then 3 else if x = 1 then 0 else 2) (fun _ => false))
  | "frozenRegisterRepeat" => some (initialFixture name 3 (some 0) Fin.val (fun v => v != 1))
  | _ => none

def run (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      match fixtureNamed name with
      | some result => IO.println result.compress; return 0
      | none => IO.eprintln "unknown fixture"; return 2
  | _ => IO.eprintln "expected one fixture name"; return 2

#print axioms initialState_sourceValid
#print axioms initialCode_coLocated
#print axioms carriedState_sourceValid
#print axioms carriedCode_coLocated

end UnifiedLean.G7.OriginalPopulationFixture

def main (args : List String) : IO UInt32 :=
  UnifiedLean.G7.OriginalPopulationFixture.run args
