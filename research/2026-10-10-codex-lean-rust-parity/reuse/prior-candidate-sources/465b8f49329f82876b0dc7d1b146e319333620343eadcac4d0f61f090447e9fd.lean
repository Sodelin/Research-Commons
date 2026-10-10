import G7EffectiveWordCoefficients
import G7OriginalBoundaryFixture
import Lean.Data.Json

/-!
# Nine actual original-word coefficient controls

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses the separately admitted two-tip and original parallel-occurrence source.
The executable word provider has an entire coefficient identity to the inherited
wordPolynomial/naturalWordPolynomial. Conditional inputs are actual encodeActual
images. The unchanged frozen request is reconstructed from those typed inputs;
normalization and JSON are finite controls, not a general native refinement.
No resource-work fields, calendar admission or completion are inferred.
Draft pending sole-scheduler kernel/audit and actual evaluator comparison.
-/
namespace UnifiedLean.G7.OriginalWordFixture
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.G6.OriginalCalendarSchema (Symbol)
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.SymbolicProgramPolynomial

abbrev N2 := OriginalBoundaryFixture.N2
abbrev NP := OriginalBoundaryFixture.NP

def registry2 : OriginalParentRegistry N2 where
  parents h := False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)
  original_site h := False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)

def rootState (n : Nat) : State (Fin 3) (Fin 2) (Fin n) :=
  OriginalEpochFixture.singletonState (fun _ => .rootPopulation N2.root) (fun v => v != 1)

theorem rootState_sourceValid (n : Nat) (sample : Fin n → Fin 2) :
    SourceValid N2 sample (rootState n) := by
  refine ⟨OriginalEpochFixture.singletonState_valid _ _,?_⟩
  intro x
  exact ⟨rfl,N2.rooted (N2.leaf (sample x))⟩

def rootCode (n : Nat) (sample : Fin n → Fin 2) : Code N2 sample :=
  encodeActual N2 sample (rootState n) (rootState_sourceValid n sample)

def coordinateList {v e j : Nat} (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    (hybridIDs : List (Hybrid N)) : List (WordVariable N (Fin j)) :=
  (FinEnum.toList (Fin j)).flatMap (fun slot =>
    ((FinEnum.toList (Fin e)).map some ++ [none]).map (fun i => Sum.inl (slot,i))) ++
    hybridIDs.map Sum.inr

def variableJson {v e j : Nat} (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    (hybridIndex : Hybrid N → Nat) : WordVariable N (Fin j) → Lean.Json
  | .inl (slot,some edge) => Lean.Json.arr
      #[Lean.Json.str "X",Lean.toJson slot.val,Lean.Json.str "E",Lean.toJson edge.val]
  | .inl (slot,none) => Lean.Json.arr
      #[Lean.Json.str "X",Lean.toJson slot.val,Lean.Json.str "A",Lean.toJson N.root.val]
  | .inr hybrid => Lean.Json.arr
      #[Lean.Json.str "ORIGINAL_GAMMA",Lean.toJson (hybridIndex hybrid)]

def normalizedTerms {I : Type*} [DecidableEq I] (coordinates : List I) (p : Sparse I) :
    List (List Nat × Rat) :=
  let expanded := p.map fun z =>
    (coordinates.map (fun i => ((z.1.filter fun a => a.1 == i).map Prod.snd).sum),z.2)
  let monomials := (expanded.map Prod.fst).eraseDups.mergeSort OriginalEpochFixture.lexLe
  (monomials.map fun m =>
    (m,expanded.foldl (fun q z => if z.1 = m then q + z.2 else q) 0))
      |>.filter (fun z => z.2 != 0)

def rowsJson {v e n j : Nat} {N : RootedBinary (Fin v) (Fin e) (Fin 2)}
    {sample : Fin n → Fin 2} (coordinates : List (WordVariable N (Fin j)))
    (rows : Rows (WordVariable N (Fin j)) (Code N sample)) : Lean.Json :=
  let keys := (rows.map fun row => project N Finset.univ row.1).eraseDups
  let output := keys.flatMap fun key =>
    match rows.find? (fun row => project N Finset.univ row.1 == key) with
    | none => []
    | some witness =>
      let terms := normalizedTerms coordinates (readRows (project N Finset.univ) rows key)
      if terms.isEmpty then [] else [Lean.Json.mkObj [
        ("view",OriginalEpochFixture.viewJson key),
        ("witness",OriginalEpochFixture.snapshotJson witness.1),
        ("coefficients",OriginalEpochFixture.termsJson terms)]]
  Lean.Json.arr output.toArray

def contextJson {v e n : Nat} (N : RootedBinary (Fin v) (Fin e) (Fin 2))
    (sample : Fin n → Fin 2) (labels : Fin n → Nat)
    (hybrids : List (Nat × Nat × Nat)) : Lean.Json :=
  Lean.Json.mkObj [
    ("vertices",Lean.toJson v),("root",Lean.toJson N.root.val),
    ("edges",Lean.toJson ((FinEnum.toList (Fin e)).map fun i =>
      ((N.graph.source i).val,(N.graph.target i).val))),
    ("leaves",Lean.toJson ((FinEnum.toList (Fin 2)).map fun x => (N.leaf x).val)),
    ("hybrids",Lean.Json.arr (hybrids.map fun h =>
      Lean.Json.arr #[Lean.toJson h.1,Lean.toJson h.2.1,Lean.toJson h.2.2]).toArray),
    ("global_labels",Lean.toJson ((FinEnum.toList (Fin n)).map labels)),
    ("local_samples",Lean.toJson ((FinEnum.toList (Fin n)).map fun x => (sample x).val))]

def symbolJson {v e j : Nat} : Symbol (Fin j) (Fin v) (Fin e) → Lean.Json
  | .interval i => Lean.Json.arr #[Lean.Json.str "INTERVAL",Lean.toJson i.val]
  | .exit e => Lean.Json.arr #[Lean.Json.str "EXIT",Lean.toJson e.val]
  | .enter v => Lean.Json.arr #[Lean.Json.str "ENTER",Lean.toJson v.val]

def limitsJson : Lean.Json := Lean.Json.mkObj [
  ("initial_assignments",Lean.toJson (16 : Nat)),("initial_terms",Lean.toJson (256 : Nat)),
  ("queries",Lean.toJson (4096 : Nat)),("branches",Lean.toJson (65536 : Nat)),
  ("term_products",Lean.toJson (262144 : Nat)),("destinations",Lean.toJson (4096 : Nat)),
  ("terms",Lean.toJson (65536 : Nat))]

def fixtureJson {v e n j : Nat} (name : String)
    (N : RootedBinary (Fin v) (Fin e) (Fin 2)) (sample : Fin n → Fin 2)
    (labels : Fin n → Nat) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (hybridIDs : List (Hybrid N))
    (hybridIndex : Hybrid N → Nat) (hybrids : List (Nat × Nat × Nat))
    (word : List (Symbol (Fin j) (Fin v) (Fin e))) (initial : Option (Code N sample)) : Lean.Json :=
  let coordinates := coordinateList (j := j) N hybridIDs
  let rows := match initial with
    | none => naturalWordRows N sample H common word
    | some s => wordRows N H common word s
  let initialJson := match initial with
    | none => Lean.Json.mkObj [("kind",Lean.Json.str "NATURAL")]
    | some s => Lean.Json.mkObj [("kind",Lean.Json.str "CONDITIONAL"),
        ("snapshot",OriginalEpochFixture.snapshotJson s)]
  let request := Lean.Json.mkObj [
    ("context",contextJson N sample labels hybrids),("initial",initialJson),
    ("common",Lean.toJson (hybridIDs.map common)),("slots",Lean.toJson j),
    ("word",Lean.Json.arr (word.map symbolJson).toArray),
    ("terminal",Lean.Json.str "FULL_VIEW"),("limits",limitsJson)]
  Lean.Json.mkObj [
    ("schema",Lean.Json.str "source_original_word_coefficients_v1"),
    ("fixture",Lean.Json.str name),("request",request),
    ("variables",Lean.Json.arr (coordinates.map (variableJson N hybridIndex)).toArray),
    ("rows",rowsJson coordinates rows)]

def twoTipFixture {n j : Nat} (name : String) (sample : Fin n → Fin 2)
    (word : List (Symbol (Fin j) (Fin 3) (Fin 2))) (s : Code N2 sample) : Lean.Json :=
  fixtureJson name N2 sample Fin.val registry2 (fun _ => false) []
    (fun h => False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)) [] word (some s)

def parallelFixture {n j : Nat} (name : String) (sample : Fin n → Fin 2)
    (common : Bool) (word : List (Symbol (Fin j) (Fin 5) (Fin 5)))
    (initial : Option (Code NP sample)) : Lean.Json :=
  fixtureJson name NP sample Fin.val OriginalParallelEpochFixture.registry
    (fun _ => common) [OriginalParallelEpochFixture.ids 0]
    (fun h => (OriginalParallelEpochFixture.ids.symm h).val) [(3,2,3)] word initial

def parallelFiniteWord : List (Symbol (Fin 3) (Fin 5) (Fin 5)) :=
  [.enter 1,.enter 4,.interval 0,.exit 4,.enter 3,.interval 1,
   .exit 2,.exit 3,.enter 2,.interval 2,.exit 0,.exit 1,.enter 0]

def parallelFiniteSample (x : Fin 3) : Fin 2 := if x = 0 then 0 else 1

def repeatedSample (x : Fin 3) : Fin 2 := if x = 2 then 1 else 0

def fixtureNamed (name : String) : Option Lean.Json :=
  match name with
  | "emptyConditionalWord" => some (twoTipFixture (j := 0) name
      (fun x : Fin 0 => Fin.elim0 x) [] (rootCode 0 (fun x => Fin.elim0 x)))
  | "emptyNaturalWord" => some (parallelFixture (j := 0) name
      (fun x : Fin 0 => Fin.elim0 x) true [] none)
  | "emptyNaturalCommonWord" => some (parallelFixture (j := 0) name
      (fun x : Fin 0 => Fin.elim0 x) true [.enter 3,.enter 3] none)
  | "conditionalCommonFalseWord" => some (parallelFixture (j := 0) name
      (fun _ : Fin 2 => 1) true [.enter 3,.enter 3]
      (some (OriginalBoundaryFixture.siteCode 2 OriginalBoundaryFixture.falseRegister)))
  | "conditionalCommonTrueWord" => some (parallelFixture (j := 0) name
      (fun _ : Fin 2 => 1) true [.enter 3,.enter 3]
      (some (OriginalBoundaryFixture.siteCode 2 OriginalBoundaryFixture.trueRegister)))
  | "repeatedIntervalSlot" => some (twoTipFixture name repeatedSample
      ([.interval 0,.interval 0] : List (Symbol (Fin 1) (Fin 3) (Fin 2)))
      (rootCode 3 repeatedSample))
  | "carriedOutsideWord" => some (parallelFixture name OriginalBoundaryFixture.carriedSample
      false ([.enter 3,.interval 0,.exit 2,.exit 3,.enter 2] :
        List (Symbol (Fin 1) (Fin 5) (Fin 5))) (some OriginalBoundaryFixture.carriedCode))
  | "parallelCommonFinite" => some (parallelFixture name parallelFiniteSample
      true parallelFiniteWord none)
  | "parallelIndependentFinite" => some (parallelFixture name parallelFiniteSample
      false parallelFiniteWord none)
  | _ => none

def run (args : List String) : IO UInt32 := do
  match args with
  | [name] =>
      match fixtureNamed name with
      | none => IO.eprintln "unknown original word coefficient fixture"; pure 2
      | some output => IO.println output.compress; pure 0
  | _ => IO.eprintln "one fixture name required"; pure 2

#print axioms rootState_sourceValid
#print axioms polynomial_wordRows
#print axioms polynomial_naturalWordRows
end UnifiedLean.G7.OriginalWordFixture
