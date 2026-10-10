import G2AssembledBoundaryNull
import G2UniversalTransitionCriterion
import G2ActualSourceTransitionCriterion
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
Lossless, streamed declaration/type/body DAG audit. Pointer identity preserves
actual sharing without merging alpha-equivalent or metadata-distinct terms.
Unsafe pointer operations are confined to this diagnostic serializer; they are
not declarations of the imported mathematical target, and prove no proposition.
-/
open Lean Elab Command
set_option debug.skipKernelTC false
set_option stderrAsMessages false
namespace CompleteDAGAudit

def progress (label : String) : CommandElabM Unit := liftIO do
  let stream ← IO.getStderr
  stream.putStrLn ("G2-DAG-CHECKPOINT " ++ label)
  stream.flush

run_cmd progress "imports-loaded-before-serializer-definitions"

def arr (xs : List Json) : Json := Json.arr xs.toArray
def nameJson : Name → Json
  | .anonymous => arr [toJson "anonymous"]
  | .str p s => arr [toJson "str", nameJson p, toJson s]
  | .num p n => arr [toJson "num", nameJson p, toJson n]

def levelJson : Level → Json
  | .zero => arr [toJson "zero"]
  | .succ u => arr [toJson "succ", levelJson u]
  | .max u v => arr [toJson "max", levelJson u, levelJson v]
  | .imax u v => arr [toJson "imax", levelJson u, levelJson v]
  | .param n => arr [toJson "param", nameJson n]
  | .mvar n => arr [toJson "mvar", nameJson n.name]

def substringJson (s : Substring.Raw) : Json :=
  arr [toJson s.str, toJson s.startPos.byteIdx, toJson s.stopPos.byteIdx]

def sourceInfoJson : SourceInfo → Json
  | .none => arr [toJson "none"]
  | .synthetic p e c => arr [toJson "synthetic", toJson p.byteIdx, toJson e.byteIdx, toJson c]
  | .original l p t e => arr [toJson "original", substringJson l, toJson p.byteIdx,
      substringJson t, toJson e.byteIdx]

def preresolvedJson : Syntax.Preresolved → Json
  | .namespace n => arr [toJson "namespace", nameJson n]
  | .decl n fs => arr [toJson "decl", nameJson n, toJson fs]

partial def syntaxJson : Syntax → Json
  | .missing => arr [toJson "missing"]
  | .node i k args => arr [toJson "node", sourceInfoJson i, nameJson k,
      Json.arr (args.map syntaxJson)]
  | .atom i v => arr [toJson "atom", sourceInfoJson i, toJson v]
  | .ident i raw n pre => arr [toJson "ident", sourceInfoJson i, substringJson raw,
      nameJson n, Json.arr (pre.toArray.map preresolvedJson)]

def dataValueJson : DataValue → Json
  | .ofString v => arr [toJson "string", toJson v]
  | .ofBool v => arr [toJson "bool", toJson v]
  | .ofName v => arr [toJson "name", nameJson v]
  | .ofNat v => arr [toJson "nat", toJson v]
  | .ofInt v => arr [toJson "int", toJson v]
  | .ofSyntax v => arr [toJson "syntax", syntaxJson v]

def metadataJson (m : MData) : Json := Json.arr <| m.entries.toArray.map fun (n,v) =>
  arr [nameJson n, dataValueJson v]

def binderJson : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"

unsafe structure ExprPool where
  ids : PtrMap Expr Nat := mkPtrMap
  nodes : Array Json := #[]

unsafe def internExpr (e : Expr) : StateM ExprPool Nat := do
  if let some id := (← get).ids.find? e then return id
  let node ← match e with
    | .bvar i => pure <| arr [toJson "bvar", toJson i]
    | .fvar i => pure <| arr [toJson "fvar", nameJson i.name]
    | .mvar i => pure <| arr [toJson "mvar", nameJson i.name]
    | .sort u => pure <| arr [toJson "sort", levelJson u]
    | .const n us => pure <| arr [toJson "const", nameJson n, Json.arr (us.toArray.map levelJson)]
    | .app f a => do
      let fi ← internExpr f; let ai ← internExpr a
      pure <| arr [toJson "app", toJson fi, toJson ai]
    | .lam n t b bi => do
      let ti ← internExpr t; let bi' ← internExpr b
      pure <| arr [toJson "lam", nameJson n, toJson ti, toJson bi', binderJson bi]
    | .forallE n t b bi => do
      let ti ← internExpr t; let bi' ← internExpr b
      pure <| arr [toJson "forallE", nameJson n, toJson ti, toJson bi', binderJson bi]
    | .letE n t v b nd => do
      let ti ← internExpr t; let vi ← internExpr v; let bi ← internExpr b
      pure <| arr [toJson "letE", nameJson n, toJson ti, toJson vi, toJson bi, toJson nd]
    | .lit (.natVal n) => pure <| arr [toJson "natVal", toJson n]
    | .lit (.strVal s) => pure <| arr [toJson "strVal", toJson s]
    | .mdata m b => do
      let bi ← internExpr b
      pure <| arr [toJson "mdata", metadataJson m, toJson bi]
    | .proj n i b => do
      let bi ← internExpr b
      pure <| arr [toJson "proj", nameJson n, toJson i, toJson bi]
  let st ← get
  let id := st.nodes.size
  set ({ids := st.ids.insert e id, nodes := st.nodes.push node} : ExprPool)
  return id

def allowedG2PartialNames : Array String := #["_private.G2ActualTimedAllPanelLaw.0.GProgram.G2.ActualTimedAllPanelLaw.instEncodableGenealogy_g2ActualTimedAllPanelLaw.encodable_toS.«_@».G2ActualTimedAllPanelLaw.31462420._hygCtx._hyg.8._unsafe_rec", "_private.G2ActualTimedAllPanelLaw.0.GProgram.G2.ActualTimedAllPanelLaw.instEncodableGenealogy_g2ActualTimedAllPanelLaw.encodable_fromS.«_@».G2ActualTimedAllPanelLaw.31462420._hygCtx._hyg.9._unsafe_rec"]
def contextPartialNames : Array String := #["GProgram.SourceForest.Genealogy.prune._unsafe_rec", "UnifiedLean.Source.FiniteGenealogyEncoding.TreeCode._unsafe_rec", "UnifiedLean.Source.FiniteGenealogyEncoding.decodeTree._unsafe_rec", "UnifiedLean.Source.SourceInitializedCalendar.finalDate._unsafe_rec", "_private.G2ActualTimedAllPanelLaw.0.GProgram.G2.ActualTimedAllPanelLaw.instEncodableGenealogy_g2ActualTimedAllPanelLaw.encodable_toS.«_@».G2ActualTimedAllPanelLaw.31462420._hygCtx._hyg.8._unsafe_rec", "UnifiedLean.Source.FiniteGenealogyEncoding.treeCodeFintype._unsafe_rec", "UnifiedLean.Source.FiniteGenealogyEncoding.genealogyHeight._unsafe_rec", "GProgram.SourceForest.instDecidableEqGenealogy.decEq._unsafe_rec", "GProgram.SourceForest.Genealogy.WellLabelled._unsafe_rec", "GProgram.SourceForest.Genealogy.leaves._unsafe_rec", "UnifiedLean.Source.FiniteGenealogyEncoding.encodeTree._unsafe_rec", "_private.G2ActualTimedAllPanelLaw.0.GProgram.G2.ActualTimedAllPanelLaw.instEncodableGenealogy_g2ActualTimedAllPanelLaw.encodable_fromS.«_@».G2ActualTimedAllPanelLaw.31462420._hygCtx._hyg.9._unsafe_rec", "G4TwoRootSourceStopping.tailSurvival._unsafe_rec", "UnifiedLean.Source.SourceCopyCarrierTransport.mapLabels._unsafe_rec"]

unsafe def auditOwned (target : Name) (own : List (Name × ConstantInfo)) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  if own.isEmpty then throwError "No target declarations"
  liftIO <| IO.println <| (Json.mkObj [("record",toJson "header"),
    ("schema",toJson "complete-module-dag-v1"),("module",nameJson target),("module_display",toJson target.toString),
    ("declaration_count",toJson own.length)]).compress
  liftIO do (← IO.getStdout).flush
  for (name,ci) in own do
    progress ("declaration-start " ++ toString name)
    let value := ci.value? true
    let requiresBody := match ci with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
      | _ => false
    if requiresBody && value.isNone then throwError "Missing body in {name}"
    let typeRefs := ci.type.getUsedConstants.qsort Name.quickLt
    let bodyRefs := (value.map Expr.getUsedConstants |>.getD #[]).qsort Name.quickLt
    let axioms := (← collectAxioms name).qsort Name.quickLt
    if (typeRefs ++ bodyRefs).any (fun n => (env.find? n).isNone) then
      throwError "Unresolved references in {name}"
    if ci.isUnsafe then throwError "Unsafe target {name}"
    if ci.isPartial then
      if !allowedG2PartialNames.contains name.toString then
        throwError "Unclassified partial target {name}"
      let .str base "_unsafe_rec" := name
        | throwError "Partial target is not a generated recursion companion: {name}"
      let some safe := env.find? base
        | throwError "Missing safe base for {name}"
      if safe.isUnsafe || safe.isPartial || !(safe.type == ci.type) then
        throwError "Invalid safe-base correspondence for {name}"
    if (typeRefs ++ bodyRefs).any (fun n => contextPartialNames.contains n.toString && n != name) then
      throwError "Non-self logical reference to generated partial companion in {name}"
    if ci.type.hasFVar || ci.type.hasMVar || value.any (fun e => e.hasFVar || e.hasMVar) then
      throwError "Nonclosed target {name}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      throwError "Unapproved axioms in {name}"
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    let build : StateM ExprPool (Nat × Option Nat) := do
      let ti ← internExpr ci.type
      let bi ← match value with | none => pure none | some b => some <$> internExpr b
      pure (ti,bi)
    let ((ti,bi),pool) := build.run {}
    progress ("before-DAG-emission " ++ toString name ++ " nodes=" ++ toString pool.nodes.size)
    liftIO <| IO.println <| (Json.mkObj [
      ("record",toJson "declaration"),("name",nameJson name),("name_display",toJson name.toString),("kind",toJson kind),
      ("level_parameters",Json.arr (ci.levelParams.toArray.map nameJson)),
      ("type_root",toJson ti),("body_root",bi.map toJson |>.getD Json.null),
      ("nodes",Json.arr pool.nodes),
      ("type_references",Json.arr (typeRefs.map nameJson)),
      ("type_references_display",toJson (typeRefs.map Name.toString)),
      ("body_references",Json.arr (bodyRefs.map nameJson)),
      ("body_references_display",toJson (bodyRefs.map Name.toString)),
      ("axioms",Json.arr (axioms.map nameJson)),
      ("axioms_display",toJson (axioms.map Name.toString)),
      ("unsafe",toJson ci.isUnsafe),("partial",toJson ci.isPartial)]).compress
  liftIO <| IO.println <| (Json.mkObj [("record",toJson "footer"),
    ("status",toJson "COMPLETE"),("declaration_count",toJson own.length)]).compress


unsafe def auditTargets (targets : Array Name) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let moduleNames := env.header.moduleNames
  let indices := moduleNames.map (fun n => targets.contains n)
  let mut grouped : Array (List (Name × ConstantInfo)) := Array.replicate moduleNames.size []
  progress "before-single-constants-acquisition"
  let constants := env.constants
  progress "before-single-ownership-traversal"
  for (name, ci) in constants do
    if let some idx := env.getModuleIdxFor? name then
      if indices[idx.toNat]! then
        grouped := grouped.modify idx.toNat (fun xs => (name, ci) :: xs)
  progress "single-ownership-traversal-complete"
  for target in targets do
    let some idx := moduleNames.findIdx? (fun n => n == target)
      | throwError "Target module is not imported: {target}"
    let own := grouped[idx]!.mergeSort (fun a b => Name.quickLt a.1 b.1)
    progress ("owned-list-complete " ++ toString target ++ " count=" ++ toString own.length)
    auditOwned target own

end CompleteDAGAudit
run_cmd do
  CompleteDAGAudit.progress "serializer-elaboration-complete-before-all68-grouped-audit"
  CompleteDAGAudit.auditTargets #[`G2LiveLineageRouting, `G2FaithfulPairAgeDecoration, `G2SourceGraftDecoration, `G2LiteralMarkedClockTrace, `G2ActualDecorationFold, `G2DecorationMeasurability, `G2MarkedTraceRenewal, `G2LiteralEpochLaw, `G2ActualCalendarTrace, `G2FiniteAncestralTrace, `G2AncestralTraceSourceLaw, `G2CompleteCalendarAttachment, `G2LiteralCutResidual, `G2MarkedTraceCuts, `G2MarkedTraceBudgetStability, `G2SameClockContinuation, `G2HistoryResidualAttachment, `G2CutFutureSourceBinding, `G2SameClockPastFutureLaw, `G2EpochHistoryReadout, `G2CompleteAncestralPath, `G2ChronologicalPathReadout, `G2CalendarDecoration, `G2CompleteDecoration, `G2PairBirthFold, `G2ClockBoundaryNull, `G2WholeMatrixAges, `G2ChronologicalDecoration, `G2StrictClockDecoration, `G2OriginalProgramSafety, `G2TimedBoundMeasurability, `G2CutResidualSourceMixture, `G2SourceFiniteHistory, `G2ActualEpochHistoryLaw, `G2EpochPathProjection, `G2ActualSegmentPathLaw, `G2FiniteFibreTransport, `G2CalendarHistoryBinding, `G2CalendarPathProjection, `G2CompletedCalendarPathLaw, `G2ChronologicalGluing, `G2ActualChronologicalPathLaw, `G2EventualPathReadout, `G2ActualPairCoalescence, `G2CalendarPairSupport, `G2RationalAgeReadout, `G2PairBirthThreshold, `G2AncestralPairSupport, `G2AncestralAgeCertificate, `G2ChronologicalTraceCompatibility, `G2CalendarFirstAge, `G2ControlledTraceAssembly, `G2RegisteredPathProjection, `G2OriginalAbsoluteAges, `G2JointTimedObservation, `G2CompleteTimedSupport, `G2TimedDecorationPruning, `G2ChronologicalPruning, `G2SourcePairMatrixReadout, `G2CompleteTerminalReadout, `G2FaithfulTimedOutput, `G2LiteralTimedObservationPruning, `G2ActualTimedAllPanelLaw, `G2TimedOutputForgetting, `G2RootedTimedOutputSupport, `G2AssembledBoundaryNull, `G2UniversalTransitionCriterion, `G2ActualSourceTransitionCriterion]
