import G1DecoratedRootBlobRetention

/-! Canonical original multi-span temporal list admission. Contributor: dot,
2026-10-03. Physical original node dates split the SAME full calendar batches. -/
namespace G1OriginalSpanCalendarDecomposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open G1OriginalDecoratedSpan G1CanonicalThreeEpochList G1OriginalCalendarDecomposition
open G1CanonicalComponentSegment G1CanonicalEpochSpecialization G1NonrootBigonKernel
open G1InitializedFrontierPrefix
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

/-- Parent-order admission is original syntax, not a kernel equality. -/
def RegistrySpan (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    {a b : V} : OriginalSpan N a b → Prop
  | .edge _ _ => True
  | .bigon B => B.parents = H.parents ⟨B.parents.hybrid,B.parents.isHybrid⟩
  | .append first last => RegistrySpan N H first ∧ RegistrySpan N H last

lemma actual_span_dates_strict (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (word : OriginalSpan N a b) : C.age a < C.age b := by
  induction word with
  | edge e _ => exact C.edge_older e
  | bigon B =>
      have h := C.edge_older B.parents.parent0
      rw [B.parents.target0,show N.graph.source B.parents.parent0 = B.upper from B.arm_sources false] at h
      exact h
  | append _ _ hfirst hlast => exact hfirst.trans hlast

noncomputable def fullSpanAgenda (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : V → unitInterval) (common : V → Bool)
    (a b : V) : List (ProgramStep N) :=
  canonicalEpochBlock N C H (fun h => gamma h.val) (fun h => common h.val) a b
    (originalExits N C (C.age b))

/-- Literal whole original calendar phase concatenates at an internal node:
all its exits end the first phase, all its nodes begin the second phase. -/
theorem actual_full_span_agenda_append (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : V → unitInterval) (common : V → Bool)
    (a b c : V) (hab : C.age a < C.age b) (hbc : C.age b < C.age c) :
    fullSpanAgenda N C H gamma common a c = fullSpanAgenda N C H gamma common a b ++
      fullSpanAgenda N C H gamma common b c := by
  have h := actual_stop_tail_middle_cut N C H (fun h => gamma h.val) (fun h => common h.val)
    (afterDate N C (C.age a)) (original_after_ordered N C _) (C.age b) (C.age c)
    (original_after_member N C _ b hab) hbc (C.age a)
  have hf : (afterDate N C (C.age a)).filter (fun t => decide (C.age b < t)) =
      afterDate N C (C.age b) := filter_after_filter hab _
  rw [hf] at h
  unfold fullSpanAgenda canonicalEpochBlock
  rw [h]
  have hb : boundaryOperations N C H (fun h => gamma h.val) (fun h => common h.val) (C.age b) =
      (originalExits N C (C.age b)).map (fun e => .boundary (.exit e)) ++
      nodeOperations N C H (fun h => gamma h.val) (fun h => common h.val) (C.age b) := rfl
  rw [hb]
  simp only [List.append_assoc]

end G1OriginalSpanCalendarDecomposition
