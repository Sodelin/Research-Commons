import G1OriginatedBridgeBookends

/-! The literal last ORIGINAL cut edge fixes the closing phase, before any
remaining same-date exterior operations. Contributor: dot, 2026-10-03. -/
namespace G1OriginalSpanClosingPhase
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1OriginalSpanBridgeBookends
open G1OriginalSpanCalendarDecomposition G1CanonicalThreeEpochList G1OriginalCalendarDecomposition
open G1CanonicalComponentSegment G1CanonicalEpochSpecialization G1InitializedFrontierPrefix
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def EndsAt (O : Source X) (edge : O.Edge) {a b : O.Vertex} : OriginalSpan O.network a b → Prop
  | .edge e _ => e = edge
  | .bigon _ => False
  | .append _ last => EndsAt O edge last

lemma actual_end_cut_syntax (O : Source X) {a b : O.Vertex} (word : OriginalSpan O.network a b)
    (h : EndsBridge O word) :
    ∃ e : O.Edge, O.network.graph.IsBridge e ∧ O.network.graph.source e = b ∧ EndsAt O e word := by
  induction word with
  | edge e _ => exact ⟨e,h,rfl,rfl⟩
  | bigon _ => exact False.elim h
  | append _ _ _ ih => exact ih h

noncomputable def closingExits (O : Source X) (edge : O.Edge) : List O.Edge :=
  (originalExits O.network O.calendar (O.calendar.age (O.network.graph.source edge))).takeWhile
    (fun f => decide (f ≠ edge)) ++ [edge]

noncomputable def closingSpanAgenda (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool)
    (a b : O.Vertex) (edge : O.Edge) : List (ProgramStep O.network) :=
  canonicalEpochBlock O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) a b
    (closingExits O edge)

/-- Full internal exit batches remain before the next segment. The FINAL
batch is truncated precisely at the last original component exit. -/
theorem actual_closing_span_agenda_append (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b c : O.Vertex) (edge : O.Edge)
    (hab : O.calendar.age a < O.calendar.age b) (hbc : O.calendar.age b < O.calendar.age c) :
    closingSpanAgenda O H gamma common a c edge =
      fullSpanAgenda O.network O.calendar H gamma common a b ++ closingSpanAgenda O H gamma common b c edge := by
  have h := actual_stop_tail_middle_cut O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (afterDate O.network O.calendar (O.calendar.age a)) (original_after_ordered _ _ _)
    (O.calendar.age b) (O.calendar.age c) (original_after_member _ _ _ b hab) hbc (O.calendar.age a)
  have hf : (afterDate O.network O.calendar (O.calendar.age a)).filter (fun t => decide (O.calendar.age b < t)) =
      afterDate O.network O.calendar (O.calendar.age b) := filter_after_filter hab _
  rw [hf] at h
  unfold closingSpanAgenda fullSpanAgenda canonicalEpochBlock
  rw [h]
  have hb : boundaryOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b) =
      (originalExits O.network O.calendar (O.calendar.age b)).map (fun e => .boundary (.exit e)) ++
      nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age b) := rfl
  rw [hb]
  simp only [List.append_assoc]

end G1OriginalSpanClosingPhase
