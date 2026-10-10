import G1DerivedSpanSeparatedAgenda

/-! The literal original closing phase has a safe prefix and precisely one
last cut-edge exit. Contributor: dot, 2026-10-03. -/
namespace G1ClosingSpanSafeSyntax
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1OriginalSpanClosingPhase G1CanonicalThreeEpochList
open G1CanonicalEpochSpecialization G1CanonicalComponentSegment G1InitializedFrontierPrefix
open G1OriginalCalendarDecomposition G1OriginalEpochPanelCompression
open scoped Classical NNReal
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def closingSpanPrefix (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b : O.Vertex) (edge : O.Edge) :
    List (ProgramStep O.network) :=
  nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age a) ++
  stopBeforeTail O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
    (O.calendar.age b) (O.calendar.age a) (afterDate O.network O.calendar (O.calendar.age a)) ++
  ((originalExits O.network O.calendar (O.calendar.age (O.network.graph.source edge))).takeWhile
    (fun f => decide (f ≠ edge))).map (fun e => .boundary (.exit e))

lemma actual_closing_span_prefix_last (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b : O.Vertex) (edge : O.Edge) :
    closingSpanAgenda O H gamma common a b edge = closingSpanPrefix O H gamma common a b edge ++ [.boundary (.exit edge)] := by
  simp only [closingSpanAgenda,canonicalEpochBlock,closingSpanPrefix,closingExits,List.map_append,
    List.map_singleton,List.append_assoc]

theorem actual_closing_span_prefix_safe (O : Source X) (H : OriginalParentRegistry O.network)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (a b : O.Vertex) (edge : O.Edge)
    (hb : O.network.graph.source edge = b) (hab : O.calendar.age a < O.calendar.age b) :
    ∀ op ∈ closingSpanPrefix O H gamma common a b edge,
      EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val) {edge} op := by
  have hsource : ∀ e ∈ ({edge} : Finset O.Edge), O.calendar.age (O.network.graph.source e) = O.calendar.age b := by
    intro e he
    have he : e = edge := Finset.mem_singleton.mp he
    subst e; exact congrArg O.calendar.age hb
  intro op hop
  rcases List.mem_append.mp hop with hleft | hexit
  · rcases List.mem_append.mp hleft with hnode | htail
    · obtain ⟨v,_,hv⟩ := List.mem_map.mp hnode
      exact Or.inr (Or.inr ⟨v,hv.symm⟩)
    · exact actual_stop_tail_edge_safe O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val)
        {edge} (O.calendar.age b) hsource _ (original_after_ordered _ _ _)
        (original_after_member _ _ _ b hab) _ op htail
  · obtain ⟨e,he,hop⟩ := List.mem_map.mp hexit
    exact Or.inr (Or.inl ⟨e,by simpa using takeWhile_avoids edge _ e he,hop.symm⟩)

end G1ClosingSpanSafeSyntax
