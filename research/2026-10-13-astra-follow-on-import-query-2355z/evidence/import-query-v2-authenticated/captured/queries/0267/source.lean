import G1ActualComponentAgenda

/-! Canonical interleaved original-calendar component agenda. Contributor:
dot, 2026-10-03. All unrelated original dates and boundaries remain in place.
The phase starts before D's original node batch and closes precisely at the
original entry-edge exit within A0's exit batch. Its separator is DERIVED. -/
namespace G1CanonicalComponentSegment
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open G1CutChildPorts G1ActualTwoPortBlob G1ActualComponentAgenda G1InitializedFrontierPrefix
open G1ActualEnteringFrontier G1ComponentDescendantClosure G1ActualJointProgram
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def nodeOperations (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (a : ℝ) : List (ProgramStep N) :=
  ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
    (fun v => .boundary (originalNodeOperation N H gamma common v)))

noncomputable def exitsBeforeEntry (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) : List E :=
  (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = C.age (N.graph.source A.entry))).toList.takeWhile
    (fun e => decide (e ≠ A.entry))

noncomputable def phaseBeforeClosing (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) : List (ProgramStep N) :=
  nodeOperations N C H gamma common (C.age (N.graph.target A.child)) ++
    stopBeforeTail N C H gamma common (C.age (N.graph.source A.entry))
      (C.age (N.graph.target A.child))
      ((sortedOriginalDates N C).filter (fun a => decide (C.age (N.graph.target A.child) < a))) ++
    (exitsBeforeEntry N C b A).map (fun e => .boundary (.exit e))

noncomputable def componentAgenda (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) : List (ProgramStep N) :=
  phaseBeforeClosing N C b A H gamma common ++ [.boundary (.exit A.entry)]

lemma actual_component_dates_strict (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) :
    C.age (N.graph.target A.child) < C.age (N.graph.source A.entry) := by
  have hc := C.edge_older A.child
  have hp := C.edge_older A.fragment.parents.parent0
  have he := C.edge_older A.entry
  rw [A.child_source] at hc
  rw [A.fragment.parents.target0,show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false] at hp
  rw [A.entry_target] at he
  exact hc.trans (hp.trans he)

lemma actual_node_operations_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (a : ℝ)
    (op : ProgramStep N) (ho : op ∈ nodeOperations N C H gamma common a) :
    SafeOriginalStep N b A H gamma common op := by
  obtain ⟨v,_,hv⟩ := List.mem_map.mp ho
  exact Or.inr (Or.inr ⟨v,hv.symm⟩)

lemma actual_earlier_boundary_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (a : ℝ)
    (ha : a < C.age (N.graph.source A.entry)) (op : ProgramStep N)
    (ho : op ∈ boundaryOperations N C H gamma common a) : SafeOriginalStep N b A H gamma common op := by
  rcases List.mem_append.mp ho with hexit | hnode
  · obtain ⟨e,he,hop⟩ := List.mem_map.mp hexit
    have he := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    have hne : e ≠ A.entry := by
      intro h; subst e; exact (ne_of_lt ha) he.symm
    exact Or.inr (Or.inl ⟨e,hne,hop.symm⟩)
  · exact actual_node_operations_safe N C b A H gamma common a op hnode

lemma actual_stop_tail_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (dates : List ℝ)
    (horder : dates.Pairwise (· < ·)) (hstop : C.age (N.graph.source A.entry) ∈ dates)
    (a : ℝ) : ∀ op ∈ stopBeforeTail N C H gamma common (C.age (N.graph.source A.entry)) a dates,
      SafeOriginalStep N b A H gamma common op := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hstop)
  | cons c cs ih =>
      have hp := List.pairwise_cons.mp horder
      intro op hop
      by_cases hc : c = C.age (N.graph.source A.entry)
      · have heq : op = .interval (Real.toNNReal (c-a)) := by simpa [stopBeforeTail,hc] using hop
        exact Or.inl ⟨_,heq⟩
      · have hm : C.age (N.graph.source A.entry) ∈ cs := (List.mem_cons.mp hstop).resolve_left (Ne.symm hc)
        have hlt := hp.1 _ hm
        have hop : op = .interval (Real.toNNReal (c-a)) ∨
            op ∈ boundaryOperations N C H gamma common c ++ stopBeforeTail N C H gamma common (C.age (N.graph.source A.entry)) c cs := by
          simpa [stopBeforeTail,hc] using hop
        rcases hop with heq | hop
        · exact Or.inl ⟨_,heq⟩
        · rcases List.mem_append.mp hop with hboundary | htail
          · exact actual_earlier_boundary_safe N C b A H gamma common c hlt op hboundary
          · exact ih hp.2 hm c op htail

lemma takeWhile_avoids {A : Type*} [DecidableEq A] (e : A) (es : List A) :
    ∀ f ∈ es.takeWhile (fun f => decide (f ≠ e)), f ≠ e := by
  induction es with
  | nil => simp
  | cons a as ih =>
      by_cases ha : a ≠ e
      · intro f hf
        have hf : f = a ∨ f ∈ as.takeWhile (fun f => decide (f ≠ e)) := by simpa [ha] using hf
        rcases hf with rfl | hf
        · exact ha
        · exact ih f hf
      · simp [ha]

/-- Every operation of the derived canonical interleaved phase before its
closing entry exit is a safe ORIGINAL operation. No desired law is supplied. -/
theorem actual_canonical_component_safe_prefix (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    ∀ op ∈ phaseBeforeClosing N C b A H gamma common, SafeOriginalStep N b A H gamma common op := by
  have horder : ((sortedOriginalDates N C).filter (fun a => decide (C.age (N.graph.target A.child) < a))).Pairwise (· < ·) :=
    (UnifiedLean.Source.SourceCalendarTiming.original_dates_strict N C).filter _
  have hstop : C.age (N.graph.source A.entry) ∈
      (sortedOriginalDates N C).filter (fun a => decide (C.age (N.graph.target A.child) < a)) := by
    simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨original_date_scheduled N C _,actual_component_dates_strict N C b A⟩
  intro op hop
  rcases List.mem_append.mp hop with hfirst | hexit
  · rcases List.mem_append.mp hfirst with hnode | htail
    · exact actual_node_operations_safe N C b A H gamma common _ op hnode
    · exact actual_stop_tail_safe N C b A H gamma common _ horder hstop _ op htail
  · obtain ⟨e,he,hop⟩ := List.mem_map.mp hexit
    exact Or.inr (Or.inl ⟨e,takeWhile_avoids A.entry _ e he,hop.symm⟩)

/-- The complete canonical actual agenda obtains its separator from the
NATURALLY initialized CURRENT-root interface, without an original Copy cap. -/
theorem actual_initialized_canonical_component_agenda (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    {s : Code N sample}
    (hs : s ∈ (UnifiedLean.Source.SourceProgramTransport.sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (UnifiedLean.Source.SourceInitializedCalendar.initialCode N sample register)).support) :
    SeparatedAgenda N r (enteringRoots N s (N.graph.target A.child))
      (exteriorRoots N s (N.graph.target A.child)) (componentAgenda N C b A H gamma common) s := by
  obtain ⟨_,hin,hout⟩ := actual_initialized_cut_frontier N C sample register H gamma common r A.child A.child_bridge hs
  apply actual_original_component_separated_agenda N hc b A H gamma common r _
    (actual_canonical_component_safe_prefix N C b A H gamma common) s _ _ _ hout
  intro x hx
  rw [hin x hx]
  exact Or.inl rfl

end G1CanonicalComponentSegment
