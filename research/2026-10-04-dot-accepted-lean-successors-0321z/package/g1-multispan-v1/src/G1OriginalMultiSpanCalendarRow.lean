import G1OriginalSpanAtomAdmission

/-! Exact complete original inside-source row for arbitrary registered finite
original spans. Contributor: dot, 2026-10-03. All external dates/batches remain
processed; only the full selected-state row is compressed to its literal word. -/
namespace G1OriginalMultiSpanCalendarRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open G1OriginalDecoratedSpan G1OriginalSpanCalendarDecomposition G1OriginalSpanAtomAdmission
open G1OriginalNodeBatchBinding G1CanonicalEpochBlockBinding G1CompactSourceComposition
open G1CompactComponentBlockRows G1ExtractedComponentProgram G1OriginalCalendarDecomposition
open G1ActualJointProgram G1SameOriginalExteriorContinuation
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- One fixed original registry/gamma/mode assignment works for the whole
finite word. Full genealogy, populations and SAME register are retained. -/
theorem actual_original_registered_span_calendar_row_and_exit (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (gamma : V → unitInterval) (common : V → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    {a b : V} (word : OriginalSpan N a b) (hr : RegistrySpan N H word)
    (s : Code N sample) (hs : AtNodePanel (state s) keep a) :
    (sourceProgram N r (fullSpanAgenda N C H gamma common a b) s).map (projection N keep) =
      (sourceProgram N r (spanProgram N C gamma common word) s).map (projection N keep) ∧
    (∀ d ∈ (sourceProgram N r (spanProgram N C gamma common word) s).support,
      AtNodePanel (state d) keep b) := by
  induction word generalizing s with
  | edge e degree =>
      refine ⟨?_,fun d hd => actual_original_edge_span_atom_exit N H gamma common r keep C e degree s hs hd⟩
      have he : e ∈ originalExits N C (C.age (N.graph.source e)) :=
        Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩)
      simpa only [fullSpanAgenda,spanProgram] using
        (actual_canonical_ordinary_block_row N C H (fun h => gamma h.val) (fun h => common h.val) r keep
          e degree (originalExits N C (C.age (N.graph.source e))) he s hs)
  | bigon B =>
      exact ⟨actual_original_bigon_span_atom_row N C H gamma common r keep B hr s hs,
        fun d hd => actual_original_bigon_span_atom_exit N H gamma common r keep C B hr s hs hd⟩
  | @append a mid b first last ihfirst ihlast =>
      obtain ⟨hrfirst,hrlast⟩ := hr
      have hfirst := ihfirst hrfirst s hs
      have hactualout {d : Code N sample}
          (hd : d ∈ (sourceProgram N r (fullSpanAgenda N C H gamma common a mid) s).support) :
          AtNodePanel (state d) keep mid :=
        actual_block_exit_support_from_row N r keep _ _ s mid hfirst.1 hfirst.2 hd
      refine ⟨?_,?_⟩
      · rw [actual_full_span_agenda_append N C H gamma common a mid b
          (actual_span_dates_strict N C first) (actual_span_dates_strict N C last)]
        change (sourceProgram N r (fullSpanAgenda N C H gamma common a mid ++
          fullSpanAgenda N C H gamma common mid b) s).map (projection N keep) =
          (sourceProgram N r (spanProgram N C gamma common first ++ spanProgram N C gamma common last) s).map
            (projection N keep)
        calc
          _ = (sourceProgram N r (fullSpanAgenda N C H gamma common a mid ++
              spanProgram N C gamma common last) s).map (projection N keep) := by
            rw [actual_source_program_append,actual_source_program_append,PMF.map_bind,PMF.map_bind]
            apply bind_eq_of_eq_on_support
            intro d hd
            exact (ihlast hrlast d (hactualout hd)).1
          _ = _ := actual_source_row_suffix_congr N r keep _ _ _ s hfirst.1
      · intro d hd
        rw [spanProgram,actual_source_program_append] at hd
        obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        exact (ihlast hrlast z (hfirst.2 z hz)).2 d hd

#print axioms actual_original_registered_span_calendar_row_and_exit
end G1OriginalMultiSpanCalendarRow
