import G1OriginalComponentNodeIdentity

/-! Original node/epoch/exit block binding. Contributor: dot, 2026-10-03.
Original demographic rates and durations are retained by the actual source. -/
namespace G1CanonicalEpochBlockBinding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceBoundaryProjection UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourcePoissonKernel
open G1OriginalEpochPanelSilence G1OriginalEpochPanelCompression G1OriginalNodeBatchBinding
open G1OriginalExitBatchBinding G1CompactSourceComposition G1ActualJointProgram
open G1SameOriginalExteriorContinuation G1InitializedFrontierPrefix
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_epoch_exit_block_binding (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (edges : Finset E)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (a b : ℝ) (hb : b ∈ dates)
    (ha : ∀ c ∈ dates, a ≤ c) (U : V) (hU : C.age U = b)
    (hsource : ∀ e ∈ edges, N.graph.source e = U) (es canonical : List E)
    (hcover : ∀ e ∈ edges, e ∈ es) (hcanonical : ∀ e ∈ edges, e ∈ canonical)
    (s : Code N sample) (hs : AtEdgePanel (state s) keep edges) :
    (sourceProgram N r (stopBeforeTail N C H gamma common b a dates ++
      es.map (fun e => .boundary (.exit e))) s).map (projection N keep) =
    (sourceProgram N r ([.interval (Real.toNNReal (b-a))] ++
      canonical.map (fun e => .boundary (.exit e))) s).map (projection N keep) := by
  have hc := actual_canonical_edge_panel_epoch_compression N C H gamma common r keep edges
    dates horder b hb (fun e he => by rw [hsource e he,hU]) a ha s hs
  have hc' : (sourceProgram N r (stopBeforeTail N C H gamma common b a dates) s).map (projection N keep) =
      (sourceProgram N r [.interval (Real.toNNReal (b-a))] s).map (projection N keep) := by
    simpa [sourceProgram,sourceProgramStep] using hc
  calc
    _ = (sourceProgram N r ([.interval (Real.toNNReal (b-a))] ++
        es.map (fun e => .boundary (.exit e))) s).map (projection N keep) :=
      actual_source_row_suffix_congr N r keep _ _ _ s hc'
    _ = _ := by
      simp only [List.singleton_append,sourceProgram,sourceProgramStep,PMF.map_bind]
      apply bind_eq_of_eq_on_support
      intro d hd
      exact actual_complete_exit_batch_inside_law N r es canonical d keep edges U
        (actual_time_edge_panel N r _ s keep edges hs hd) hsource hcover hcanonical

/-- All original same-date nodes, every interleaved exterior boundary and all
original exits have the complete inside law of the one original node,
original unchanged epoch, and canonical exiting edges. -/
theorem actual_node_epoch_exit_block_binding (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (vs : List V) (D : V) (hr : D ≠ N.root) (hD : D ∈ vs)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (a b : ℝ) (hb : b ∈ dates)
    (ha : ∀ c ∈ dates, a ≤ c) (U : V) (hU : C.age U = b)
    (hsource : ∀ e ∈ incomingEdges N D, N.graph.source e = U) (es canonical : List E)
    (hcover : ∀ e ∈ incomingEdges N D, e ∈ es)
    (hcanonical : ∀ e ∈ incomingEdges N D, e ∈ canonical)
    (s : Code N sample) (hs : AtNodePanel (state s) keep D) :
    (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v)) ++
      stopBeforeTail N C H gamma common b a dates ++ es.map (fun e => .boundary (.exit e))) s).map (projection N keep) =
    (sourceProgram N r ([.boundary (originalNodeOperation N H gamma common D),.interval (Real.toNNReal (b-a))] ++
      canonical.map (fun e => .boundary (.exit e))) s).map (projection N keep) := by
  have hn := actual_original_node_list_binding N H gamma common r vs D hr hD s keep hs
  have hn' : (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s).map
      (projection N keep) = (sourceProgram N r [.boundary (originalNodeOperation N H gamma common D)] s).map
        (projection N keep) := by simpa [sourceProgram,sourceProgramStep] using hn
  rw [List.append_assoc]
  calc
    _ = (sourceProgram N r ([.boundary (originalNodeOperation N H gamma common D)] ++
        (stopBeforeTail N C H gamma common b a dates ++ es.map (fun e => .boundary (.exit e)))) s).map
        (projection N keep) := actual_source_row_suffix_congr N r keep _ _ _ s hn'
    _ = _ := by
      simp only [List.singleton_append,List.cons_append,sourceProgram,sourceProgramStep,PMF.map_bind]
      apply bind_eq_of_eq_on_support
      intro d hd
      simpa only [List.nil_append,List.singleton_append,sourceProgram,sourceProgramStep,PMF.map_bind] using
        (actual_epoch_exit_block_binding N C H gamma common r keep (incomingEdges N D)
          dates horder a b hb ha U hU hsource es canonical hcover hcanonical d
          (actual_own_node_enters_edges N H gamma common s keep D hr hs hd))

lemma actual_compact_epoch_block_exit_support (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (D U : V) (hr : D ≠ N.root) (t : ℝ≥0) (canonical : List E)
    (hsource : ∀ e ∈ incomingEdges N D, N.graph.source e = U)
    (hcover : ∀ e ∈ incomingEdges N D, e ∈ canonical)
    (s : Code N sample) (hs : AtNodePanel (state s) keep D)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r
      ([.boundary (originalNodeOperation N H gamma common D),.interval t] ++
        canonical.map (fun e => .boundary (.exit e))) s).support) :
    AtNodePanel (state d) keep U := by
  simp only [List.cons_append,List.nil_append,sourceProgram,sourceProgramStep] at hd
  obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  obtain ⟨w,hw,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hnodes := actual_own_node_enters_edges N H gamma common s keep D hr hs hz
  have hedges := actual_time_edge_panel N r t z keep (incomingEdges N D) hnodes hw
  rw [actual_exit_list_program] at hd
  have he : d = exitCodeList N canonical w := by simpa using hd
  subst d
  intro x hx
  obtain ⟨e,he,hpop⟩ := hedges x hx
  rw [actual_exit_list_copy_location,hpop,actual_exit_location_list_hit N canonical e (hcover e he),hsource e he]

/-- Population support is transported through a PROVED complete selected-row
identity, with actual witnesses from the compact ORIGINAL source support. -/
lemma actual_block_exit_support_from_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (xs ys : List (ProgramStep N))
    (s : Code N sample) (U : V)
    (heq : (sourceProgram N r xs s).map (projection N keep) =
      (sourceProgram N r ys s).map (projection N keep))
    (hys : ∀ d ∈ (sourceProgram N r ys s).support, AtNodePanel (state d) keep U)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r xs s).support) :
    AtNodePanel (state d) keep U := by
  obtain ⟨z,hz,hview⟩ := actual_projected_support_transfer N keep _ _ heq hd
  intro x hx
  exact (actual_projected_copy_location N keep d z hview.symm x hx).trans (hys z hz x hx)

end G1CanonicalEpochBlockBinding
