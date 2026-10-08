import G1OriginalEpochPanelCompression
import G1CanonicalEpochSpecialization
import G1OriginalCurrentRootReconstruction
import G5ParentChoiceCalendar

/-!
# Actual original parent-path slices with unequal older endpoints

Cloud G3, 2026-10-08. Compiler UNCHECKED, outside shared source freezes.
The original routes, dates, compiler, rates and whole register are unchanged.
The main new row proves compression when every occupied edge ends AT OR AFTER
next cut, rather than requiring all occupied edges to share that endpoint.
No desired kernel/source law, path coverage, or independence equality is a field.
Full mixed-boundary fork serialization and Kingman regrouping remain hand-level.
-/
namespace CloudG3.GroupedParentPathCalendar
set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.UnrankedGenealogyObservation
open G1CutChildPorts G1OriginalEpochPanelSilence G1OriginalEpochPanelCompression
open G1InterleavedEpochCompression G1CanonicalThreeEpochList G1OriginalCalendarDecomposition
open G1InitializedFrontierPrefix
open G1CanonicalEpochSpecialization G1OriginalCurrentRootReconstruction
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Cut-child plus the constructed nonbridge route excludes another original
hybrid at EVERY arm-route source vertex. -/
theorem actual_parent_route_sources_nonhybrid (N : RootedBinary V E X)
    (hc : CutChild N) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) {e : E}
    (hm : e ∈ parentRoute H he bit) : ¬ N.graph.IsHybrid (N.graph.source e) := by
  intro hh
  exact parentRoute_nonbridge H he bit e hm (hc e hh)

/-- Original ordinary-node indegree, with the possible root explicitly excluded. -/
theorem actual_parent_route_source_ordinary (N : RootedBinary V E X)
    (hc : CutChild N) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) {e : E}
    (hm : e ∈ parentRoute H he bit) (hr : N.graph.source e ≠ N.root) :
    N.graph.inDegree (N.graph.source e) = 1 :=
  N.indegree_one_of_nonroot_nonhybrid hr
    (actual_parent_route_sources_nonhybrid N hc H he bit hm)

/-- Strict age is obtained from an actual final parent edge and its path. -/
theorem actual_parent_route_entry_older (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) : C.age H.hybrid < C.age entry := by
  have hm : H.parent false ∈ parentRoute H he false := by simp [parentRoute]
  have hs := (parentRoute_path H he false).source_age_le C hm
  have hl := C.edge_older (H.parent false)
  rw [original_parent_target H false] at hl
  exact hl.trans_le hs

/-- This weaker physical bound is enough to derive actual boundary silence. -/
theorem actual_earlier_boundary_edge_safe_of_end_ge (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (edges : Finset E) (b a : ℝ) (ha : a < b)
    (hend : ∀ e ∈ edges, b ≤ C.age (N.graph.source e)) :
    ∀ op ∈ boundaryOperations N C R gamma common a,
      EdgeSafeStep N R gamma common edges op := by
  intro op hop
  rcases List.mem_append.mp hop with hiexit | hinode
  · obtain ⟨e,he,hop⟩ := List.mem_map.mp hiexit
    have he := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    have hnot : e ∉ edges := by
      intro hm
      have hb := hend e hm
      rw [he] at hb
      exact (not_le_of_gt ha) hb
    exact Or.inr (Or.inl ⟨e,hnot,hop.symm⟩)
  · obtain ⟨v,_,hop⟩ := List.mem_map.mp hinode
    exact Or.inr (Or.inr ⟨v,hop.symm⟩)

/-- Actual all-original stop-tail syntax inherits the weaker endpoint bound. -/
theorem actual_stop_tail_edge_safe_of_end_ge (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (edges : Finset E) (b : ℝ) (hend : ∀ e ∈ edges, b ≤ C.age (N.graph.source e))
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (hb : b ∈ dates) (a : ℝ) :
    ∀ op ∈ stopBeforeTail N C R gamma common b a dates,
      EdgeSafeStep N R gamma common edges op := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hb)
  | cons c cs ih =>
      have hp := List.pairwise_cons.mp horder
      intro op hop
      by_cases hc : c = b
      · have heq : op = .interval (Real.toNNReal (c-a)) := by
          simpa [stopBeforeTail,hc] using hop
        exact Or.inl ⟨_,heq⟩
      · have hm : b ∈ cs := (List.mem_cons.mp hb).resolve_left (Ne.symm hc)
        have hop : op = .interval (Real.toNNReal (c-a)) ∨
            op ∈ boundaryOperations N C R gamma common c ++
              stopBeforeTail N C R gamma common b c cs := by
          simpa [stopBeforeTail,hc] using hop
        rcases hop with heq | hop
        · exact Or.inl ⟨_,heq⟩
        · rcases List.mem_append.mp hop with hboundary | htail
          · exact actual_earlier_boundary_edge_safe_of_end_ge N C R gamma common edges b c
              (hp.1 _ hm) hend op hboundary
          · exact ih hp.2 hm c op htail

/-- Principal new ACTUAL source row. The original outside operations still
execute; only the selected whole genealogy/population/register view is read. -/
theorem actual_unequal_endpoint_epoch_row (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) {sample : Copy → X} (r : PositivePairRates E)
    (keep : Finset Copy) (edges : Finset E) (dates : List ℝ)
    (horder : dates.Pairwise (· < ·)) (b : ℝ) (hb : b ∈ dates)
    (hend : ∀ e ∈ edges, b ≤ C.age (N.graph.source e)) (a : ℝ)
    (ha : ∀ c ∈ dates, a ≤ c) (s : Code N sample)
    (hs : AtEdgePanel (state s) keep edges) :
    (sourceProgram N r (stopBeforeTail N C R gamma common b a dates) s).map
      (projection N keep) =
    (sourceTimeKernel N r (Real.toNNReal (b-a)) s).map (projection N keep) := by
  exact actual_interleaved_original_date_partition N r keep _ s
    (actual_edge_safe_agenda_silent N R gamma common r _ edges
      (actual_stop_tail_edge_safe_of_end_ge N C R gamma common edges b hend dates horder hb a)
      s keep hs)
    (actual_stop_tail_duration_partition N C R gamma common dates horder b hb a ha)

noncomputable def occupiedParentEdges (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) : Finset E :=
  Finset.univ.image (parentPosition C H he hl hu)

/-- Minimum of TWO actual original older endpoints, not a fitted cut. -/
noncomputable def nextParentCut (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) : ℝ :=
  min (C.age (N.graph.source (parentPosition C H he hl hu false)))
    (C.age (N.graph.source (parentPosition C H he hl hu true)))

theorem actual_next_parent_cut_later (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    t < nextParentCut N C H he hl hu := by
  exact lt_min (parentPosition_spec C H he hl hu false).2.2
    (parentPosition_spec C H he hl hu true).2.2

theorem actual_next_parent_cut_is_original_date (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    nextParentCut N C H he hl hu ∈ afterDate N C t := by
  unfold nextParentCut
  by_cases hf : C.age (N.graph.source (parentPosition C H he hl hu false)) ≤
      C.age (N.graph.source (parentPosition C H he hl hu true))
  · rw [min_eq_left hf]
    exact original_after_member N C t _ (parentPosition_spec C H he hl hu false).2.2
  · rw [min_eq_right (le_of_not_ge hf)]
    exact original_after_member N C t _ (parentPosition_spec C H he hl hu true).2.2

theorem actual_occupied_parent_edges_end_ge_cut (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    ∀ e ∈ occupiedParentEdges N C H he hl hu,
      nextParentCut N C H he hl hu ≤ C.age (N.graph.source e) := by
  intro e hm
  obtain ⟨bit,_,rfl⟩ := Finset.mem_image.mp hm
  cases bit with
  | false => exact min_le_left _ _
  | true => exact min_le_right _ _

noncomputable def parentPairSliceProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) : List (ProgramStep N) :=
  stopBeforeTail N C R gamma common (nextParentCut N C H he hl hu) t (afterDate N C t)

/-- A completely constructed actual-parent slice: ordering, cut membership,
endpoint bounds and all selected-silence premises are DERIVED. -/
theorem actual_parent_pair_slice_source_row (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (hs : AtEdgePanel (state s) keep (occupiedParentEdges N C H he hl hu)) :
    (sourceProgram N r (parentPairSliceProgram N C R gamma common H he hl hu) s).map
      (projection N keep) =
    (sourceTimeKernel N r (Real.toNNReal (nextParentCut N C H he hl hu-t)) s).map
      (projection N keep) := by
  apply actual_unequal_endpoint_epoch_row N C R gamma common r keep _ _
    (original_after_ordered N C t) _ (actual_next_parent_cut_is_original_date N C H he hl hu)
    (actual_occupied_parent_edges_end_ge_cut N C H he hl hu) t _ s hs
  intro c hc
  exact ((List.mem_filter.mp hc).2 |> of_decide_eq_true).le

/-- The full ORIGINAL calendar phase from h to join keeps every outside date;
it stops before the join's node batch and includes its original exit batch. -/
noncomputable def forkCalendarProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (h join : V) : List (ProgramStep N) :=
  canonicalEpochBlock N C R gamma common h join (originalExits N C (C.age join))

/-- The unchanged complete calendar future starts with the join node batch. -/
noncomputable def forkCalendarFuture (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (join : V) : List (ProgramStep N) :=
  nodeOperations N C R gamma common (C.age join) ++
    calendarTail N C R gamma common (C.age join) (afterDate N C (C.age join))

/-- The fork phase is literally part of the SAME full original compiler.
No NonrootBigon/OriginalSpan or desired program equality is a premise. -/
theorem actual_full_calendar_fork_decomposition (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (h join : V) (hdate : C.age h < C.age join) :
    compiledCalendarProgram N C R gamma common =
      actualFrontierProgram N C R gamma common (C.age h) ++
        forkCalendarProgram N C R gamma common h join ++
          forkCalendarFuture N C R gamma common join := by
  have hstart := actual_compiled_calendar_date_cut N C R gamma common (C.age h)
    (original_date_scheduled N C h)
  have hmiddle := actual_calendar_tail_cut N C R gamma common
    (afterDate N C (C.age h)) (original_after_ordered N C _) (C.age join)
    (original_after_member N C _ join hdate) (C.age h)
  have hf : (afterDate N C (C.age h)).filter (fun c => decide (C.age join < c)) =
      afterDate N C (C.age join) := filter_after_filter hdate _
  rw [hstart,hmiddle,hf]
  have hbatch (a : ℝ) : boundaryOperations N C R gamma common a =
      (originalExits N C a).map (fun e => .boundary (.exit e)) ++
        nodeOperations N C R gamma common a := rfl
  rw [hbatch,hbatch]
  simp only [actualFrontierProgram,forkCalendarProgram,canonicalEpochBlock,
    forkCalendarFuture,originalExits,List.append_assoc]

/-- Existing original/current-root/graft/context law instantiated at the
ACTUAL fork calendar programme. This does not assert the grouped Kingman law. -/
theorem actual_fork_calendar_current_root_context (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} {History Obs : Type*} (r : PositivePairRates E)
    (h join : V) (s : Code N sample)
    (hs : ∀ l ∈ (state s).live, (state s).location l = .node h)
    (history : History)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    (sourceProgram N r (forkCalendarProgram N C R gamma common h join) s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
    (smallerCurrentRootKernel N r (forkCalendarProgram N C R gamma common h join)
      s (.node h) hs).bind
      (fun F => exterior (history,(state s).register,
        F.image (G1OpaqueSourceGrafting.graftUnranked (fun l => (state s).genealogy l.val)))) :=
  actual_original_contextual_forest_replacement N r _ s (.node h) hs history exterior

end CloudG3.GroupedParentPathCalendar
