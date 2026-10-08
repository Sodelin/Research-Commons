import FirstParentJoin
import G1OriginalExitBatchBinding

/-!
Cloud G3 actual mixed original parent-path boundary consumer, 2026-10-08.
Compiler UNCHECKED. The physical node set and its source support are derived
from locations and original exits. Foreign same-date node operations are erased
ONLY from the selected marginal; the actual whole-source compiler still runs.
No desired projection law, fresh COMMON register, outside independence or
original graph-to-word coverage field is introduced.
-/
namespace CloudG3.MixedParentBoundary
set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceCalendarPhysicalSupport
open G1OriginalNodeBatchBinding G1OriginalExitBatchBinding
open G1OriginalEpochPanelSilence G1ExteriorBoundarySilence G1ActualJointProgram
open G1OriginalCalendarDecomposition G1CanonicalComponentSegment
open G1InitializedFrontierPrefix G1CutChildPorts
open CloudG3.FirstParentJoin CloudG3.GroupedParentPathCalendar
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Only a physical location restriction. Edge/root populations and opaque
outside roots are unrestricted; no kernel equality is part of this predicate. -/
def NodesWithin (s : State V E Copy) (keep : Finset Copy) (nodes : Finset V) : Prop :=
  ∀ x ∈ keep, ∀ v : V, copyLocation s x = .node v → v ∈ nodes

noncomputable def nodeListProgram (N : RootedBinary V E X)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (vs : List V) : List (ProgramStep N) :=
  vs.map (fun v => .boundary (originalNodeOperation N R gamma common v))

/-- Derived from the ACTUAL original node kernel, including both hybrid modes. -/
theorem actual_node_support_nodes_within (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (s : Code N sample) (keep : Finset Copy) (nodes : Finset V)
    (hs : NodesWithin (state s) keep nodes) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N R gamma common v) s).support) :
    NodesWithin (state d) keep nodes := by
  intro x hx u hu
  have hm := actual_original_node_kernel_movement N R gamma common v s hd x
  have hold : copyLocation (state s) x = .node u := by
    by_contra hn
    exact node_move_never_creates_node N hm hn hu
  exact hs x hx u hold

/-- A node outside the physically possible selected node set is absent. -/
theorem actual_foreign_node_set_absent (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (s : Code N sample) (keep : Finset Copy) (nodes : Finset V)
    (hv : v ∉ nodes) (hs : NodesWithin (state s) keep nodes) :
    PanelAbsent N (originalNodeOperation N R gamma common v) (state s) keep := by
  intro x hx hloc
  rw [actual_node_touched_site] at hloc
  exact hv (hs x hx v hloc)

/-- All supported destinations of the literal actual node list retain the
same physical node-set bound; no normalization or fictitious support is used. -/
theorem actual_node_list_support_nodes_within (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (vs : List V) (s : Code N sample)
    (keep : Finset Copy) (nodes : Finset V) (hs : NodesWithin (state s) keep nodes)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (nodeListProgram N R gamma common vs) s).support) :
    NodesWithin (state d) keep nodes := by
  induction vs generalizing s with
  | nil =>
      have hds : d = s := by simpa [nodeListProgram,sourceProgram] using hd
      subst d
      exact hs
  | cons v vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N R gamma common v) s).bind
        (sourceProgram N r (nodeListProgram N R gamma common vs))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (actual_node_support_nodes_within N R gamma common v s keep nodes hs hm) hdm

/-- Principal mixed-node law: the whole selected genealogy/population/SAME
register marginal of the actual list equals its physically relevant sublist.
The list order, original operations and their true source kernels are retained. -/
theorem actual_node_list_filtered_law (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (vs : List V) (s : Code N sample)
    (keep : Finset Copy) (nodes : Finset V) (hs : NodesWithin (state s) keep nodes) :
    (sourceProgram N r (nodeListProgram N R gamma common vs) s).map (projection N keep) =
      (sourceProgram N r (nodeListProgram N R gamma common
        (vs.filter (fun v => decide (v ∈ nodes)))) s).map (projection N keep) := by
  induction vs generalizing s with
  | nil => rfl
  | cons v vs ih =>
      by_cases hv : v ∈ nodes
      · have hfilter : (v :: vs).filter (fun u => decide (u ∈ nodes)) =
            v :: vs.filter (fun u => decide (u ∈ nodes)) := by simp [hv]
        rw [hfilter]
        simp only [nodeListProgram,List.map_cons,sourceProgram,sourceProgramStep,PMF.map_bind]
        apply bind_eq_of_eq_on_support
        intro d hd
        exact ih d (actual_node_support_nodes_within N R gamma common v s keep nodes hs hd)
      · have hfilter : (v :: vs).filter (fun u => decide (u ∈ nodes)) =
            vs.filter (fun u => decide (u ∈ nodes)) := by simp [hv]
        rw [hfilter]
        simp only [nodeListProgram,List.map_cons,sourceProgram,sourceProgramStep,PMF.map_bind]
        calc
          _ = (boundaryKernel N (originalNodeOperation N R gamma common v) s).bind
              (fun d => (sourceProgram N r (nodeListProgram N R gamma common
                (vs.filter (fun u => decide (u ∈ nodes)))) d).map (projection N keep)) := by
            apply bind_eq_of_eq_on_support
            intro d hd
            exact ih d (actual_node_support_nodes_within N R gamma common v s keep nodes hs hd)
          _ = (boundaryKernel N (originalNodeOperation N R gamma common v) s).bind
              (fun _ => (sourceProgram N r (nodeListProgram N R gamma common
                (vs.filter (fun u => decide (u ∈ nodes)))) s).map (projection N keep)) := by
            apply bind_eq_of_eq_on_support
            intro d hd
            have hp := actual_untouched_boundary_panel N _ s keep
              (actual_foreign_node_set_absent N R gamma common v s keep nodes hv hs) hd
            rw [actual_source_program_projection,actual_source_program_projection,hp]
          _ = _ := PMF.bind_const _ _

/-- Missing an original edge in a literal exit list leaves its location fixed. -/
theorem actual_exit_location_list_miss (N : RootedBinary V E X)
    (es : List E) (e : E) (he : e ∉ es) : exitLocationList N es (.edge e) = .edge e := by
  induction es with
  | nil => rfl
  | cons f fs ih =>
      have hef : e ≠ f := fun h => he (List.mem_cons.mpr (Or.inl h))
      have htail : e ∉ fs := fun h => he (List.mem_cons_of_mem f h)
      simpa [exitLocationList,exitLocation,hef] using ih htail

/-- Membership is determined by the SAME original source endpoint age. -/
theorem actual_original_exit_mem_iff (N : RootedBinary V E X)
    (C : Calendar N.graph) (b : ℝ) (e : E) :
    e ∈ originalExits N C b ↔ C.age (N.graph.source e) = b := by
  simp [originalExits]

/-- Unequal arm ends are handled without forcing both into one upper node. -/
theorem actual_original_exit_list_edge_position (N : RootedBinary V E X)
    (C : Calendar N.graph) (b : ℝ) (e : E) :
    exitLocationList N (originalExits N C b) (.edge e) =
      if C.age (N.graph.source e) = b then .node (N.graph.source e) else .edge e := by
  by_cases ha : C.age (N.graph.source e) = b
  · rw [if_pos ha]
    exact actual_exit_location_list_hit N _ e ((actual_original_exit_mem_iff N C b e).mpr ha)
  · rw [if_neg ha]
    exact actual_exit_location_list_miss N _ e (fun h => ha ((actual_original_exit_mem_iff N C b e).mp h))

/-- Actual pending nodes after all exits, extracted from original occupied IDs. -/
noncomputable def endingNodes (N : RootedBinary V E X) (C : Calendar N.graph)
    (b : ℝ) (edges : Finset E) : Finset V :=
  (edges.filter (fun e => C.age (N.graph.source e) = b)).image N.graph.source

/-- Physical mixed frontier of a complete ORIGINAL exit batch. The remaining
selected copies stay on nonending edges; only ending source nodes are possible. -/
theorem actual_original_exit_batch_nodes_within (N : RootedBinary V E X)
    {sample : Copy → X} (C : Calendar N.graph) (b : ℝ) (s : Code N sample)
    (keep : Finset Copy) (edges : Finset E) (hs : AtEdgePanel (state s) keep edges) :
    NodesWithin (state (exitCodeList N (originalExits N C b) s)) keep (endingNodes N C b edges) := by
  intro x hx v hv
  obtain ⟨e,he,hpop⟩ := hs x hx
  rw [actual_exit_list_copy_location,hpop,actual_original_exit_list_edge_position] at hv
  by_cases ha : C.age (N.graph.source e) = b
  · rw [if_pos ha] at hv
    exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨he,ha⟩,Location.node.inj hv⟩
  · rw [if_neg ha] at hv
    cases hv

/-- Actual full boundary, conditional on any edge-panel entering Code. All
original exits execute. The node sublist is derived from the exit destinations,
not supplied as a law. Equal ages at unrelated endpoints are permitted. -/
theorem actual_original_mixed_boundary_filtered_law (N : RootedBinary V E X)
    {sample : Copy → X} (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (b : ℝ) (s : Code N sample)
    (keep : Finset Copy) (edges : Finset E) (hs : AtEdgePanel (state s) keep edges) :
    let vs := (Finset.univ.filter (fun v : V => C.age v = b)).toList
    (sourceProgram N r (boundaryOperations N C R gamma common b) s).map (projection N keep) =
      (sourceProgram N r
        ((originalExits N C b).map (fun e => .boundary (.exit e)) ++
          nodeListProgram N R gamma common
            (vs.filter (fun v => decide (v ∈ endingNodes N C b edges))))) s).map (projection N keep) := by
  change (sourceProgram N r
      ((originalExits N C b).map (fun e => .boundary (.exit e)) ++
        nodeListProgram N R gamma common ((Finset.univ.filter (fun v : V => C.age v = b)).toList)) s).map
        (projection N keep) = _
  rw [sourceProgram_append,sourceProgram_append,actual_exit_list_program,PMF.pure_bind,PMF.pure_bind]
  exact actual_node_list_filtered_law N R gamma common r _ _ keep _
    (actual_original_exit_batch_nodes_within N C b s keep edges hs)

/-- Before the derived first join, every ending original arm node is genuinely
ordinary and nonroot. This is obtained from CutChild routes and strict ages. -/
theorem actual_intermediate_ending_nodes_ordinary (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : ParentCalendar.IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hcut : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) < C.age (firstParentJoin N C H he)) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    ∀ v ∈ endingNodes N C (nextParentCut N C H he hl hu)
      (occupiedParentEdges N C H he hl hu), N.graph.inDegree v = 1 := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  intro v hv
  obtain ⟨e,hem,hsrc⟩ := Finset.mem_image.mp hv
  have hedges := (Finset.mem_filter.mp hem).1
  have ha := (Finset.mem_filter.mp hem).2
  obtain ⟨bit,_,hpos⟩ := Finset.mem_image.mp hedges
  have hroute := (ParentCalendar.parentPosition_spec C H he hl hu bit).1
  rw [hpos] at hroute
  have hh := actual_parent_route_sources_nonhybrid N hc H he bit hroute
  have hroot : N.graph.source e ≠ N.root := by
    intro hr
    have hle := C.age_le_of_directed (N.rooted (firstParentJoin N C H he))
    rw [hr] at ha
    have hrootlt : C.age N.root < C.age (firstParentJoin N C H he) := by
      rw [ha]
      exact hcut
    exact (not_lt_of_ge hle) hrootlt
  rw [← hsrc]
  exact N.indegree_one_of_nonroot_nonhybrid _ hroot hh

/-- Focal pulse in the true initialized larger source, BEFORE h's node batch.
Only the selected descendants are at h; the full outside source is unrestricted.
The right row uses R.parents hy, exactly the original registry orientation. -/
theorem actual_initialized_focal_node_batch_law (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (hy : Hybrid N)
    (sample : Copy → X) (register : V → Bool) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (s : Code N sample)
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age hy.val))
      (initialCode N sample register)).support)
    (keep : Finset Copy)
    (hkeep : ∀ x ∈ keep, N.graph.DReach hy.val (N.leaf (sample x))) :
    (sourceProgram N r (nodeOperations N C R gamma common (C.age hy.val)) s).map (projection N keep) =
      if common hy then
        PMF.pure (projection N keep (pulseCode (R.parents hy) s
          (fun _ => (state s).register hy.val)))
      else (currentCoinPMF (AtNode (state s) (R.parents hy).hybrid) (gamma hy)).map
        (fun coin => projection N keep (pulseCode (R.parents hy) s coin)) := by
  have hr : hy.val ≠ N.root := by
    intro h
    have hdeg := hy.property.1
    rw [h,N.root_degrees.1] at hdeg
    omega
  have hpanel : AtNodePanel (state s) keep hy.val := by
    intro x hx
    have hout := actual_initialized_hybrid_descendant_frontier N hc C (R.parents hy)
      sample register R gamma common r (by simpa only [R.original_site] using hs) x
      (by simpa only [R.original_site] using hkeep x hx)
    simpa only [R.original_site] using hout
  have hmem : hy.val ∈ (Finset.univ.filter (fun v : V => C.age v = C.age hy.val)).toList := by
    simp
  have hbatch := actual_original_node_list_binding N R gamma common r _ hy.val hr hmem s keep hpanel
  change (sourceProgram N r (nodeOperations N C R gamma common (C.age hy.val)) s).map
      (projection N keep) = _ at hbatch
  rw [hbatch]
  have hhy : (⟨hy.val,hy.property⟩ : Hybrid N) = hy := rfl
  cases hm : common hy <;>
    simp [originalNodeOperation,hr,hy.property,hhy,hm,boundaryKernel,independentPulseKernel,
      PMF.pure_map,PMF.map_comp,Function.comp_def,R.original_site]

/-- One complete ACTUAL parent-path step: all interleaved original dates in
its open slice, all exits at the derived next cut, then the original mixed node
batch. Its selected full law equals one actual time row followed by the
physically relevant original boundary sublist. This does not assume a next
arm-position/frontier identity or a complete grouped-word law. -/
theorem actual_parent_slice_then_boundary_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : ParentCalendar.IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample)
    (hs : AtEdgePanel (state s) keep (occupiedParentEdges N C H he hl hu)) :
    let cut := nextParentCut N C H he hl hu
    let nodes := endingNodes N C cut (occupiedParentEdges N C H he hl hu)
    let vs := (Finset.univ.filter (fun v : V => C.age v = cut)).toList
    let batch := (originalExits N C cut).map (fun e => .boundary (.exit e)) ++
      nodeListProgram N R gamma common (vs.filter (fun v => decide (v ∈ nodes)))
    (sourceProgram N r
      (parentPairSliceProgram N C R gamma common H he hl hu ++
        boundaryOperations N C R gamma common cut) s).map (projection N keep) =
      (sourceTimeKernel N r (Real.toNNReal (cut-t)) s).bind
        (fun d => (sourceProgram N r batch d).map (projection N keep)) := by
  let cut := nextParentCut N C H he hl hu
  let nodes := endingNodes N C cut (occupiedParentEdges N C H he hl hu)
  let vs := (Finset.univ.filter (fun v : V => C.age v = cut)).toList
  let batch := (originalExits N C cut).map (fun e => ProgramStep.boundary (.exit e)) ++
    nodeListProgram N R gamma common (vs.filter (fun v => decide (v ∈ nodes)))
  let slice := parentPairSliceProgram N C R gamma common H he hl hu
  let wholeBatch := boundaryOperations N C R gamma common cut
  change (sourceProgram N r (slice ++ wholeBatch) s).map (projection N keep) =
    (sourceTimeKernel N r (Real.toNNReal (cut-t)) s).bind
      (fun d => (sourceProgram N r batch d).map (projection N keep))
  calc
    _ = (sourceProgram N r slice s).bind
        (fun d => (sourceProgram N r wholeBatch d).map (projection N keep)) := by
      rw [sourceProgram_append,PMF.map_bind]
    _ = ((sourceProgram N r slice s).map (projection N keep)).bind
        (selectedProgram N r keep wholeBatch) := by
      simp_rw [actual_source_program_projection]
      rw [PMF.bind_map]
      rfl
    _ = ((sourceTimeKernel N r (Real.toNNReal (cut-t)) s).map (projection N keep)).bind
        (selectedProgram N r keep wholeBatch) := by
      rw [actual_parent_pair_slice_source_row N C R gamma common H he hl hu r keep s hs]
    _ = (sourceTimeKernel N r (Real.toNNReal (cut-t)) s).bind
        (fun d => (sourceProgram N r wholeBatch d).map (projection N keep)) := by
      rw [PMF.bind_map]
      simp_rw [actual_source_program_projection]
      rfl
    _ = _ := by
      apply bind_eq_of_eq_on_support
      intro d hd
      exact actual_original_mixed_boundary_filtered_law N C R gamma common r cut d keep
        (occupiedParentEdges N C H he hl hu)
        (actual_time_edge_panel N r (Real.toNNReal (cut-t)) s keep
          (occupiedParentEdges N C H he hl hu) hs hd)

end CloudG3.MixedParentBoundary
