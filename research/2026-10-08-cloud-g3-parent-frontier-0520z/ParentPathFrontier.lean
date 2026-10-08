import MixedParentBoundary
import G1OriginalComponentNodeIdentity

/-!
Cloud G3 literal original parent-path successor and actual boundary frontier.
2026-10-08. SOURCE prototype, compiler UNCHECKED. No graph-to-word coverage,
desired law, outside independence or pathwise scalar indicator is a premise.
Each edge is an actual original ID; COMMON retains the SAME original register.
Whole-arm operator grouping is a separate hand consumer in this packet.
-/
namespace CloudG3.ParentPathFrontier
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open G1OriginalNodeBatchBinding G1OriginalExitBatchBinding G1OriginalComponentNodeIdentity
open G1OriginalEpochPanelSilence G1OriginalEpochPanelCompression G1ActualJointProgram
open G1OriginalCalendarDecomposition G1CanonicalComponentSegment
open G1InitializedFrontierPrefix G1CutChildPorts G1CanonicalThreeEpochList
open CloudG3.GroupedParentPathCalendar CloudG3.FirstParentJoin CloudG3.MixedParentBoundary
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- A nontrivial literal original directed path has an edge into its end. -/
theorem path_end_is_target {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) (hab : a ≠ b) : ∃ e ∈ es, G.target e = b := by
  induction p with
  | nil => exact False.elim (hab rfl)
  | @cons a b e es hs rest ih =>
      by_cases he : G.target e = b
      · exact ⟨e,List.mem_cons_self,he⟩
      · obtain ⟨f,hf,hft⟩ := ih he
        exact ⟨f,List.mem_cons_of_mem e hf,hft⟩

/-- At an internal listed original source, the older literal path prefix gives
an actual incoming edge active at that EXACT vertex date. -/
theorem path_incoming_at_listed_source {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (he : e ∈ es) (hne : a ≠ G.source e) :
    ∃ f ∈ es, G.target f = G.source e ∧ C.Active (C.age (G.source e)) f := by
  obtain ⟨pre,post,heq,hpre,_⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge p he
  obtain ⟨f,hf,ht⟩ := path_end_is_target hpre hne
  refine ⟨f,?_,ht,?_,?_⟩
  · rw [heq]
    exact List.mem_append.mpr (Or.inl hf)
  · rw [ht]
  · simpa only [ht] using C.edge_older f

/-- Original strict chronology forbids two different listed source vertices
at the same age on one literal path. Unrelated vertices may still tie. -/
theorem path_source_eq_of_equal_age {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es) {e f : E}
    (he : e ∈ es) (hf : f ∈ es) (hage : C.age (G.source e) = C.age (G.source f)) :
    G.source e = G.source f := by
  induction p with
  | nil => simp at he
  | @cons a b g gs hs rest ih =>
      rcases List.mem_cons.mp he with heg | he
      · subst e
        rcases List.mem_cons.mp hf with hfg | hf
        · subst f
          rfl
        · have hlt := (rest.source_age_le C hf).trans_lt (C.edge_older g)
          exact False.elim ((ne_of_lt hlt) hage.symm)
      · rcases List.mem_cons.mp hf with hfg | hf
        · subst f
          have hlt := (rest.source_age_le C he).trans_lt (C.edge_older g)
          exact False.elim ((ne_of_lt hlt) hage)
        · exact ih he hf hage

/-- Exact original incoming target at an ending arm node. Both proof bounds
for the next parent position are derived from the actual minimum cut and join. -/
theorem actual_ending_next_position_target (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hcut : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) < C.age (firstParentJoin N C H he))
    (bit : Bool)
    (hend : C.age (N.graph.source (parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit)) =
      nextParentCut N C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2)) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    let b := nextParentCut N C H he hl hu
    let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
    let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
    N.graph.target (parentPosition C H he hlow hup bit) =
      N.graph.source (parentPosition C H he hl hu bit) := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  let b := nextParentCut N C H he hl hu
  let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
  let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
  let e := parentPosition C H he hl hu bit
  have hentry : entry ≠ N.graph.source e := by
    intro hv
    have hlt : C.age (N.graph.source e) < C.age entry := hend.trans_lt hup
    rw [← hv] at hlt
    exact (lt_irrefl _) hlt
  obtain ⟨f,hf,hft,hfa⟩ := path_incoming_at_listed_source C
    (parentRoute_path H he bit) (parentPosition_spec C H he hl hu bit).1 hentry
  have hactive : C.Active b f := by simpa only [hend] using hfa
  have hfeq := (parentRoute_path H he bit).active_unique C hf
    (parentPosition_spec C H he hlow hup bit).1 hactive
    (parentPosition_spec C H he hlow hup bit).2
  simpa only [hfeq] using hft

/-- Nonending original arm stays on exactly the same original edge. -/
theorem actual_nonending_next_position_same (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hcut : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) < C.age (firstParentJoin N C H he))
    (bit : Bool)
    (hend : C.age (N.graph.source (parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit)) ≠
      nextParentCut N C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2)) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    let b := nextParentCut N C H he hl hu
    let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
    let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
    parentPosition C H he hl hu bit = parentPosition C H he hlow hup bit := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  let b := nextParentCut N C H he hl hu
  let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
  let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
  have hle : b ≤ C.age (N.graph.source (parentPosition C H he hl hu bit)) := by
    apply actual_occupied_parent_edges_end_ge_cut N C H he hl hu
    exact Finset.mem_image.mpr ⟨bit,Finset.mem_univ _,rfl⟩
  have hgt : b < C.age (N.graph.source (parentPosition C H he hl hu bit)) :=
    lt_of_le_of_ne hle (Ne.symm hend)
  have htarget := (parentPosition_spec C H he hl hu bit).2.1
  exact (parentRoute_path H he bit).active_unique C
    (parentPosition_spec C H he hl hu bit).1 (parentPosition_spec C H he hlow hup bit).1
    ⟨htarget.trans (actual_next_parent_cut_later N C H he hl hu).le,hgt⟩
    (parentPosition_spec C H he hlow hup bit).2

/-- Every ACTUAL node list leaves a selected copy already on an edge fixed. -/
theorem actual_node_list_copy_keeps_edge (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (vs : List V) (s : Code N sample) (x : Copy) (e : E)
    (hx : copyLocation (state s) x = .edge e) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (nodeListProgram N R gamma common vs) s).support) :
    copyLocation (state d) x = .edge e := by
  induction vs generalizing s with
  | nil =>
      have hds : d = s := by simpa [nodeListProgram,sourceProgram] using hd
      subst d
      exact hx
  | cons v vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N R gamma common v) s).bind
        (sourceProgram N r (nodeListProgram N R gamma common vs))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (actual_node_kernel_keeps_existing_edge N R gamma common v s hm x e hx) hdm

/-- The entire original node list containing a genuine ordinary endpoint sends
that copy to its unique incoming original edge; foreign tied nodes still run. -/
theorem actual_node_list_copy_ordinary_entry (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (vs : List V) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) (hmem : N.graph.target e ∈ vs)
    (s : Code N sample) (x : Copy) (hx : copyLocation (state s) x = .node (N.graph.target e))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (nodeListProgram N R gamma common vs) s).support) :
    copyLocation (state d) x = .edge e := by
  induction vs generalizing s with
  | nil => exact False.elim (List.not_mem_nil hmem)
  | cons v vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N R gamma common v) s).bind
        (sourceProgram N r (nodeListProgram N R gamma common vs))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      by_cases hv : v = N.graph.target e
      · subst v
        rw [actual_original_ordinary_edge_identity N R gamma common e degree] at hm
        have hms : m = ordinaryCode N s e := by simpa [boundaryKernel] using hm
        subst m
        have hnew : copyLocation (state (ordinaryCode N s e)) x = .edge e := by
          rw [ordinaryCode_copyLocation]
          simp [ordinaryLocation,hx]
        exact actual_node_list_copy_keeps_edge N R gamma common r vs _ x e hnew hdm
      · have htail : N.graph.target e ∈ vs := (List.mem_cons.mp hmem).resolve_left (Ne.symm hv)
        have hmove := actual_original_node_kernel_movement N R gamma common v s hm x
        unfold NodeMovement at hmove
        have hn : copyLocation (state s) x ≠ .node v := by
          rw [hx]
          intro h
          exact hv (Location.node.inj h).symm
        rw [if_neg hn] at hmove
        exact ih htail m (hmove.trans hx) hdm

/-- The COMPLETE actual exit-then-node boundary places each selected arm copy
on the constructed next original route edge. No frontier identity is assumed. -/
theorem actual_complete_parent_boundary_position (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hcut : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (x : Copy) (bit : Bool)
    (hx : copyLocation (state s) x = .edge (parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C R gamma common
      (nextParentCut N C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2))) s).support) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
    let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
    copyLocation (state d) x = .edge (parentPosition C H he hlow hup bit) := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  let b := nextParentCut N C H he hl hu
  let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
  let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
  let old := parentPosition C H he hl hu bit
  let new := parentPosition C H he hlow hup bit
  let vs := (Finset.univ.filter (fun v : V => C.age v = b)).toList
  change d ∈ (sourceProgram N r
    ((originalExits N C b).map (fun e => .boundary (.exit e)) ++
      nodeListProgram N R gamma common vs) s).support at hd
  rw [sourceProgram_append,actual_exit_list_program,PMF.pure_bind] at hd
  have hpost : copyLocation (state (exitCodeList N (originalExits N C b) s)) x =
      if C.age (N.graph.source old) = b then .node (N.graph.source old) else .edge old := by
    rw [actual_exit_list_copy_location,hx,actual_original_exit_list_edge_position]
  by_cases hend : C.age (N.graph.source old) = b
  · rw [if_pos hend] at hpost
    have htarget := actual_ending_next_position_target N C H he hl ht hcut bit hend
    have hnode : N.graph.source old ∈ endingNodes N C b (occupiedParentEdges N C H he hl hu) :=
      Finset.mem_image.mpr ⟨old,Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨bit,Finset.mem_univ _,rfl⟩,hend⟩,rfl⟩
    have hdegree := actual_intermediate_ending_nodes_ordinary N hc C H he hl ht hcut _ hnode
    have hdegreeNew : N.graph.inDegree (N.graph.target new) = 1 := by simpa only [htarget] using hdegree
    have hmem : N.graph.target new ∈ vs := by
      apply Finset.mem_toList.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [htarget] using hend⟩
    exact actual_node_list_copy_ordinary_entry N R gamma common r vs new hdegreeNew hmem
      _ x (by simpa only [htarget] using hpost) hd
  · rw [if_neg hend] at hpost
    have hsame := actual_nonending_next_position_same N C H he hl ht hcut bit hend
    have hkeep := actual_node_list_copy_keeps_edge N R gamma common r vs _ x old hpost hd
    simpa only [hsame] using hkeep

/-- Actual support preservation for a literal edge-safe original programme. -/
theorem actual_edge_safe_program_support (N : RootedBinary V E X)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N)) (edges : Finset E)
    (hsafe : ∀ op ∈ ops, EdgeSafeStep N R gamma common edges op)
    (s : Code N sample) (keep : Finset Copy) (hs : AtEdgePanel (state s) keep edges)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    AtEdgePanel (state d) keep edges := by
  induction ops generalizing s with
  | nil =>
      have hds : d = s := by simpa [sourceProgram] using hd
      subst d
      exact hs
  | cons op ops ih =>
      change d ∈ ((sourceProgramStep N r op s).bind (sourceProgram N r ops)).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih (fun p hp => hsafe p (List.mem_cons_of_mem op hp)) m
        (actual_edge_safe_step_support N R gamma common r op edges (hsafe op (by simp)) s keep hs hm) hdm

/-- The actual open slice preserves EACH singleton original arm position on
all true source outcomes, not only the projected PMF after compression. -/
theorem actual_parent_slice_singleton_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (bit : Bool)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep {parentPosition C H he hl hu bit})
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (parentPairSliceProgram N C R gamma common H he hl hu) s).support) :
    AtEdgePanel (state d) keep {parentPosition C H he hl hu bit} := by
  apply actual_edge_safe_program_support N R gamma common r _ _ _ s keep hs hd
  apply actual_stop_tail_edge_safe_of_end_ge N C R gamma common _
    (nextParentCut N C H he hl hu) _ (afterDate N C t) (original_after_ordered N C t)
    (actual_next_parent_cut_is_original_date N C H he hl hu) t
  intro e hem
  have heq : e = parentPosition C H he hl hu bit := by simpa using hem
  subst e
  cases bit
  · exact min_le_left _ _
  · exact min_le_right _ _

noncomputable def oneParentStepProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) : List (ProgramStep N) :=
  parentPairSliceProgram N C R gamma common H he hl hu ++
    boundaryOperations N C R gamma common (nextParentCut N C H he hl hu)

/-- One true open slice AND its complete boundary produce the next physical
arm panel. Original outside operations, ties and supported merges are included. -/
theorem actual_parent_step_next_panel (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hcut : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) < C.age (firstParentJoin N C H he))
    (bit : Bool) {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit})
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (oneParentStepProgram N C R gamma common H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2)) s).support) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    let hlow := hl.trans (actual_next_parent_cut_later N C H he hl hu).le
    let hup := hcut.trans_le (actual_first_join_age_window N C H he).2
    AtEdgePanel (state d) keep {parentPosition C H he hlow hup bit} := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  change d ∈ (sourceProgram N r
    (parentPairSliceProgram N C R gamma common H he hl hu ++
      boundaryOperations N C R gamma common (nextParentCut N C H he hl hu)) s).support at hd
  rw [sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hpanel := actual_parent_slice_singleton_support N C R gamma common H he hl hu bit r s keep hs hm
  intro x hx
  obtain ⟨e,hem,hpop⟩ := hpanel x hx
  have heq : e = parentPosition C H he hl hu bit := by simpa using hem
  subst e
  exact ⟨_,Finset.mem_singleton_self _,
    actual_complete_parent_boundary_position N hc C R gamma common H he hl ht hcut r m x bit hpop hdm⟩

/-- Actual node-list support of an already edge-resident selected panel. -/
theorem actual_node_list_keeps_edge_panel (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (vs : List V) (s : Code N sample)
    (keep : Finset Copy) (edges : Finset E) (hs : AtEdgePanel (state s) keep edges)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (nodeListProgram N R gamma common vs) s).support) :
    AtEdgePanel (state d) keep edges := by
  intro x hx
  obtain ⟨e,he,hpop⟩ := hs x hx
  exact ⟨e,he,actual_node_list_copy_keeps_edge N R gamma common r vs s x e hpop hd⟩

/-- After ALL tied original node operations, a nonroot focal node panel is on
its actual incoming edges. Current-owner hybrid draws are never redrawn later. -/
theorem actual_node_list_enters_incoming_panel (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (vs : List V) (v : V) (hr : v ≠ N.root) (hv : v ∈ vs)
    (s : Code N sample) (keep : Finset Copy) (hs : AtNodePanel (state s) keep v)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (nodeListProgram N R gamma common vs) s).support) :
    AtEdgePanel (state d) keep (incomingEdges N v) := by
  induction vs generalizing s with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons u vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N R gamma common u) s).bind
        (sourceProgram N r (nodeListProgram N R gamma common vs))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      by_cases hu : u = v
      · subst u
        exact actual_node_list_keeps_edge_panel N R gamma common r vs m keep _
          (actual_own_node_enters_edges N R gamma common s keep v hr hs hm) hdm
      · have htail : v ∈ vs := (List.mem_cons.mp hv).resolve_left (Ne.symm hu)
        exact ih htail m (actual_foreign_node_preserves_panel N R gamma common s keep v u hu hs hm) hdm

/-- Exhaustive incoming pair from the ACTUAL degree-two hybrid, with no
parallel-parent or NonrootBigon premise. -/
theorem actual_hybrid_incoming_pair (N : RootedBinary V E X)
    (H : GProgram.G2.OriginalHybridParents N) : incomingEdges N H.hybrid = {H.parent0,H.parent1} := by
  ext e
  simp only [incomingEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro he
    exact edge_pair_exhaustive _ _ _ H.different
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H.target0⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H.target1⟩) H.isHybrid.1 e
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  · rintro (rfl | rfl)
    · exact H.target0
    · exact H.target1

/-- At h's exact original date, the constructed route positions are the
actual registered parent occurrences, even when their older ends differ. -/
theorem actual_parent_position_at_h (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) :
    parentPosition C H he (le_refl (C.age H.hybrid))
      (actual_parent_route_entry_older N C H he) bit = H.parent bit := by
  have hm : H.parent bit ∈ parentRoute H he bit :=
    List.mem_append.mpr (Or.inr (by simp))
  have ha : C.Active (C.age H.hybrid) (H.parent bit) := by
    exact ⟨by rw [original_parent_target H bit],
      by simpa only [original_parent_target H bit] using C.edge_older (H.parent bit)⟩
  exact ((parentRoute_path H he bit).active_unique C hm
    (parentPosition_spec C H he (le_refl _) (actual_parent_route_entry_older N C H he) bit).1
    ha (parentPosition_spec C H he (le_refl _) (actual_parent_route_entry_older N C H he) bit).2).symm

/-- Natural full-source initialized support followed by ALL tied h-date nodes
supplies the real two-arm edge frontier; outside roots stay in the same Code. -/
theorem actual_initialized_after_h_nodes_parent_frontier (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    (r : PositivePairRates E) (s : Code N sample)
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age hy.val))
      (initialCode N sample register)).support)
    (keep : Finset Copy) (hkeep : ∀ x ∈ keep, N.graph.DReach hy.val (N.leaf (sample x)))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (nodeOperations N C R gamma common (C.age hy.val)) s).support) :
    AtEdgePanel (state d) keep (occupiedParentEdges N C (R.parents hy) he
      (le_refl (C.age (R.parents hy).hybrid)) (actual_parent_route_entry_older N C (R.parents hy) he)) := by
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
  let vs := (Finset.univ.filter (fun v : V => C.age v = C.age hy.val)).toList
  have hmem : hy.val ∈ vs := by simp [vs]
  have hin := actual_node_list_enters_incoming_panel N R gamma common r vs hy.val hr hmem s keep hpanel hd
  intro x hx
  obtain ⟨e,hem,hpop⟩ := hin x hx
  have hpair : e = (R.parents hy).parent0 ∨ e = (R.parents hy).parent1 := by
    have hmem' : e ∈ incomingEdges N (R.parents hy).hybrid := by
      simpa only [R.original_site] using hem
    simpa only [actual_hybrid_incoming_pair N (R.parents hy),Finset.mem_insert,Finset.mem_singleton] using hmem'
  refine ⟨e,?_,hpop⟩
  rcases hpair with he0 | he1
  · exact Finset.mem_image.mpr ⟨false,Finset.mem_univ _,by
      simpa [he0,GProgram.G2.OriginalHybridParents.parent]
        using actual_parent_position_at_h N C (R.parents hy) he false⟩
  · exact Finset.mem_image.mpr ⟨true,Finset.mem_univ _,by
      simpa [he1,GProgram.G2.OriginalHybridParents.parent]
        using actual_parent_position_at_h N C (R.parents hy) he true⟩

/-- When the actual next minimum reaches j, BOTH arm edges end at j. This
uses original route chronology and the derived join bound, not a common-source
assumption or a replacement parallel bigon. -/
theorem actual_final_parent_positions_source_join (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hfinal : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) = C.age (firstParentJoin N C H he))
    (bit : Bool) :
    N.graph.source (parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit) = firstParentJoin N C H he := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  have hle := actual_position_source_age_le_join N C H he hl ht bit
  have hge : C.age (firstParentJoin N C H he) ≤
      C.age (N.graph.source (parentPosition C H he hl hu bit)) := by
    rw [← hfinal]
    apply actual_occupied_parent_edges_end_ge_cut N C H he hl hu
    exact Finset.mem_image.mpr ⟨bit,Finset.mem_univ _,rfl⟩
  have hage := le_antisymm hle hge
  have hm : firstParentJoin N C H he ∈ routeSourceVertices N H he bit := by
    cases bit
    · exact (Finset.mem_inter.mp (actual_first_join_spec N C H he).1).1
    · exact (Finset.mem_inter.mp (actual_first_join_spec N C H he).1).2
  obtain ⟨f,hf,hfs⟩ := (route_source_mem_iff N H he bit _).mp hm
  have heq := path_source_eq_of_equal_age C (parentRoute_path H he bit)
    (parentPosition_spec C H he hl hu bit).1 hf (by simpa only [hfs] using hage)
  exact heq.trans hfs

/-- The final COMPLETE original exit batch pools the selected arms at j while
retaining the old forest and register. The join's node batch is not included. -/
theorem actual_final_parent_exit_frontier (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hfinal : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) = C.age (firstParentJoin N C H he))
    {sample : Copy → X} (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep (occupiedParentEdges N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2))) :
    AtNodePanel (state (exitCodeList N (originalExits N C (C.age (firstParentJoin N C H he))) s))
      keep (firstParentJoin N C H he) := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  intro x hx
  obtain ⟨e,hem,hpop⟩ := hs x hx
  obtain ⟨bit,_,hpos⟩ := Finset.mem_image.mp hem
  have hsrc : N.graph.source e = firstParentJoin N C H he := by
    rw [← hpos]
    exact actual_final_parent_positions_source_join N C H he hl ht hfinal bit
  have hhit : e ∈ originalExits N C (C.age (firstParentJoin N C H he)) :=
    (actual_original_exit_mem_iff N C _ e).mpr (by rw [hsrc])
  rw [actual_exit_list_copy_location,hpop,actual_exit_location_list_hit N _ e hhit,hsrc]

end CloudG3.ParentPathFrontier
