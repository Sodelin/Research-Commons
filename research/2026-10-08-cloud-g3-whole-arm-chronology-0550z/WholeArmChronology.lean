import ParentPathFrontier

/-!
Literal ORIGINAL chronological loop and full stopped fork frontier.
Cloud G3, 2026-10-08. Compiler UNCHECKED. No desired grouped kernel, source
coverage or separated-agenda field is supplied. The loop is the unchanged
compiler stopBeforeTail on its actual sorted original dates. Operator grouping
and the exact last-exit separator are hand consumers, separately identified.
-/
namespace CloudG3.WholeArmChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceFiniteProjection
open G1InterleavedEpochCompression G1OriginalEpochRecomposition
open G1OriginalNodeBatchBinding G1OriginalExitBatchBinding G1OriginalEpochPanelSilence
open G1OriginalEpochPanelCompression G1ActualJointProgram G1CanonicalThreeEpochList
open G1CanonicalEpochSpecialization G1InitializedFrontierPrefix G1OriginalCalendarDecomposition
open CloudG3.GroupedParentPathCalendar CloudG3.FirstParentJoin
open CloudG3.MixedParentBoundary CloudG3.ParentPathFrontier
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- The actual sorted ORIGINAL head is strictly later than the current cut. -/
theorem actual_after_head_later (N : RootedBinary V E X) (C : Calendar N.graph)
    (t c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs) : t < c := by
  have hm : c ∈ afterDate N C t := by rw [hdates]; exact List.mem_cons_self
  exact of_decide_eq_true (List.mem_filter.mp hm).2

/-- After processing the actual head date, its literal tail is exactly the
original remaining calendar. It is not a chosen graph-to-word continuation. -/
theorem actual_after_head_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (t c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs) : afterDate N C c = cs := by
  have hl := actual_after_head_later N C t c cs hdates
  have hord := original_after_ordered N C t
  rw [hdates] at hord
  have hfilters := filter_after_filter hl (sortedOriginalDates N C)
  change (afterDate N C t).filter (fun a => decide (c < a)) = afterDate N C c at hfilters
  rw [hdates,filter_after_head (List.pairwise_cons.mp hord).1] at hfilters
  exact hfilters.symm

/-- An actual head cannot cross either current arm's older source endpoint:
that source date is itself in the SAME original sorted calendar. -/
theorem actual_after_head_le_parent_cut (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry)
    (c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs) :
    c ≤ nextParentCut N C H he hl hu := by
  have hord := original_after_ordered N C t
  rw [hdates] at hord
  have hle (bit : Bool) : c ≤ C.age (N.graph.source (parentPosition C H he hl hu bit)) := by
    have hm := original_after_member N C t _ (parentPosition_spec C H he hl hu bit).2.2
    rw [hdates] at hm
    rcases List.mem_cons.mp hm with hm | hm
    · exact le_of_eq hm.symm
    · exact (List.pairwise_cons.mp hord).1 _ hm |>.le
  exact le_min (hle false) (hle true)

/-- Remaining actual fork tail, ending after ALL original join exits and
BEFORE its node batch. This is a programme definition, not a law field. -/
noncomputable def remainingForkTail (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (join : V) (t : ℝ) (dates : List ℝ) : List (ProgramStep N) :=
  stopBeforeTail N C R gamma common (C.age join) t dates ++
    (originalExits N C (C.age join)).map (fun e => .boundary (.exit e))

/-- Exact ORIGINAL chronological recursion, including unrelated dates and ties. -/
theorem actual_remaining_fork_head_split (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (join : V) (t c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs)
    (hc : c < C.age join) :
    remainingForkTail N C R gamma common join t (afterDate N C t) =
      [.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c ++
        remainingForkTail N C R gamma common join c (afterDate N C c) := by
  rw [actual_after_head_tail N C t c cs hdates]
  simp [remainingForkTail,hdates,stopBeforeTail,ne_of_lt hc,List.append_assoc]

/-- Original date-head interval and full boundary retain the actual next arm
panel, whether this head ends an arm or is only an outside date. -/
theorem actual_original_head_next_panel (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs)
    (hcj : c < C.age (firstParentJoin N C H he)) (bit : Bool)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit})
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ([.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c) s).support) :
    let hlc := hl.trans (actual_after_head_later N C t c cs hdates).le
    let huc := hcj.trans_le (actual_first_join_age_window N C H he).2
    AtEdgePanel (state d) keep {parentPosition C H he hlc huc bit} := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  have hct := actual_after_head_later N C t c cs hdates
  have hcutle := actual_after_head_le_parent_cut N C H he hl hu c cs hdates
  by_cases hceq : c = nextParentCut N C H he hl hu
  · have hcut : nextParentCut N C H he hl hu < C.age (firstParentJoin N C H he) := by
      rw [← hceq]
      exact hcj
    have hword : oneParentStepProgram N C R gamma common H he hl hu =
        [.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c := by
      simp [oneParentStepProgram,parentPairSliceProgram,hdates,← hceq,stopBeforeTail]
    have hh := actual_parent_step_next_panel N hc C R gamma common H he hl ht hcut bit r s keep hs
      (by rw [hword]; exact hd)
    simpa only [← hceq] using hh
  · have hstrict : c < nextParentCut N C H he hl hu := lt_of_le_of_ne hcutle hceq
    have hend : c < C.age (N.graph.source (parentPosition C H he hl hu bit)) := by
      apply hstrict.trans_le
      apply actual_occupied_parent_edges_end_ge_cut N C H he hl hu
      exact Finset.mem_image.mpr ⟨bit,Finset.mem_univ _,rfl⟩
    have hsafe : ∀ op ∈ [.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c,
        EdgeSafeStep N R gamma common {parentPosition C H he hl hu bit} op := by
      intro op hop
      rcases List.mem_append.mp hop with hin | hin
      · have ho : op = .interval (Real.toNNReal (c-t)) := by simpa using hin
        exact Or.inl ⟨_,ho⟩
      · exact actual_earlier_boundary_edge_safe_of_end_ge N C R gamma common _
          (C.age (N.graph.source (parentPosition C H he hl hu bit))) c hend
          (by intro e hem; have heq : e = parentPosition C H he hl hu bit := by simpa using hem
              subst e; exact le_refl _) op hin
    have hpanel := actual_edge_safe_program_support N R gamma common r _ _ hsafe s keep hs hd
    have hpos := (parentRoute_path H he bit).active_unique C
      (parentPosition_spec C H he hl hu bit).1
      (parentPosition_spec C H he (hl.trans hct.le)
        (hcj.trans_le (actual_first_join_age_window N C H he).2) bit).1
      ⟨(parentPosition_spec C H he hl hu bit).2.1.trans hct.le,hend⟩
      (parentPosition_spec C H he (hl.trans hct.le)
        (hcj.trans_le (actual_first_join_age_window N C H he).2) bit).2
    simpa only [hpos] using hpanel

/-- Whole literal chronological ORIGINAL tail pools every selected arm panel
at the derived first join. Induction consumes the actual finite date list;
no loop termination, frontier oracle or grouped-law premise is inserted. -/
theorem actual_whole_parent_tail_frontier (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (dates : List ℝ) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hdates : dates = afterDate N C t) (bit : Bool)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit})
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (remainingForkTail N C R gamma common
      (firstParentJoin N C H he) t dates) s).support) :
    AtNodePanel (state d) keep (firstParentJoin N C H he) := by
  induction dates generalizing t s with
  | nil =>
      have hm := original_after_member N C t (firstParentJoin N C H he) ht
      rw [← hdates] at hm
      exact False.elim (List.not_mem_nil hm)
  | cons c cs ih =>
      have hhead : afterDate N C t = c :: cs := hdates.symm
      have hct := actual_after_head_later N C t c cs hhead
      have hm := original_after_member N C t (firstParentJoin N C H he) ht
      rw [hhead] at hm
      have hord := original_after_ordered N C t
      rw [hhead] at hord
      by_cases hfinal : c = C.age (firstParentJoin N C H he)
      · have hcut : nextParentCut N C H he hl
            (ht.trans_le (actual_first_join_age_window N C H he).2) = C.age (firstParentJoin N C H he) := by
          apply le_antisymm (actual_next_parent_cut_le_join N C H he hl ht)
          have hh := actual_after_head_le_parent_cut N C H he hl
            (ht.trans_le (actual_first_join_age_window N C H he).2) c cs hhead
          simpa only [hfinal] using hh
        have hword : remainingForkTail N C R gamma common (firstParentJoin N C H he) t (c :: cs) =
            [.interval (Real.toNNReal (c-t))] ++
              (originalExits N C (C.age (firstParentJoin N C H he))).map (fun e => .boundary (.exit e)) := by
          simp [remainingForkTail,stopBeforeTail,hfinal]
        rw [hword,sourceProgram_append] at hd
        obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        have htime : m ∈ (UnifiedLean.Source.SourcePoissonKernel.sourceTimeKernel N r
            (Real.toNNReal (c-t)) s).support := by simpa [sourceProgram,sourceProgramStep] using hm
        have hpanel := actual_time_edge_panel N r _ s keep _ hs htime
        have hunion : AtEdgePanel (state m) keep (occupiedParentEdges N C H he hl
            (ht.trans_le (actual_first_join_age_window N C H he).2)) := by
          intro x hx
          obtain ⟨e,hem,hpop⟩ := hpanel x hx
          have heq : e = parentPosition C H he hl
              (ht.trans_le (actual_first_join_age_window N C H he).2) bit := by simpa using hem
          exact ⟨e,Finset.mem_image.mpr ⟨bit,Finset.mem_univ _,heq.symm⟩,hpop⟩
        rw [actual_exit_list_program] at hdm
        have hdm' : d = exitCodeList N (originalExits N C (C.age (firstParentJoin N C H he))) m := by
          simpa using hdm
        subst d
        exact actual_final_parent_exit_frontier N C H he hl ht hcut m keep hunion
      · have hcj : c < C.age (firstParentJoin N C H he) :=
          (List.pairwise_cons.mp hord).1 _ ((List.mem_cons.mp hm).resolve_left (Ne.symm hfinal))
        have hword := actual_remaining_fork_head_split N C R gamma common
          (firstParentJoin N C H he) t c cs hhead hcj
        rw [hdates,hword,sourceProgram_append] at hd
        obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        have hpanel := actual_original_head_next_panel N hc C R gamma common H he hl ht
          c cs hhead hcj bit r s keep hs hm
        have htail : cs = afterDate N C c := (actual_after_head_tail N C t c cs hhead).symm
        exact ih (hl.trans hct.le) hcj htail m hpanel hdm

/-- The existing ORIGINAL fork programme is exactly its original initial
node batch followed by the actual finite chronological stopped tail. -/
theorem actual_fork_programme_is_chronological_tail (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (h join : V) :
    forkCalendarProgram N C R gamma common h join =
      G1CanonicalComponentSegment.nodeOperations N C R gamma common (C.age h) ++
        remainingForkTail N C R gamma common join (C.age h) (afterDate N C (C.age h)) := by
  simp only [forkCalendarProgram,canonicalEpochBlock,remainingForkTail,List.append_assoc]

/-- Every copy in the real union of the two arm panels reaches the SAME join.
The argument chooses its actual arm membership, not an artificial entering
product law. The empty selected panel is covered by the universal conclusion. -/
theorem actual_whole_parent_tail_pools_panel (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep (occupiedParentEdges N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2)))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (remainingForkTail N C R gamma common
      (firstParentJoin N C H he) t (afterDate N C t)) s).support) :
    AtNodePanel (state d) keep (firstParentJoin N C H he) := by
  intro x hx
  obtain ⟨e,hem,hpop⟩ := hs x hx
  obtain ⟨bit,_,hpos⟩ := Finset.mem_image.mp hem
  have hsingle : AtEdgePanel (state s) {x} {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit} := by
    intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨e,by simpa only [hpos] using Finset.mem_singleton_self e,hpop⟩
  exact actual_whole_parent_tail_frontier N hc C R gamma common H he
    (afterDate N C t) hl ht rfl bit r s {x} hsingle hd x (Finset.mem_singleton_self x)

/-- The actual natural initialized old forest, followed by the full ORIGINAL
fork (ALL tied initial nodes, every interior date and ALL final exits), has its
selected descendant panel at the derived join. No initialization independence
or desired grouped-kernel equality is supplied. -/
theorem actual_initialized_whole_fork_frontier (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (sample : Copy → X)
    (register : V → Bool) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    (r : PositivePairRates E) (s : Code N sample)
    (hs : s ∈ (sourceProgram N r (actualFrontierProgram N C R gamma common (C.age hy.val))
      (initialCode N sample register)).support)
    (keep : Finset Copy) (hkeep : ∀ x ∈ keep, N.graph.DReach hy.val (N.leaf (sample x)))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (forkCalendarProgram N C R gamma common hy.val
      (firstParentJoin N C (R.parents hy) he)) s).support) :
    AtNodePanel (state d) keep (firstParentJoin N C (R.parents hy) he) := by
  rw [actual_fork_programme_is_chronological_tail,sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hpanel := actual_initialized_after_h_nodes_parent_frontier N hc C sample register
    R gamma common hy he r s hs keep hkeep hm
  have hl := le_refl (C.age (R.parents hy).hybrid)
  have ht := (actual_first_join_age_window N C (R.parents hy) he).1
  have hdm' : d ∈ (sourceProgram N r (remainingForkTail N C R gamma common
      (firstParentJoin N C (R.parents hy) he) (C.age (R.parents hy).hybrid)
      (afterDate N C (C.age (R.parents hy).hybrid))) m).support := by
    simpa only [R.original_site] using hdm
  exact actual_whole_parent_tail_pools_panel N hc C R gamma common (R.parents hy) he
    hl ht r m keep hpanel hdm'

/-- The final full ORIGINAL exit batch has exactly the selected law of the
two real occupied original exits. This removes its selected-silent suffix at
the level of the actual PMF, after the stopped separated word, not by claiming
population separation after the two arms have pooled. Old genealogy and the
SAME copied register are retained by the selected projection. -/
theorem actual_final_parent_exits_selected_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hfinal : nextParentCut N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) = C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep (occupiedParentEdges N C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2))) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    (sourceProgram N r ((originalExits N C (C.age (firstParentJoin N C H he))).map
      (fun e => .boundary (.exit e))) s).map (projection N keep) =
    (sourceProgram N r ([parentPosition C H he hl hu false,parentPosition C H he hl hu true].map
      (fun e => .boundary (.exit e))) s).map (projection N keep) := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  apply actual_complete_exit_batch_inside_law N r _ _ s keep
    (occupiedParentEdges N C H he hl hu) (firstParentJoin N C H he) hs
  · intro e hem
    obtain ⟨bit,_,hpos⟩ := Finset.mem_image.mp hem
    rw [← hpos]
    exact actual_final_parent_positions_source_join N C H he hl ht hfinal bit
  · intro e hem
    obtain ⟨bit,_,hpos⟩ := Finset.mem_image.mp hem
    apply (actual_original_exit_mem_iff N C _ e).mpr
    rw [← hpos,actual_final_parent_positions_source_join N C H he hl ht hfinal bit]
  · intro e hem
    obtain ⟨bit,_,hpos⟩ := Finset.mem_image.mp hem
    cases bit with
    | false => exact List.mem_cons.mpr (Or.inl hpos.symm)
    | true => exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr hpos.symm))

/-- Each ORIGINAL edge's exact clock partition is derived from the unchanged
calendar, including unrelated source dates. This is stronger than a fitted
whole-arm duration and needs no graph-to-word law assumption. -/
theorem actual_edge_clock_partition (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (e : E) :
    OriginalDurationPartition (C.age (N.graph.target e)) (C.age (N.graph.source e))
      (originalIntervalDurations N (stopBeforeTail N C R gamma common
        (C.age (N.graph.source e)) (C.age (N.graph.target e))
        (afterDate N C (C.age (N.graph.target e))))) := by
  apply actual_stop_tail_duration_partition N C R gamma common _
    (original_after_ordered N C _) _ (original_after_member N C _ _ (C.edge_older e))
  intro c hc
  exact (of_decide_eq_true (List.mem_filter.mp hc).2).le

/-- Summing the actual edge clock slices gives precisely its original positive
length. Applied to every disjoint-arm edge, this supplies the coefficient
partition used in the unit Kingman grouping; it does not assert that the
whole fork is a single original edge. -/
theorem actual_edge_clock_sum (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (e : E) :
    (originalIntervalDurations N (stopBeforeTail N C R gamma common
      (C.age (N.graph.source e)) (C.age (N.graph.target e))
      (afterDate N C (C.age (N.graph.target e))))).sum =
        Real.toNNReal (C.age (N.graph.source e)-C.age (N.graph.target e)) := by
  exact actual_original_partition_duration_sum (actual_edge_clock_partition N C R gamma common e)

end CloudG3.WholeArmChronology
