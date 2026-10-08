import ActualHybridEntryCell
import G1UnrankedSingleExitLabel

/-! The derived actual local-cell exit population makes its pooled labelled
forest/SAME-register readout a sufficient ORIGINAL selected future interface.
Actual full calendar/future laws are composed, not assumed as kernel fields.
Cloud G3, 2026-10-08. Compiler UNCHECKED; general graph/menu coverage separate. -/
namespace CloudG3.ActualJoinForestContinuation
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalNodeBatchBinding G1OriginalEpochPanelSilence G1ActualJointProgram
open G1InitializedFrontierPrefix G1CutChildPorts G1UnrankedSourceView G1UnrankedActualFuture
open G1UnrankedSingleExitLabel G1CanonicalThreeEpochList G1OriginalCalendarDecomposition
open CloudG3.FirstParentJoin CloudG3.ParentPathFrontier CloudG3.MixedParentBoundary
open CloudG3.WholeArmChronology CloudG3.ActualHybridEntryCell
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

abbrev ForestRegister (V Copy : Type*) := Finset (UnrankedTree Copy) × (V → Bool)

noncomputable def sourceReadout (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : ForestRegister V Copy :=
  (sourceUnrankedForest (state s) keep,(state s).register)

noncomputable def viewReadout (v : UnrankedView V E Copy) : ForestRegister V Copy :=
  (unrankedViewForest v,v.register)

/-- Literal source support of the WHOLE cell reaches its actual original
first join. ALL tied nodes and all original intermediate/final exits execute;
the proof has no normalized-row or desired endpoint-law hypothesis. -/
theorem actual_entry_cell_exit_panel (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).support) :
    AtNodePanel (state d) keep (firstParentJoin N C (R.parents hy) he) := by
  rw [entryCellProgram,sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  let H := R.parents hy
  have hr : hy.val ≠ N.root := by
    intro h
    have hg := hy.property.1
    rw [h,N.root_degrees.1] at hg
    omega
  let vs := (Finset.univ.filter (fun v : V => C.age v = C.age hy.val)).toList
  have hmem : hy.val ∈ vs := by simp [vs]
  have hnode : AtNodePanel (state s) keep hy.val := by simpa only [H,R.original_site] using hs
  have hin := actual_node_list_enters_incoming_panel N R gamma common r vs hy.val hr hmem s keep hnode hm
  have harmpair : AtEdgePanel (state m) keep {H.parent0,H.parent1} := by
    simpa only [H,← R.original_site hy,actual_hybrid_incoming_pair N (R.parents hy)] using hin
  let a := keep.filter (fun x => copyLocation (state m) x = .edge (H.parent false))
  let b := keep.filter (fun x => copyLocation (state m) x = .edge (H.parent true))
  have hcover : a ∪ b = keep := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (Finset.filter_subset _ keep) (Finset.filter_subset _ keep)
    · intro x hx
      obtain ⟨e,he,hpop⟩ := harmpair x hx
      rcases Finset.mem_insert.mp he with h0 | h1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,by
          simpa [GProgram.G2.OriginalHybridParents.parent,h0] using hpop⟩)
      · have h1' : e = H.parent1 := Finset.mem_singleton.mp h1
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,by
          simpa [GProgram.G2.OriginalHybridParents.parent,h1'] using hpop⟩)
  have hl : C.age H.hybrid ≤ C.age H.hybrid := le_refl _
  have ht : C.age H.hybrid < C.age (firstParentJoin N C H he) :=
    (actual_first_join_age_window N C H he).1
  have h0 : AtEdgePanel (state m) a {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false} := by
    rw [actual_parent_position_at_h]
    intro x hx
    exact ⟨_,Finset.mem_singleton_self _,(Finset.mem_filter.mp hx).2⟩
  have h1 : AtEdgePanel (state m) b {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true} := by
    rw [actual_parent_position_at_h]
    intro x hx
    exact ⟨_,Finset.mem_singleton_self _,(Finset.mem_filter.mp hx).2⟩
  have ha := actual_whole_parent_tail_frontier N hc C R gamma common H he
    (afterDate N C (C.age H.hybrid)) hl ht rfl false r m a h0 hdm
  have hb := actual_whole_parent_tail_frontier N hc C R gamma common H he
    (afterDate N C (C.age H.hybrid)) hl ht rfl true r m b h1 hdm
  intro x hx
  rw [← hcover] at hx
  exact (Finset.mem_union.mp hx).elim (ha x) (hb x)

/-- K plus actual exit population and SAME register determines the full
rooted-unranked ORIGINAL selected causal interface. This is the existing
complete-G1 fibre theorem instantiated at the actual join, not a new field. -/
theorem actual_join_readout_determines_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (join : V) (s z : Code N sample)
    (hs : AtNodePanel (state s) keep join) (hz : AtNodePanel (state z) keep join)
    (h : sourceReadout N keep s = sourceReadout N keep z) :
    unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep) := by
  exact actual_single_exit_unranked_label_view (state s) (state z) s.property.forest z.property.forest
    keep (.node join) (congrArg Prod.fst h) hs hz (congrArg Prod.snd h)

/-- SAME actual future row, with no outside-owner relocation, independence
or desired output-law hypothesis. Only this selected unranked observer. -/
theorem actual_join_future_row_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (join : V) (future : List (ProgramStep N))
    (s z : Code N sample) (hs : AtNodePanel (state s) keep join) (hz : AtNodePanel (state z) keep join)
    (h : sourceReadout N keep s = sourceReadout N keep z) :
    (sourceProgram N r future s).map (sourceReadout N keep) =
      (sourceProgram N r future z).map (sourceReadout N keep) := by
  have hf := actual_unranked_future_row_independent N r keep future s z
    (actual_join_readout_determines_view N keep join s z hs hz h) viewReadout
  simpa only [sourceReadout,viewReadout,sourceUnrankedForest,actual_unranked_view_forest,
    unrankedView,selectedView] using hf

/-- A genuine ACTUAL source continuation row on the admitted join image.
The unsupported branch is only a total readout identity; it is never used
by actual cell support and never supplies a default Code or Copy. -/
noncomputable def joinFutureRaw (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (keep : Finset Copy) (join : V) (future : List (ProgramStep N))
    (q : ForestRegister V Copy) : PMF (ForestRegister V Copy) :=
  if h : ∃ s : Code N sample, AtNodePanel (state s) keep join ∧ sourceReadout N keep s = q then
    (sourceProgram N r future (Classical.choose h)).map (sourceReadout N keep)
    else PMF.pure q

theorem actual_join_future_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (join : V) (future : List (ProgramStep N))
    (s : Code N sample) (hs : AtNodePanel (state s) keep join) :
    (sourceProgram N r future s).map (sourceReadout N keep) =
      joinFutureRaw N sample r keep join future (sourceReadout N keep s) := by
  have h : ∃ z : Code N sample, AtNodePanel (state z) keep join ∧
      sourceReadout N keep z = sourceReadout N keep s := ⟨s,hs,rfl⟩
  rw [joinFutureRaw,dif_pos h]
  exact actual_join_future_row_independent N r keep join future s (Classical.choose h)
    hs (Classical.choose_spec h).1 (Classical.choose_spec h).2.symm

/-- A real cell's normalized input row depends only on the WHOLE old forest
and SAME Γ at its actual hybrid population. The row equality is derived from
the existing actual causal source law, not supplied as an operator field. -/
theorem actual_normalized_entry_row_independent (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (s z : Code N sample)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid)
    (hz : AtNodePanel (state z) keep (R.parents hy).hybrid)
    (h : sourceReadout N keep s = sourceReadout N keep z) :
    normalizedEntryRow N C R gamma common hy he r s keep =
      normalizedEntryRow N C R gamma common hy he r z keep := by
  have hf := actual_join_future_row_independent N r keep (R.parents hy).hybrid
    (entryCellProgram N C R gamma common hy he) s z hs hz h
  change (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).map
      (fun d => (sourceUnrankedForest (state d) keep,(state d).register)) =
    (sourceProgram N r (entryCellProgram N C R gamma common hy he) z).map
      (fun d => (sourceUnrankedForest (state d) keep,(state d).register)) at hf
  rw [actual_hybrid_entry_cell_row N hc C R gamma common hy he r s keep hs,
    actual_hybrid_entry_cell_row N hc C R gamma common hy he r z keep hz] at hf
  exact hf

/-- Concrete normalized cell on the actual hybrid input image. Only the
unsupported readout branch is totalized, without a default source state. -/
noncomputable def cellKernelRaw (N : RootedBinary V E X) (sample : Copy → X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    (r : PositivePairRates E) (keep : Finset Copy) (q : ForestRegister V Copy) : PMF (ForestRegister V Copy) :=
  if h : ∃ s : Code N sample, AtNodePanel (state s) keep (R.parents hy).hybrid ∧ sourceReadout N keep s = q then
    normalizedEntryRow N C R gamma common hy he r (Classical.choose h) keep else PMF.pure q

theorem actual_entry_input_row (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) :
    normalizedEntryRow N C R gamma common hy he r s keep =
      cellKernelRaw N sample C R gamma common hy he r keep (sourceReadout N keep s) := by
  have h : ∃ z : Code N sample, AtNodePanel (state z) keep (R.parents hy).hybrid ∧
      sourceReadout N keep z = sourceReadout N keep s := ⟨s,hs,rfl⟩
  rw [cellKernelRaw,dif_pos h]
  exact actual_normalized_entry_row_independent N hc C R gamma common hy he r keep s (Classical.choose h)
    hs (Classical.choose_spec h).1 (Classical.choose_spec h).2.symm

theorem actual_cell_image_kernel (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) :
    (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).map (sourceReadout N keep) =
      cellKernelRaw N sample C R gamma common hy he r keep (sourceReadout N keep s) :=
  (actual_hybrid_entry_cell_row N hc C R gamma common hy he r s keep hs).trans
    (actual_entry_input_row N hc C R gamma common hy he r s keep hs)

/-- Actual stopped cell followed by ANY original source future. Its complete
old forest/Γ output is sufficient because exit-at-j was derived above. -/
theorem actual_cell_then_future (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) (future : List (ProgramStep N)) :
    (sourceProgram N r (entryCellProgram N C R gamma common hy he ++ future) s).map (sourceReadout N keep) =
      (normalizedEntryRow N C R gamma common hy he r s keep).bind
        (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he) future) := by
  rw [sourceProgram_append,PMF.map_bind]
  calc
    _ = (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).bind
        (fun d => joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he) future
          (sourceReadout N keep d)) := by
      apply bind_eq_of_eq_on_support
      intro d hd
      exact actual_join_future_row N r keep _ future d
        (actual_entry_cell_exit_panel N hc C R gamma common hy he r s keep hs hd)
    _ = ((sourceProgram N r (entryCellProgram N C R gamma common hy he) s).map
        (sourceReadout N keep)).bind
          (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he) future) := by
      rw [PMF.bind_map]
      rfl
    _ = _ := by rw [actual_hybrid_entry_cell_row N hc C R gamma common hy he r s keep hs]

/-- Preserve the actual cell checkpoint JOINTLY with the later forest/Γ.
The bind is conditional source continuation, never a product of cells. -/
theorem actual_cell_joint_checkpoint_future (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) (future : List (ProgramStep N)) :
    (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).bind
      (fun d => ((sourceProgram N r future d).map (sourceReadout N keep)).map
        (fun q => (sourceReadout N keep d,q))) =
      (normalizedEntryRow N C R gamma common hy he r s keep).bind
        (fun p => (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he) future p).map
          (fun q => (p,q))) := by
  calc
    _ = (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).bind
        (fun d => (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he) future
          (sourceReadout N keep d)).map (fun q => (sourceReadout N keep d,q))) := by
      apply bind_eq_of_eq_on_support
      intro d hd
      rw [actual_join_future_row N r keep _ future d
        (actual_entry_cell_exit_panel N hc C R gamma common hy he r s keep hs hd)]
    _ = ((sourceProgram N r (entryCellProgram N C R gamma common hy he) s).map
        (sourceReadout N keep)).bind
        (fun p => (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he) future p).map
          (fun q => (p,q))) := by
      rw [PMF.bind_map]
      rfl
    _ = _ := by rw [actual_hybrid_entry_cell_row N hc C R gamma common hy he r s keep hs]

/-- The literal source future starts after the already-processed join exits,
so its tied join nodes execute exactly once. All later original dates remain. -/
noncomputable def joinCalendarFuture (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (join : V) : List (ProgramStep N) :=
  nodeOperations N C R gamma common (C.age join) ++
    calendarTail N C R gamma common (C.age join) (afterDate N C (C.age join))

/-- EXACT unchanged compiler list split. The real date membership/order and
inherited original calendar-tail cut are used, not a coverage/law field. -/
theorem actual_full_calendar_entry_cell_decomposition (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid) :
    compiledCalendarProgram N C R gamma common =
      actualFrontierProgram N C R gamma common (C.age hy.val) ++
        entryCellProgram N C R gamma common hy he ++
        joinCalendarFuture N C R gamma common (firstParentJoin N C (R.parents hy) he) := by
  let H := R.parents hy
  let j := firstParentJoin N C H he
  have hstart := actual_compiled_calendar_date_cut N C R gamma common (C.age hy.val)
    (original_date_scheduled N C hy.val)
  have hage : C.age hy.val = C.age H.hybrid := by simp only [H,R.original_site]
  rw [hage] at hstart
  have hj : C.age H.hybrid < C.age j := (actual_first_join_age_window N C H he).1
  have hm := original_after_member N C (C.age H.hybrid) j hj
  have hmiddle := actual_calendar_tail_cut N C R gamma common (afterDate N C (C.age H.hybrid))
    (original_after_ordered N C (C.age H.hybrid)) (C.age j) hm (C.age H.hybrid)
  have hfilters := filter_after_filter hj (sortedOriginalDates N C)
  change (afterDate N C (C.age H.hybrid)).filter (fun c => decide (C.age j < c)) =
    afterDate N C (C.age j) at hfilters
  change compiledCalendarProgram N C R gamma common =
    beforeBoundaryProgram N C R gamma common (C.age H.hybrid) ++
      boundaryOperations N C R gamma common (C.age H.hybrid) ++
        calendarTail N C R gamma common (C.age H.hybrid) (afterDate N C (C.age H.hybrid)) at hstart
  rw [hstart,hmiddle,hfilters]
  have hbatch (a : ℝ) : boundaryOperations N C R gamma common a =
      (originalExits N C a).map (fun e => .boundary (.exit e)) ++ nodeOperations N C R gamma common a := rfl
  simp only [actualFrontierProgram,entryCellProgram,remainingForkTail,joinCalendarFuture,hbatch,
    H,j,R.original_site,originalExits,List.append_assoc]

/-- Whole finite compiled ACTUAL original calendar law, with one normalized
cell and the SAME remaining original source row. Initialization supplies its
node panel on support; the fixed-register old-source correlations survive.
Unbounded ancestral completion is a separate consumer. -/
theorem actual_full_calendar_cell_continuation (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    (r : PositivePairRates E) (keep : Finset Copy)
    (hkeep : ∀ x ∈ keep, N.graph.DReach hy.val (N.leaf (sample x))) :
    (sourceProgram N r (compiledCalendarProgram N C R gamma common) (initialCode N sample register)).map
      (sourceReadout N keep) =
      (sourceProgram N r (actualFrontierProgram N C R gamma common (C.age hy.val))
        (initialCode N sample register)).bind (fun s =>
          (normalizedEntryRow N C R gamma common hy he r s keep).bind
            (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he)
              (joinCalendarFuture N C R gamma common (firstParentJoin N C (R.parents hy) he)))) := by
  rw [actual_full_calendar_entry_cell_decomposition N C R gamma common hy he]
  rw [List.append_assoc]
  rw [sourceProgram_append,PMF.map_bind]
  apply bind_eq_of_eq_on_support
  intro s hs
  have hnode : AtNodePanel (state s) keep (R.parents hy).hybrid := by
    intro x hx
    exact actual_initialized_hybrid_descendant_frontier N hc C (R.parents hy) sample register R gamma common r
      (by simpa only [R.original_site] using hs) x (by simpa only [R.original_site] using hkeep x hx)
  exact actual_cell_then_future N hc C R gamma common hy he r s keep hnode _

/-- Real initialized input forest law, the derived normalized cell, then
the SAME actual calendar remainder. Full pre-cell source correlations are
compressed only by the PROVED causal-interface equality above. -/
theorem actual_full_calendar_forest_kernel_composition (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    (r : PositivePairRates E) (keep : Finset Copy)
    (hkeep : ∀ x ∈ keep, N.graph.DReach hy.val (N.leaf (sample x))) :
    (sourceProgram N r (compiledCalendarProgram N C R gamma common) (initialCode N sample register)).map
      (sourceReadout N keep) =
      ((sourceProgram N r (actualFrontierProgram N C R gamma common (C.age hy.val))
        (initialCode N sample register)).map (sourceReadout N keep)).bind (fun p =>
          (cellKernelRaw N sample C R gamma common hy he r keep p).bind
            (joinFutureRaw N sample r keep (firstParentJoin N C (R.parents hy) he)
              (joinCalendarFuture N C R gamma common (firstParentJoin N C (R.parents hy) he)))) := by
  rw [actual_full_calendar_cell_continuation N hc C sample register R gamma common hy he r keep hkeep,
    PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro s hs
  have hnode : AtNodePanel (state s) keep (R.parents hy).hybrid := by
    intro x hx
    exact actual_initialized_hybrid_descendant_frontier N hc C (R.parents hy) sample register R gamma common r
      (by simpa only [R.original_site] using hs) x (by simpa only [R.original_site] using hkeep x hx)
  rw [actual_entry_input_row N hc C R gamma common hy he r s keep hnode]

end CloudG3.ActualJoinForestContinuation
