import UnitArmSemigroup

/-! Concrete original chronological arm rows compose into ONE common
normalized unit operator at their derived physical exposure. Cloud G3,
2026-10-08; compiler UNCHECKED. General graph-to-word coverage is separate. -/
namespace CloudG3.ActualStoppedArmExposure
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalEpochPanelSilence G1OriginalCalendarDecomposition G1ActualJointProgram
open G1ActualJointOpaqueContext G1UnrankedActualFuture
open CloudG3.GroupedParentPathCalendar CloudG3.FirstParentJoin CloudG3.WholeArmChronology
open CloudG3.StoppedArmOperators CloudG3.UnitArmGenerator CloudG3.ClosedArmCarrier
open CloudG3.ActualFixedEdgeRow CloudG3.UnitArmSemigroup
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

abbrev RawForestRegister (V Copy : Type*) := (Copy → Option (UnrankedTree Copy)) × (V → Bool)

/-- Total readout extension ONLY. The unsupported branch is identity on raw
readouts and is never used by an actual singleton-edge source outcome. It is
not an admitted source Code, new input law or default Copy. -/
noncomputable def unitRaw (N : RootedBinary V E X) (sample : Copy → X)
    (keep : Finset Copy) (t : ℝ≥0) (q : RawForestRegister V Copy) : PMF (RawForestRegister V Copy) :=
  if h : ∃ s : SingleEdgeCode N sample keep,
      forestRegister (selectedView (state s.val) keep) = q then
    (unitTimeKernel N (sample := sample) keep t ⟨q,h⟩).map Subtype.val else PMF.pure q

lemma unit_raw_at_member (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (t : ℝ≥0) (x : ArmForestIndex N sample keep) :
    unitRaw N sample keep t x.val = (unitTimeKernel N (sample := sample) keep t x).map Subtype.val := by
  simp only [unitRaw,dif_pos x.property]

lemma unit_raw_bind (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (a b : ℝ≥0) (x : ArmForestIndex N sample keep) :
    (unitRaw N sample keep a x.val).bind (unitRaw N sample keep b) = unitRaw N sample keep (a+b) x.val := by
  rw [unit_raw_at_member,PMF.bind_map]
  simp_rw [unit_raw_at_member]
  rw [← PMF.map_bind,unit_time_bind]

lemma actual_original_interval_raw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (e : E) (t : ℝ≥0)
    (s : Code N sample) (hs : AtEdgePanel (state s) keep {e}) :
    (sourceTimeKernel N r t s).map (fun d => forestRegister (selectedView (state d) keep)) =
      unitRaw N sample keep (rateExposure r e t) (forestRegister (selectedView (state s) keep)) := by
  exact (actual_original_edge_exposure N (sample := sample) r keep e t s hs).trans
    (unit_raw_at_member N (sample := sample) keep (rateExposure r e t) (edgeForestProjection N (sample := sample) keep e ⟨s,hs⟩)).symm

lemma actual_boundary_raw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (bs : List (BoundaryOperation N)) (s : Code N sample)
    (keep : Finset Copy) :
    (sourceProgram N r (bs.map ProgramStep.boundary) s).map
      (fun d => forestRegister (selectedView (state d) keep)) =
        PMF.pure (forestRegister (selectedView (state s) keep)) := by
  calc
    _ = (sourceProgram N r (bs.map ProgramStep.boundary) s).map
        (fun _ => forestRegister (selectedView (state s) keep)) := by
      apply map_eq_of_eq_on_support
      intro d hd
      have h := actual_boundary_word_genealogy_register N r bs s keep hd
      unfold forestRegister
      rw [h.1,h.2]
    _ = _ := PMF.map_const _ _

lemma actual_complete_boundary_raw (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (c : ℝ) (s : Code N sample) (keep : Finset Copy) :
    (sourceProgram N r (boundaryOperations N C R gamma common c) s).map
      (fun d => forestRegister (selectedView (state d) keep)) =
        PMF.pure (forestRegister (selectedView (state s) keep)) := by
  have hbs : boundaryOperations N C R gamma common c =
      ((originalExits N C c).map BoundaryOperation.exit ++
       ((Finset.univ.filter (fun v : V => C.age v = c)).toList.map
         (originalNodeOperation N R gamma common))).map ProgramStep.boundary := by
    simp only [boundaryOperations,originalExits,List.map_append,List.map_map,Function.comp_def]
  rw [hbs]
  exact actual_boundary_raw N (sample := sample) r _ s keep

/-- Actual full chronological head block, including every outside/tied node,
is its physical interval unit row for this instantaneous old-forest observer. -/
lemma actual_head_block_raw (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (t c : ℝ) (s : Code N sample)
    (keep : Finset Copy) (e : E) (hs : AtEdgePanel (state s) keep {e}) :
    (sourceProgram N r ([.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c) s).map
      (fun d => forestRegister (selectedView (state d) keep)) =
        unitRaw N sample keep (rateExposure r e (Real.toNNReal (c-t)))
          (forestRegister (selectedView (state s) keep)) := by
  rw [sourceProgram_append,PMF.map_bind]
  simp_rw [actual_complete_boundary_raw N (sample := sample) C R gamma common r c]
  rw [PMF.bind_pure_comp]
  simpa only [sourceProgram,sourceProgramStep,PMF.bind_pure] using
    actual_original_interval_raw N (sample := sample) r keep e (Real.toNNReal (c-t)) s hs

/-- Total edge reader outside the actual before-join phase uses the existing
original H parent. Actual applications prove the first branch and never use
that fallback as a relocated source or a coverage premise. -/
noncomputable def chronologicalParentEdge (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) (t : ℝ) : E :=
  if h : C.age H.hybrid ≤ t ∧ t < C.age (firstParentJoin N C H he) then
    parentPosition C H he h.1 (h.2.trans_le (actual_first_join_age_window N C H he).2) bit
  else H.parent bit

lemma actual_chronological_parent_edge (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he)) :
    chronologicalParentEdge N C H he bit t =
      parentPosition C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2) bit := by
  simp only [chronologicalParentEdge,dif_pos ⟨hl,ht⟩]

/-- Derived original rate × actual date-slice duration; no free hazard field. -/
noncomputable def sliceExposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (r : PositivePairRates E) (bit : Bool) (t c : ℝ) : ℝ≥0 :=
  rateExposure r (chronologicalParentEdge N C H he bit t) (Real.toNNReal (c-t))

/-- Exact clock sum over the ACTUAL literal stopped original date recursion. -/
noncomputable def stoppedExposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (r : PositivePairRates E) (bit : Bool) :
    ℝ → List ℝ → ℝ≥0
  | _,[] => 0
  | t,c::cs => if c = C.age (firstParentJoin N C H he) then sliceExposure N C H he r bit t c
      else sliceExposure N C H he r bit t c + stoppedExposure N C H he r bit c cs

/-- ONE normalized same common unit operator for the ENTIRE actual stopped
arm. Each successor premise is DERIVED from the original chronological
frontier; no desired row law, generator field or graph-to-word coverage. -/
theorem actual_stopped_single_arm_exposure (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (dates : List ℝ) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hdates : dates = afterDate N C t) (bit : Bool)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit}) :
    (sourceProgram N r (stopBeforeTail N C R gamma common
      (C.age (firstParentJoin N C H he)) t dates) s).map
      (fun d => forestRegister (selectedView (state d) keep)) =
        unitRaw N sample keep (stoppedExposure N C H he r bit t dates)
          (forestRegister (selectedView (state s) keep)) := by
  induction dates generalizing t s with
  | nil =>
      have hm := original_after_member N C t (firstParentJoin N C H he) ht
      rw [← hdates] at hm
      exact False.elim (List.not_mem_nil hm)
  | cons c cs ih =>
      have hhead : afterDate N C t = c::cs := hdates.symm
      have hord := original_after_ordered N C t
      rw [hhead] at hord
      have hm := original_after_member N C t (firstParentJoin N C H he) ht
      rw [hhead] at hm
      have hpos := actual_chronological_parent_edge N C H he bit hl ht
      by_cases hfinal : c = C.age (firstParentJoin N C H he)
      · have hh := actual_original_interval_raw N (sample := sample) r keep _ (Real.toNNReal (c-t)) s hs
        simpa only [stopBeforeTail,if_pos hfinal,sourceProgram,sourceProgramStep,
          PMF.bind_pure,stoppedExposure,if_pos hfinal,sliceExposure,hpos] using hh
      · have hcj : c < C.age (firstParentJoin N C H he) :=
          (List.pairwise_cons.mp hord).1 _ ((List.mem_cons.mp hm).resolve_left (Ne.symm hfinal))
        have hct := actual_after_head_later N C t c cs hhead
        let xs := [.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c
        let a := sliceExposure N C H he r bit t c
        let b := stoppedExposure N C H he r bit c cs
        have hword : stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (c::cs) =
            xs ++ stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) c cs := by
          simp only [xs,stopBeforeTail,if_neg hfinal,List.append_assoc]
        rw [hword,sourceProgram_append,PMF.map_bind]
        have htail : ∀ m ∈ (sourceProgram N r xs s).support,
            (sourceProgram N r (stopBeforeTail N C R gamma common
              (C.age (firstParentJoin N C H he)) c cs) m).map
                (fun d => forestRegister (selectedView (state d) keep)) =
                  unitRaw N sample keep b (forestRegister (selectedView (state m) keep)) := by
          intro m hms
          have hnext := actual_original_head_next_panel N hc C R gamma common H he hl ht
            c cs hhead hcj bit r s keep hs hms
          exact ih (hl.trans hct.le) hcj (actual_after_head_tail N C t c cs hhead).symm m hnext
        calc
          _ = (sourceProgram N r xs s).bind
              (fun m => unitRaw N sample keep b (forestRegister (selectedView (state m) keep))) :=
            bind_eq_of_eq_on_support _ _ _ htail
          _ = ((sourceProgram N r xs s).map
              (fun m => forestRegister (selectedView (state m) keep))).bind (unitRaw N sample keep b) := by
            rw [PMF.bind_map]
            rfl
          _ = (unitRaw N sample keep a (forestRegister (selectedView (state s) keep))).bind (unitRaw N sample keep b) := by
            have hh := actual_head_block_raw N (sample := sample) C R gamma common r t c s keep _ hs
            simpa only [xs,a,sliceExposure,hpos] using congrArg (fun law => law.bind (unitRaw N sample keep b)) hh
          _ = unitRaw N sample keep (a+b) (forestRegister (selectedView (state s) keep)) :=
            unit_raw_bind N (sample := sample) keep a b (edgeForestProjection N (sample := sample) keep _ ⟨s,hs⟩)
          _ = _ := by simp only [stoppedExposure,if_neg hfinal,a,b]

/-- Actual selectedProgram factor is the same full normalized exposure row.
This wrapper uses the PROVED actual source projection, not a fitted row. -/
theorem actual_stopped_selected_arm_row (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he)) (bit : Bool)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit}) :
    let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
    (selectedProgram N r keep ops (projection N keep s)).map (fun v => forestRegister v.val) =
      unitRaw N sample keep (stoppedExposure N C H he r bit t (afterDate N C t))
        (forestRegister (selectedView (state s) keep)) := by
  let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
  have hp := congrArg (fun law : PMF (SelectedIndex N sample keep) =>
      law.map (fun v => forestRegister v.val)) (actual_source_program_projection N r keep ops s)
  simp only [PMF.map_comp,projection,Function.comp_def] at hp
  exact hp.symm.trans (actual_stopped_single_arm_exposure N (sample := sample) hc C R gamma common H he
    (afterDate N C t) hl ht rfl bit r s keep hs)

noncomputable def rawForest (q : RawForestRegister V Copy) : Finset (UnrankedTree Copy) :=
  Finset.univ.biUnion (fun x => match q.1 x with | none => ∅ | some t => {t})

lemma raw_forest_of_view (v : SelectedView V E Copy) :
    rawForest (forestRegister v) = unrankedForest v := by
  rw [actual_unranked_view_forest]
  rfl

noncomputable def rawPool (q : RawForestRegister V Copy × RawForestRegister V Copy) :=
  (rawForest q.1 ∪ rawForest q.2,q.1.2)

lemma pooled_raw (v : SelectedView V E Copy × SelectedView V E Copy) :
    pooledArmReadout v = rawPool (forestRegister v.1,forestRegister v.2) := by
  simp only [rawPool,raw_forest_of_view,pooledArmReadout,forestRegister]

/-- Full actual stopped original two-arm operator, then genuine final exits:
each factor is ONE normalized common unit operator at its DERIVED chronological
exposure. Old physical union forest and SAME Γ are retained. No absolute-age
law or general graph-to-word coverage is asserted. -/
theorem actual_parent_normalized_exposure_operator (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    (sourceProgram N r (remainingForkTail N C R gamma common (firstParentJoin N C H he)
      t (afterDate N C t)) s).map (fun d =>
        (sourceUnrankedForest (state d) (inside ∪ outside),(state d).register)) =
      (independentProduct
        (unitRaw N sample inside (stoppedExposure N C H he r false t (afterDate N C t))
          (forestRegister (selectedView (state s) inside)))
        (unitRaw N sample outside (stoppedExposure N C H he r true t (afterDate N C t))
          (forestRegister (selectedView (state s) outside)))).map rawPool := by
  rw [actual_parent_whole_selected_operator N hc C R gamma common H he hl ht r s inside outside h0 h1]
  let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
  let p := selectedProgram N r inside ops (projection N inside s)
  let q := selectedProgram N r outside ops (projection N outside s)
  have hmap := congrArg (fun law => law.map rawPool)
    (independentProduct_map p q (fun v => forestRegister v.val) (fun v => forestRegister v.val))
  simp only [PMF.map_comp,Function.comp_def,← pooled_raw] at hmap
  calc
    _ = (independentProduct (p.map (fun v => forestRegister v.val))
        (q.map (fun v => forestRegister v.val))).map rawPool := hmap
    _ = _ := by
      rw [actual_stopped_selected_arm_row N (sample := sample) hc C R gamma common H he hl ht false r s inside h0,
        actual_stopped_selected_arm_row N (sample := sample) hc C R gamma common H he hl ht true r s outside h1]

end CloudG3.ActualStoppedArmExposure
