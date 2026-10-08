import WholeArmChronology
import G1ActualJointOpaqueContext
import G1UnrankedActualFuture

/-!
Actual ORIGINAL whole stopped two-arm PMF, old trees and SAME register.
Cloud G3, 2026-10-08. SOURCE-only prototype, compiler UNCHECKED.
Every concrete product premise is derived from actual time kernels, original
complete boundary transport and the proved parent frontier. No endpoint law,
SeparatedAgenda or grouped Kingman equality is supplied to the actual theorem.
Compression to exp(lambda*K) remains the explicit separate finite-carrier gate.
-/
namespace CloudG3.StoppedArmOperators
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalNodeBatchBinding G1OriginalExitBatchBinding G1OriginalEpochPanelSilence
open G1OriginalEpochPanelCompression G1ActualJointProgram G1ActualJointEpoch G1ActualJointGenerator
open G1ActualJointBoundary G1ActualJointOpaqueContext G1ContextualForestReplacement
open G1CanonicalThreeEpochList G1InitializedFrontierPrefix G1OriginalCalendarDecomposition
open G1UnrankedActualFuture G1JointForestPreservation G1JointUnrankedForestAssembly
open CloudG3.GroupedParentPathCalendar CloudG3.FirstParentJoin
open CloudG3.MixedParentBoundary CloudG3.ParentPathFrontier CloudG3.WholeArmChronology
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Actual original boundaries only transport populations: even outside private
pulses retain the selected genealogy and the SAME copied register. -/
theorem actual_boundary_genealogy_register (N : RootedBinary V E X)
    {sample : Copy → X} (op : BoundaryOperation N) (s : Code N sample) (keep : Finset Copy)
    {d : Code N sample} (hd : d ∈ (boundaryKernel N op s).support) :
    (selectedView (state d) keep).genealogy = (selectedView (state s) keep).genealogy ∧
    (selectedView (state d) keep).register = (selectedView (state s) keep).register := by
  cases op with
  | exit e =>
      have h : d = exitCode N s e := by simpa [boundaryKernel] using hd
      subst d
      rw [exitCode_view]
      exact ⟨rfl,rfl⟩
  | ordinary e degree =>
      have h : d = ordinaryCode N s e := by simpa [boundaryKernel] using hd
      subst d
      rw [ordinaryCode_view]
      exact ⟨rfl,rfl⟩
  | root =>
      have h : d = rootCode N s := by simpa [boundaryKernel] using hd
      subst d
      rw [rootCode_view]
      exact ⟨rfl,rfl⟩
  | common H =>
      have h : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa [boundaryKernel] using hd
      subst d
      rw [pulseCode_view]
      exact ⟨rfl,rfl⟩
  | independent H gamma =>
      obtain ⟨coin,_,h⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← h,pulseCode_view]
      exact ⟨rfl,rfl⟩

/-- This property holds through ANY actual boundary-only word, not only a
filtered or physically separated batch. -/
theorem actual_boundary_word_genealogy_register (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bs : List (BoundaryOperation N))
    (s : Code N sample) (keep : Finset Copy) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (bs.map ProgramStep.boundary) s).support) :
    (selectedView (state d) keep).genealogy = (selectedView (state s) keep).genealogy ∧
    (selectedView (state d) keep).register = (selectedView (state s) keep).register := by
  induction bs generalizing s with
  | nil =>
      have h : d = s := by simpa [sourceProgram] using hd
      subst d
      exact ⟨rfl,rfl⟩
  | cons b bs ih =>
      change d ∈ ((boundaryKernel N b s).bind
        (sourceProgram N r (bs.map ProgramStep.boundary))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hfirst := actual_boundary_genealogy_register N b s keep hm
      have htail := ih m hdm
      exact ⟨htail.1.trans hfirst.1,htail.2.trans hfirst.2⟩

/-- Complete original head-date boundary, WITHOUT requiring an artificial
preceding positive interval outcome, supplies the next actual arm population. -/
theorem actual_head_boundary_next_panel (N : RootedBinary V E X)
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
    {d : Code N sample} (hd : d ∈ (sourceProgram N r
      (boundaryOperations N C R gamma common c) s).support) :
    let hlc := hl.trans (actual_after_head_later N C t c cs hdates).le
    let huc := hcj.trans_le (actual_first_join_age_window N C H he).2
    AtEdgePanel (state d) keep {parentPosition C H he hlc huc bit} := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  have hct := actual_after_head_later N C t c cs hdates
  have hcle := actual_after_head_le_parent_cut N C H he hl hu c cs hdates
  by_cases hceq : c = nextParentCut N C H he hl hu
  · have hcut : nextParentCut N C H he hl hu < C.age (firstParentJoin N C H he) := by
      rw [← hceq]
      exact hcj
    intro x hx
    obtain ⟨e,hem,hpop⟩ := hs x hx
    have heq : e = parentPosition C H he hl hu bit := by simpa using hem
    subst e
    have hd' : d ∈ (sourceProgram N r (boundaryOperations N C R gamma common
        (nextParentCut N C H he hl hu)) s).support := by simpa only [← hceq] using hd
    have hp := actual_complete_parent_boundary_position N hc C R gamma common H he
      hl ht hcut r s x bit hpop hd'
    refine ⟨_,Finset.mem_singleton_self _,?_⟩
    simpa only [← hceq] using hp
  · have hstrict := lt_of_le_of_ne hcle hceq
    have hend : c < C.age (N.graph.source (parentPosition C H he hl hu bit)) := by
      apply hstrict.trans_le
      apply actual_occupied_parent_edges_end_ge_cut N C H he hl hu
      exact Finset.mem_image.mpr ⟨bit,Finset.mem_univ _,rfl⟩
    have hsafe := actual_earlier_boundary_edge_safe_of_end_ge N C R gamma common
      {parentPosition C H he hl hu bit}
      (C.age (N.graph.source (parentPosition C H he hl hu bit))) c hend
      (by intro e hem; have heq : e = parentPosition C H he hl hu bit := by simpa using hem
          subst e; exact le_refl _)
    have hp := actual_edge_safe_program_support N R gamma common r _ _ hsafe s keep hs hd
    have heq := (parentRoute_path H he bit).active_unique C
      (parentPosition_spec C H he hl hu bit).1
      (parentPosition_spec C H he (hl.trans hct.le)
        (hcj.trans_le (actual_first_join_age_window N C H he).2) bit).1
      ⟨(parentPosition_spec C H he hl hu bit).2.1.trans hct.le,hend⟩
      (parentPosition_spec C H he (hl.trans hct.le)
        (hcj.trans_le (actual_first_join_age_window N C H he).2) bit).2
    simpa only [heq] using hp

/-- Given two supported outputs of the SAME complete proper boundary batch,
each arm's entire selected view agrees. Population agreement is DERIVED by
its next position; genealogy/register agreement is actual transport support. -/
theorem actual_head_boundary_arm_view_unique (N : RootedBinary V E X)
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
    {d z : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C R gamma common c) s).support)
    (hz : z ∈ (sourceProgram N r (boundaryOperations N C R gamma common c) s).support) :
    projection N keep d = projection N keep z := by
  have hbs : boundaryOperations N C R gamma common c =
      ((originalExits N C c).map BoundaryOperation.exit ++
       ((Finset.univ.filter (fun v : V => C.age v = c)).toList.map
         (originalNodeOperation N R gamma common))).map ProgramStep.boundary := by
    simp only [boundaryOperations,originalExits,List.map_append,List.map_map,Function.comp_def]
  have hdgr := actual_boundary_word_genealogy_register N r _ s keep (by rw [← hbs]; exact hd)
  have hzgr := actual_boundary_word_genealogy_register N r _ s keep (by rw [← hbs]; exact hz)
  have hdp := actual_head_boundary_next_panel N hc C R gamma common H he hl ht
    c cs hdates hcj bit r s keep hs hd
  have hzp := actual_head_boundary_next_panel N hc C R gamma common H he hl ht
    c cs hdates hcj bit r s keep hs hz
  apply Subtype.ext
  apply SelectedView.ext
  · exact hdgr.1.trans hzgr.1.symm
  · funext x
    by_cases hx : x ∈ keep
    · obtain ⟨e,hem,hpop⟩ := hdp x hx
      obtain ⟨f,hfm,hpof⟩ := hzp x hx
      have hef : e = f := (Finset.mem_singleton.mp hem).trans (Finset.mem_singleton.mp hfm).symm
      simp only [projection,selectedView,selectedLocation,if_pos hx,hpop,hpof,hef]
    · simp only [projection,selectedView,selectedLocation,if_neg hx]
  · exact hdgr.2.trans hzgr.2.symm

/-- Complete actual proper boundary has a conditional product row. It is
proved from the deterministic selected view, not from a separation field. -/
theorem actual_head_boundary_joint_row (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs)
    (hcj : c < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    let ops := boundaryOperations N C R gamma common c
    (sourceProgram N r ops s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s)) := by
  let ops := boundaryOperations N C R gamma common c
  obtain ⟨z,hz⟩ := (sourceProgram N r ops s).support_nonempty
  have hp := pair_map_product_of_constant_right (sourceProgram N r ops s)
    (projection N inside) (projection N outside) (projection N outside z)
    (fun d hd => actual_head_boundary_arm_view_unique N hc C R gamma common H he hl ht
      c cs hdates hcj true r s outside h1 hd hz)
  simpa only [jointProjection,actual_source_program_projection] using hp

lemma selected_program_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (xs ys : List (ProgramStep N))
    (v : SelectedIndex N sample keep) :
    selectedProgram N r keep (xs ++ ys) v =
      (selectedProgram N r keep xs v).bind (selectedProgram N r keep ys) := by
  induction xs generalizing v with
  | nil => simp [selectedProgram]
  | cons x xs ih =>
      simp only [List.cons_append,selectedProgram,PMF.bind_bind]
      congr 1
      funext w
      exact ih w

/-- Internal PMF composition algebra. Its concrete row hypotheses below are
always DISCHARGED by actual derived interval/batch/tail laws; they are not new
scientific premises of actual_stopped_parent_joint_row. -/
lemma compose_actual_joint_rows (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (xs ys : List (ProgramStep N)) (s : Code N sample)
    (hfirst : (sourceProgram N r xs s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside xs (projection N inside s))
        (selectedProgram N r outside xs (projection N outside s)))
    (htail : ∀ d ∈ (sourceProgram N r xs s).support,
      (sourceProgram N r ys d).map (jointProjection N inside outside) =
        independentProduct (selectedProgram N r inside ys (projection N inside d))
          (selectedProgram N r outside ys (projection N outside d))) :
    (sourceProgram N r (xs ++ ys) s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside (xs ++ ys) (projection N inside s))
        (selectedProgram N r outside (xs ++ ys) (projection N outside s)) := by
  rw [sourceProgram_append,PMF.map_bind]
  calc
    _ = (sourceProgram N r xs s).bind (fun d =>
      independentProduct (selectedProgram N r inside ys (projection N inside d))
        (selectedProgram N r outside ys (projection N outside d))) :=
      bind_eq_of_eq_on_support _ _ _ htail
    _ = ((sourceProgram N r xs s).map (jointProjection N inside outside)).bind
      (fun v => independentProduct (selectedProgram N r inside ys v.1)
        (selectedProgram N r outside ys v.2)) := by rw [PMF.bind_map]; rfl
    _ = _ := by rw [hfirst,independentProduct_bind,selected_program_append,selected_program_append]

/-- Actual ORIGINAL interval plus its complete proper boundary is a proved
conditional product on the two next arm views. -/
theorem actual_head_block_joint_row (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (c : ℝ) (cs : List ℝ) (hdates : afterDate N C t = c :: cs)
    (hcj : c < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    let ops := [.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c
    (sourceProgram N r ops s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s)) := by
  apply compose_actual_joint_rows N r inside outside _ _ s
  · have hsep := actual_distinct_edge_panels_separated N s inside outside _ _
      (actual_parent_positions_distinct_before_join N C H he hl ht) h0 h1
    have hh := actual_separated_joint_epoch_law N r inside outside (Real.toNNReal (c-t)) s hsep
    simpa [sourceProgram,sourceProgramStep,actual_source_program_projection] using hh
  · intro m hm
    have hm' : m ∈ (sourceTimeKernel N r (Real.toNNReal (c-t)) s).support := by
      simpa [sourceProgram,sourceProgramStep] using hm
    exact actual_head_boundary_joint_row N hc C R gamma common H he hl ht c cs hdates hcj
      r m inside outside (actual_time_edge_panel N r _ s inside _ h0 hm')
        (actual_time_edge_panel N r _ s outside _ h1 hm')

/-- SINGLE full original stopped operator PMF term, before j's exits. The
actual finite chronological recursion discharges all concrete row assumptions.
Neither a desired law nor a SeparatedAgenda is a premise. Outside originals
execute; the two factors are the exact SAME original selected programme rows. -/
theorem actual_stopped_parent_joint_row (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (dates : List ℝ) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hdates : dates = afterDate N C t)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t dates
    (sourceProgram N r ops s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s)) := by
  induction dates generalizing t s with
  | nil =>
      have hm := original_after_member N C t (firstParentJoin N C H he) ht
      rw [← hdates] at hm
      exact False.elim (List.not_mem_nil hm)
  | cons c cs ih =>
      have hhead : afterDate N C t = c :: cs := hdates.symm
      have hord := original_after_ordered N C t
      rw [hhead] at hord
      have hm := original_after_member N C t (firstParentJoin N C H he) ht
      rw [hhead] at hm
      by_cases hfinal : c = C.age (firstParentJoin N C H he)
      · have hsep := actual_distinct_edge_panels_separated N s inside outside _ _
          (actual_parent_positions_distinct_before_join N C H he hl ht) h0 h1
        have hh := actual_separated_joint_epoch_law N r inside outside (Real.toNNReal (c-t)) s hsep
        simpa [stopBeforeTail,hfinal,sourceProgram,sourceProgramStep,
          actual_source_program_projection] using hh
      · have hcj : c < C.age (firstParentJoin N C H he) :=
          (List.pairwise_cons.mp hord).1 _ ((List.mem_cons.mp hm).resolve_left (Ne.symm hfinal))
        have hct := actual_after_head_later N C t c cs hhead
        have hword : stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (c::cs) =
            ([.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c) ++
              stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) c cs := by
          simp [stopBeforeTail,hfinal,List.append_assoc]
        rw [hword]
        apply compose_actual_joint_rows N r inside outside _ _ s
        · exact actual_head_block_joint_row N hc C R gamma common H he hl ht c cs hhead hcj
            r s inside outside h0 h1
        · intro m hms
          have hm0 := actual_original_head_next_panel N hc C R gamma common H he hl ht
            c cs hhead hcj false r s inside h0 hms
          have hm1 := actual_original_head_next_panel N hc C R gamma common H he hl ht
            c cs hhead hcj true r s outside h1 hms
          exact ih (hl.trans hct.le) hcj
            (actual_after_head_tail N C t c cs hhead).symm m hm0 hm1

/-- Explicit forest-and-SAME-register readout of the actual two arm views.
The two forest sets retain every full old selected subtree and binary clade.
Identification with pruning the UNION panel additionally needs the existing
pruned-panel purity consumer; it is not silently part of this definition. -/
noncomputable def pooledArmReadout (v : SelectedView V E Copy × SelectedView V E Copy) :=
  (unrankedForest v.1 ∪ unrankedForest v.2,v.1.register)

/-- Concrete actual PMF for the pooled two-arm unranked readout. Final exits
preserve both forests and SAME Γ; no factorization after pooling is assumed.
The factor rows are actual source operators, not a supplied endpoint table. -/
theorem actual_stopped_parent_pooled_operator (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
    (sourceProgram N r (remainingForkTail N C R gamma common (firstParentJoin N C H he)
      t (afterDate N C t)) s).map (fun d => pooledArmReadout
        (selectedView (state d) inside,selectedView (state d) outside)) =
      (independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s))).map
          (fun v => pooledArmReadout (v.1.val,v.2.val)) := by
  let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
  let es := originalExits N C (C.age (firstParentJoin N C H he))
  change (sourceProgram N r (ops ++ es.map (fun e => .boundary (.exit e))) s).map _ = _
  rw [sourceProgram_append,PMF.map_bind]
  have hsuffix (m : Code N sample) :
      (sourceProgram N r (es.map (fun e => .boundary (.exit e))) m).map
        (fun d => pooledArmReadout (selectedView (state d) inside,selectedView (state d) outside)) =
      PMF.pure (pooledArmReadout (selectedView (state m) inside,selectedView (state m) outside)) := by
    rw [actual_exit_list_program,PMF.pure_map]
    congr 1
    unfold pooledArmReadout unrankedForest
    rw [actual_exit_list_genealogy N es m inside,actual_exit_list_genealogy N es m outside,
      actual_exit_list_register N es m inside]
  simp_rw [hsuffix]
  rw [PMF.bind_pure_comp]
  have hh := congrArg (fun law => law.map (fun v => pooledArmReadout (v.1.val,v.2.val)))
    (actual_stopped_parent_joint_row N hc C R gamma common H he (afterDate N C t)
      hl ht rfl r s inside outside h0 h1)
  simpa only [PMF.map_comp,jointProjection,Function.comp_def] using hh

/-- The endpoint BEFORE the final exits is physically separated on EVERY
actual source outcome. Complete-batch successor support discharges the
recursive premise; no no-mixed-tree or endpoint separator is supplied. -/
theorem actual_stopped_parent_endpoint_separated (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (dates : List ℝ) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    (hdates : dates = afterDate N C t)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true})
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (stopBeforeTail N C R gamma common
      (C.age (firstParentJoin N C H he)) t dates) s).support) :
    G1JointSeparatedSourceGeometry.PopulationSeparated (state d) inside outside := by
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
      by_cases hfinal : c = C.age (firstParentJoin N C H he)
      · have hd' : d ∈ (sourceTimeKernel N r (Real.toNNReal (c-t)) s).support := by
          simpa [stopBeforeTail,hfinal,sourceProgram,sourceProgramStep] using hd
        exact actual_epoch_separation N r inside outside _ s
          (actual_distinct_edge_panels_separated N s inside outside _ _
            (actual_parent_positions_distinct_before_join N C H he hl ht) h0 h1) hd'
      · have hcj : c < C.age (firstParentJoin N C H he) :=
          (List.pairwise_cons.mp hord).1 _ ((List.mem_cons.mp hm).resolve_left (Ne.symm hfinal))
        have hct := actual_after_head_later N C t c cs hhead
        have hword : stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (c::cs) =
            ([.interval (Real.toNNReal (c-t))] ++ boundaryOperations N C R gamma common c) ++
              stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) c cs := by
          simp [stopBeforeTail,hfinal,List.append_assoc]
        rw [hword,sourceProgram_append] at hd
        obtain ⟨m,hms,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        have hm0 := actual_original_head_next_panel N hc C R gamma common H he hl ht
          c cs hhead hcj false r s inside h0 hms
        have hm1 := actual_original_head_next_panel N hc C R gamma common H he hl ht
          c cs hhead hcj true r s outside h1 hms
        exact ih (hl.trans hct.le) hcj
          (actual_after_head_tail N C t c cs hhead).symm m hm0 hm1 hdm

/-- No original boundary grafts trees, so the actual final exit batch cannot
create a mixed selected tree even though its populations have pooled. -/
theorem actual_boundary_word_pruned_pure (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bs : List (BoundaryOperation N))
    (s : Code N sample) (inside outside : Finset Copy)
    (hp : PrunedPanelSeparated (state s) inside outside) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (bs.map ProgramStep.boundary) s).support) :
    PrunedPanelSeparated (state d) inside outside := by
  induction bs generalizing s with
  | nil =>
      have h : d = s := by simpa [sourceProgram] using hd
      exact h ▸ hp
  | cons b bs ih =>
      change d ∈ ((boundaryKernel N b s).bind
        (sourceProgram N r (bs.map ProgramStep.boundary))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (actual_boundary_pruned_panel_separation N b s inside outside hp hm) hdm

/-- Exact physical selected-union forest readout AFTER all final original
exits. The no-mixed-tree condition is DERIVED from the actual stopped endpoint
and boundary transport; it is not assumed as a graph/source admission. -/
theorem actual_parent_whole_selected_operator (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
    (sourceProgram N r (remainingForkTail N C R gamma common (firstParentJoin N C H he)
      t (afterDate N C t)) s).map (fun d =>
        (sourceUnrankedForest (state d) (inside ∪ outside),(state d).register)) =
      (independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s))).map
          (fun v => pooledArmReadout (v.1.val,v.2.val)) := by
  let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
  let es := originalExits N C (C.age (firstParentJoin N C H he))
  have heq : (sourceProgram N r (remainingForkTail N C R gamma common (firstParentJoin N C H he)
      t (afterDate N C t)) s).map (fun d =>
        (sourceUnrankedForest (state d) (inside ∪ outside),(state d).register)) =
      (sourceProgram N r (remainingForkTail N C R gamma common (firstParentJoin N C H he)
        t (afterDate N C t)) s).map (fun d => pooledArmReadout
          (selectedView (state d) inside,selectedView (state d) outside)) := by
    apply map_eq_of_eq_on_support
    intro d hd
    change d ∈ (sourceProgram N r (ops ++ es.map (fun e => .boundary (.exit e))) s).support at hd
    rw [sourceProgram_append] at hd
    obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    have hsep := actual_stopped_parent_endpoint_separated N hc C R gamma common H he
      (afterDate N C t) hl ht rfl r s inside outside h0 h1 hm
    have hp := actual_boundary_word_pruned_pure N r (es.map BoundaryOperation.exit) m
      inside outside (population_separated_pruned_panels (state m) m.property.forest inside outside hsep)
      (by simpa only [List.map_map,Function.comp_def] using hdm)
    rw [actual_pruned_forest_union (state d) d.property.forest inside outside hp]
    rfl
  exact heq.trans (actual_stopped_parent_pooled_operator N hc C R gamma common H he
    hl ht r s inside outside h0 h1)

/-- Any genuine boundary-only suffix is silent for the unranked forest and
SAME register at this instant. It may change populations, so this theorem
does NOT erase the causal population interface of a later interval. -/
theorem actual_boundary_word_forest_register (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (bs : List (BoundaryOperation N))
    (s : Code N sample) (keep : Finset Copy) :
    (sourceProgram N r (bs.map ProgramStep.boundary) s).map (fun d =>
      (sourceUnrankedForest (state d) keep,(state d).register)) =
      PMF.pure (sourceUnrankedForest (state s) keep,(state s).register) := by
  calc
    _ = (sourceProgram N r (bs.map ProgramStep.boundary) s).map
        (fun _ => (sourceUnrankedForest (state s) keep,(state s).register)) := by
      apply map_eq_of_eq_on_support
      intro d hd
      have hgr := actual_boundary_word_genealogy_register N r bs s keep hd
      apply Prod.ext
      · unfold sourceUnrankedForest unrankedForest
        rw [hgr.1]
      · exact hgr.2
    _ = _ := PMF.map_const _ _

/-- The single stopped product/pooling PMF remains the actual physical
unranked readout after a genuine boundary-only suffix, including j's complete
node batch. Population transport is retained in the original Code; no claim
is made about forgetting it before a future timed/ordinary interval. -/
theorem actual_parent_whole_selected_boundary_suffix (N : RootedBinary V E X)
    (hc : G1CutChildPorts.CutChild N) (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (inside outside : Finset Copy)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true})
    (bs : List (BoundaryOperation N)) :
    let ops := stopBeforeTail N C R gamma common (C.age (firstParentJoin N C H he)) t (afterDate N C t)
    (sourceProgram N r ((remainingForkTail N C R gamma common (firstParentJoin N C H he)
      t (afterDate N C t)) ++ bs.map ProgramStep.boundary) s).map (fun d =>
        (sourceUnrankedForest (state d) (inside ∪ outside),(state d).register)) =
      (independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s))).map
          (fun v => pooledArmReadout (v.1.val,v.2.val)) := by
  rw [sourceProgram_append,PMF.map_bind]
  simp_rw [actual_boundary_word_forest_register N r bs]
  rw [PMF.bind_pure_comp]
  exact actual_parent_whole_selected_operator N hc C R gamma common H he hl ht
    r s inside outside h0 h1

end CloudG3.StoppedArmOperators
