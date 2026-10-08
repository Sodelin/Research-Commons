import ActualStoppedArmExposure
import MixedParentBoundary

/-! The ACTUAL focal node batch supplies the two panels of the original
normalized parent-path cell. Current-owner PRIVATE draws or the SAME stored
COMMON bit are used; no post-pulse panel/source-law field is supplied.
Cloud G3, 2026-10-08. Compiler UNCHECKED; graph-wide word coverage separate. -/
namespace CloudG3.ActualHybridEntryCell
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.ParentCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalNodeBatchBinding G1OriginalEpochPanelSilence G1ActualJointProgram G1ActualJointEpoch
open G1InitializedFrontierPrefix G1CutChildPorts G1UnrankedActualFuture
open G1CanonicalThreeEpochList
open CloudG3.FirstParentJoin CloudG3.ParentPathFrontier CloudG3.MixedParentBoundary CloudG3.WholeArmChronology
open CloudG3.StoppedArmOperators CloudG3.UnitArmGenerator CloudG3.ActualStoppedArmExposure
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Classified by the ACTUAL original pulse destination. All copies sharing
one current owner receive its one bit; this is not an iid Copy assignment. -/
noncomputable def routedCopies {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) (bit : Bool) : Finset Copy :=
  keep.filter (fun x => copyLocation (state (pulseCode H s coin)) x = .edge (H.parent bit))

/-- Actual current ancestor of a selected original label at this node. -/
noncomputable def nodeCopyOwner {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (x : Copy)
    (hx : copyLocation (state s) x = .node H.hybrid) : AtNode (state s) H.hybrid :=
  ⟨(state s).ancestor x,⟨s.property.forest.ancestor_live x,hx⟩⟩

theorem actual_selected_copy_pulse_route {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) (x : Copy)
    (hx : copyLocation (state s) x = .node H.hybrid) :
    copyLocation (state (pulseCode H s coin)) x = .edge (H.parent (coin (nodeCopyOwner H s x hx))) := by
  rw [show copyLocation (state (pulseCode H s coin)) x = copyLocation (pulse H (state s) coin) x from
    decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property coin).forest x]
  change (pulse H (state s) coin).location ((state s).ancestor x) = _
  exact pulse_routes_current_ancestor H (state s) coin (nodeCopyOwner H s x hx)

/-- The real pulse routes the CURRENT original ancestor, without requiring
all hidden/outside source roots to occupy the focal hybrid. -/
theorem actual_selected_copy_pulse_parent {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) (x : Copy)
    (hx : copyLocation (state s) x = .node H.hybrid) :
    ∃ bit, copyLocation (state (pulseCode H s coin)) x = .edge (H.parent bit) := by
  exact ⟨coin (nodeCopyOwner H s x hx),actual_selected_copy_pulse_route H s coin x hx⟩

/-- Exact current-owner bit classification, including merged original labels. -/
theorem actual_routed_copy_current_owner_iff {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) (bit : Bool) (x : Copy) (hx : x ∈ keep)
    (hnode : copyLocation (state s) x = .node H.hybrid) :
    x ∈ routedCopies H s keep coin bit ↔ coin (nodeCopyOwner H s x hnode) = bit := by
  have hroute := actual_selected_copy_pulse_route H s coin x hnode
  constructor
  · intro hm
    exact H.parent_injective (Location.edge.inj (hroute.symm.trans (Finset.mem_filter.mp hm).2))
  · intro hb
    exact Finset.mem_filter.mpr ⟨hx,hroute.trans (congrArg (fun b => Location.edge (H.parent b)) hb)⟩

theorem routed_copies_subset {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) (bit : Bool) :
    routedCopies H s keep coin bit ⊆ keep := Finset.filter_subset _ keep

/-- Every selected old label goes into one ACTUAL arm after the pulse. -/
theorem actual_routed_copies_union {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) (hs : AtNodePanel (state s) keep H.hybrid) :
    routedCopies H s keep coin false ∪ routedCopies H s keep coin true = keep := by
  apply Finset.Subset.antisymm
  · exact Finset.union_subset (routed_copies_subset H s keep coin false)
      (routed_copies_subset H s keep coin true)
  · intro x hx
    obtain ⟨bit,hbit⟩ := actual_selected_copy_pulse_parent H s coin x (hs x hx)
    cases bit with
    | false => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,hbit⟩)
    | true => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,hbit⟩)

theorem actual_routed_copies_disjoint {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) :
    Disjoint (routedCopies H s keep coin false) (routedCopies H s keep coin true) := by
  apply Finset.disjoint_left.mpr
  intro x h0 h1
  have hp := (Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h1).2
  exact H.different (Location.edge.inj hp)

/-- Actual parent-edge panel, derived directly from pulseCode. -/
theorem actual_routed_edge_panel {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) (bit : Bool) :
    AtEdgePanel (state (pulseCode H s coin)) (routedCopies H s keep coin bit) {H.parent bit} := by
  intro x hx
  exact ⟨_,Finset.mem_singleton_self _,(Finset.mem_filter.mp hx).2⟩

/-- Whole old trees and the SAME register survive the physical pulse. -/
theorem actual_pulse_forest_register {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) :
    forestRegister (selectedView (state (pulseCode H s coin)) keep) =
      forestRegister (selectedView (state s) keep) := by
  rw [pulseCode_view]
  rfl

/-- The actual original mode, not a desired incoming PMF. COMMON is the SAME
stored hybrid coordinate; PRIVATE is the full actual CURRENT-owner law. -/
noncomputable def focalCoinLaw {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (gamma : unitInterval) (common : Bool) : PMF (AtNode (state s) H.hybrid → Bool) :=
  if common then PMF.pure (fun _ => (state s).register H.hybrid)
    else currentCoinPMF (AtNode (state s) H.hybrid) gamma

/-- ALL tied original nodes execute in the full source; their selected law
is derived from the actual one-node binding, not supplied as a hypothesis. -/
theorem actual_focal_batch_coin_law (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) :
    (sourceProgram N r (nodeOperations N C R gamma common (C.age hy.val)) s).map (projection N keep) =
      (focalCoinLaw (R.parents hy) s (gamma hy) (common hy)).map
        (fun coin => projection N keep (pulseCode (R.parents hy) s coin)) := by
  have hr : hy.val ≠ N.root := by
    intro h
    have hg := hy.property.1
    rw [h,N.root_degrees.1] at hg
    omega
  have hnode : AtNodePanel (state s) keep hy.val := by simpa only [R.original_site] using hs
  let vs := (Finset.univ.filter (fun v : V => C.age v = C.age hy.val)).toList
  have hmem : hy.val ∈ vs := by simp [vs]
  have hb := actual_original_node_list_binding N R gamma common r vs hy.val hr hmem s keep hnode
  change (sourceProgram N r (nodeOperations N C R gamma common (C.age hy.val)) s).map
    (projection N keep) = _ at hb
  rw [hb]
  have hhy : (⟨hy.val,hy.property⟩ : Hybrid N) = hy := rfl
  cases hm : common hy <;>
    simp [focalCoinLaw,originalNodeOperation,hr,hy.property,hhy,hm,boundaryKernel,
      independentPulseKernel,PMF.pure_map,PMF.map_comp,Function.comp_def,R.original_site]

/-- The ordinary actual full-source future factors through its PROVED full
selected interface. This helper carries physical old trees plus Γ. -/
theorem actual_program_forest_register_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (fun d => (sourceUnrankedForest (state d) keep,(state d).register)) =
      (selectedProgram N r keep ops (projection N keep s)).map
        (fun v => (unrankedForest v.val,v.val.register)) := by
  have h := congrArg (fun law : PMF (SelectedIndex N sample keep) => law.map
    (fun v => (unrankedForest v.val,v.val.register))) (actual_source_program_projection N r keep ops s)
  simpa only [PMF.map_comp,projection,Function.comp_def,sourceUnrankedForest,selectedView] using h

/-- Source-connected future after the ACTUAL tied focal batch. Outside node
operations are omitted only from this selected future marginal. -/
theorem actual_focal_batch_then_future (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {sample : Copy → X} (r : PositivePairRates E)
    (s : Code N sample) (keep : Finset Copy) (hs : AtNodePanel (state s) keep (R.parents hy).hybrid)
    (future : List (ProgramStep N)) :
    (sourceProgram N r (nodeOperations N C R gamma common (C.age hy.val) ++ future) s).map
      (fun d => (sourceUnrankedForest (state d) keep,(state d).register)) =
      (focalCoinLaw (R.parents hy) s (gamma hy) (common hy)).bind
        (fun coin => (sourceProgram N r future (pulseCode (R.parents hy) s coin)).map
          (fun d => (sourceUnrankedForest (state d) keep,(state d).register))) := by
  rw [sourceProgram_append,PMF.map_bind]
  simp_rw [actual_program_forest_register_projection]
  rw [← PMF.bind_map,actual_focal_batch_coin_law N C R gamma common hy r s keep hs,PMF.bind_map]

/-- Literal original local cell; no source/coverage law is a structure field. -/
noncomputable def entryCellProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid) :
    List (ProgramStep N) :=
  nodeOperations N C R gamma common (C.age hy.val) ++
    remainingForkTail N C R gamma common (firstParentJoin N C (R.parents hy) he)
      (C.age (R.parents hy).hybrid) (afterDate N C (C.age (R.parents hy).hybrid))

/-- Strictly positive physical exposure of EACH original arm. The first
actual date slice is positive, and all remaining computed slices are NNReal;
there is no freely supplied positive clock or counterfactual edge duration. -/
theorem actual_stopped_exposure_positive (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (r : PositivePairRates E) (bit : Bool)
    {t : ℝ} (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he)) :
    0 < stoppedExposure N C H he r bit t (afterDate N C t) := by
  have hm := original_after_member N C t (firstParentJoin N C H he) ht
  cases hd : afterDate N C t with
  | nil => rw [hd] at hm; exact False.elim (List.not_mem_nil hm)
  | cons c cs =>
      have hct := actual_after_head_later N C t c cs hd
      have ha : 0 < sliceExposure N C H he r bit t c := by
        change 0 < rateExposure r (chronologicalParentEdge N C H he bit t) (Real.toNNReal (c-t))
        change (0 : ℝ) < r.edge (chronologicalParentEdge N C H he bit t) * (Real.toNNReal (c-t) : ℝ)
        exact mul_pos (r.edge_pos _) (NNReal.coe_pos.mpr (Real.toNNReal_pos.mpr (sub_pos.mpr hct)))
      simp only [stoppedExposure]
      split
      · exact ha
      · exact lt_of_lt_of_le ha (le_add_of_nonneg_right (zero_le _))

/-- Normalized operator assembled from the DERIVED arm kernel, with ACTUAL
coin-routed current-owner panels and old forests. The law is proved below. -/
noncomputable def normalizedEntryRow (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy) :=
  (focalCoinLaw (R.parents hy) s (gamma hy) (common hy)).bind (fun coin =>
    (independentProduct
      (unitRaw N sample (routedCopies (R.parents hy) s keep coin false)
        (stoppedExposure N C (R.parents hy) he r false (C.age (R.parents hy).hybrid)
          (afterDate N C (C.age (R.parents hy).hybrid)))
        (forestRegister (selectedView (state s) (routedCopies (R.parents hy) s keep coin false))))
      (unitRaw N sample (routedCopies (R.parents hy) s keep coin true)
        (stoppedExposure N C (R.parents hy) he r true (C.age (R.parents hy).hybrid)
          (afterDate N C (C.age (R.parents hy).hybrid)))
        (forestRegister (selectedView (state s) (routedCopies (R.parents hy) s keep coin true))))).map rawPool)

/-- ACTUAL original hybrid pulse + ALL tied nodes + whole stopped arm word
and final exits. The two panel hypotheses are proved from pulseCode; the
normalized interval law is an applied proof, never an assumed desired row. -/
theorem actual_hybrid_entry_cell_row (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (hy : Hybrid N)
    {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hs : AtNodePanel (state s) keep (R.parents hy).hybrid) :
    (sourceProgram N r (entryCellProgram N C R gamma common hy he) s).map
      (fun d => (sourceUnrankedForest (state d) keep,(state d).register)) =
        normalizedEntryRow N C R gamma common hy he r s keep := by
  rw [entryCellProgram,actual_focal_batch_then_future N C R gamma common hy r s keep hs]
  unfold normalizedEntryRow
  apply bind_eq_of_eq_on_support
  intro coin _
  let H := R.parents hy
  let p := pulseCode H s coin
  let a := routedCopies H s keep coin false
  let b := routedCopies H s keep coin true
  have hl : C.age H.hybrid ≤ C.age H.hybrid := le_refl _
  have ht : C.age H.hybrid < C.age (firstParentJoin N C H he) :=
    (actual_first_join_age_window N C H he).1
  have h0 : AtEdgePanel (state p) a {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false} := by
    rw [actual_parent_position_at_h]
    exact actual_routed_edge_panel H s keep coin false
  have h1 : AtEdgePanel (state p) b {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true} := by
    rw [actual_parent_position_at_h]
    exact actual_routed_edge_panel H s keep coin true
  have h := actual_parent_normalized_exposure_operator N hc C R gamma common H he hl ht r p a b h0 h1
  have hab : a ∪ b = keep := actual_routed_copies_union H s keep coin hs
  rw [hab] at h
  simpa only [H,p,a,b,actual_pulse_forest_register] using h

/-- Concrete natural initialization supplies the node panel. The full
original prefix law is retained rather than postulated as an entering PMF. -/
theorem actual_initialized_hybrid_cell_row (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (hy : Hybrid N) {entry : V} (he : IsComponentEntryFor N entry (R.parents hy).hybrid)
    (r : PositivePairRates E) (keep : Finset Copy)
    (hkeep : ∀ x ∈ keep, N.graph.DReach hy.val (N.leaf (sample x))) :
    (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age hy.val) ++ entryCellProgram N C R gamma common hy he)
      (initialCode N sample register)).map
        (fun d => (sourceUnrankedForest (state d) keep,(state d).register)) =
      (sourceProgram N r (actualFrontierProgram N C R gamma common (C.age hy.val))
        (initialCode N sample register)).bind (fun s => normalizedEntryRow N C R gamma common hy he r s keep) := by
  rw [sourceProgram_append,PMF.map_bind]
  apply bind_eq_of_eq_on_support
  intro s hs
  have hnode : AtNodePanel (state s) keep (R.parents hy).hybrid := by
    intro x hx
    exact actual_initialized_hybrid_descendant_frontier N hc C (R.parents hy) sample register R gamma common r
      (by simpa only [R.original_site] using hs) x (by simpa only [R.original_site] using hkeep x hx)
  exact actual_hybrid_entry_cell_row N hc C R gamma common hy he r s keep hnode

end CloudG3.ActualHybridEntryCell
