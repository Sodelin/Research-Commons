import GroupedParentPathCalendar
import G1OriginalNodeBatchBinding
import Mathlib.Data.Finset.Max

/-!
Cloud G3 actual first-parent-join adapter, 2026-10-08.
SOURCE prototype, compiler UNCHECKED. No frozen provider or source is changed.
The joining vertex is constructed from existing original route lists, not an
assumed graph-to-word/kernel field. Actual slice separation is proved on actual
source supports. Natural initialization and a bridge child supply a focal
node-h frontier in a larger source, without assuming all current roots are there.
Whole mixed-boundary arm continuation and Kingman regrouping remain separate.
-/
namespace CloudG3.FirstParentJoin
set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open GProgram.G5.ParentCalendar
open CloudG3.GroupedParentPathCalendar
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.FiniteSourceSnapshot
open G1CutChildPorts G1OriginalEpochPanelSilence G1OriginalEpochPanelCompression
open G1InitializedFrontierPrefix G1ActualCutDescendants G1NaturalCalendarNodes
open G1NonrootBigonKernel G1OriginalNodeBatchBinding
open G1JointSeparatedSourceGeometry G1ActualJointProgram G1ActualJointEpoch
open G1CanonicalThreeEpochList
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- A nonempty original path contains its actual starting vertex as a source. -/
theorem path_start_is_source {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) (hab : a ≠ b) : ∃ e ∈ es, G.source e = a := by
  cases p with
  | nil => exact False.elim (hab rfl)
  | cons hs _ => exact ⟨_,List.mem_cons_self,hs⟩

/-- Path continuity retains original vertices, including the final endpoint. -/
theorem path_target_is_end_or_source {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) {e : E} (he : e ∈ es) :
    G.target e = b ∨ ∃ f ∈ es, G.source f = G.target e := by
  induction p with
  | nil => simp at he
  | @cons a b g gs hs rest ih =>
      rcases List.mem_cons.mp he with heg | he
      · subst e
        cases rest with
        | nil => exact Or.inl rfl
        | cons hnext tail =>
            exact Or.inr ⟨_,List.mem_cons_of_mem g List.mem_cons_self,hnext⟩
      · rcases ih he with ht | ⟨f,hf,hsrc⟩
        · exact Or.inl ht
        · exact Or.inr ⟨f,List.mem_cons_of_mem g hf,hsrc⟩

/-- On a strictly aged path, an active edge below a listed source vertex cannot
have an older source than that vertex. No unique-parent premise is needed. -/
theorem path_active_source_not_older {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E} (he : e ∈ es)
    {v : V} (hv : ∃ f ∈ es, G.source f = v) {t : ℝ}
    (ha : C.Active t e) (ht : t < C.age v) : C.age (G.source e) ≤ C.age v := by
  induction p with
  | nil => simp at he
  | @cons a b g gs hs rest ih =>
      obtain ⟨f,hf,hfv⟩ := hv
      rcases List.mem_cons.mp hf with hfg | hf
      · subst f
        have hva : v = a := hfv.symm.trans hs
        rw [hva]
        exact (EdgePath.cons hs rest).source_age_le C he
      · rcases List.mem_cons.mp he with heg | he
        · subst e
          have hle := rest.source_age_le C hf
          rw [hfv] at hle
          exact False.elim ((not_le_of_gt ht) (hle.trans ha.1))
        · exact ih he ⟨f,hf,hfv⟩ ha ht

noncomputable def routeSourceVertices (N : RootedBinary V E X)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) : Finset V :=
  (parentRoute H he bit).toFinset.image N.graph.source

noncomputable def commonRouteSources (N : RootedBinary V E X)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) : Finset V :=
  routeSourceVertices N H he false ∩ routeSourceVertices N H he true

theorem route_source_mem_iff (N : RootedBinary V E X)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) (v : V) :
    v ∈ routeSourceVertices N H he bit ↔ ∃ e ∈ parentRoute H he bit, N.graph.source e = v := by
  simp [routeSourceVertices]

/-- The original entry is on both original routes, so the minimizer exists. -/
theorem actual_common_route_sources_nonempty (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) : (commonRouteSources N H he).Nonempty := by
  have hne : entry ≠ H.hybrid := (ne_of_gt (actual_parent_route_entry_older N C H he))
  refine ⟨entry,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
  · exact (route_source_mem_iff N H he false entry).mpr
      (path_start_is_source (parentRoute_path H he false) hne)
  · exact (route_source_mem_iff N H he true entry).mpr
      (path_start_is_source (parentRoute_path H he true) hne)

theorem actual_first_join_exists (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) :
    ∃ j ∈ commonRouteSources N H he,
      ∀ v ∈ commonRouteSources N H he, C.age j ≤ C.age v :=
  Finset.exists_min_image (commonRouteSources N H he) C.age
    (actual_common_route_sources_nonempty N C H he)

/-- Youngest shared ORIGINAL source vertex. This is a finite construction,
not a source-law or graph-coverage assumption. -/
noncomputable def firstParentJoin (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) : V :=
  Classical.choose (actual_first_join_exists N C H he)

theorem actual_first_join_spec (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) :
    firstParentJoin N C H he ∈ commonRouteSources N H he ∧
      ∀ v ∈ commonRouteSources N H he, C.age (firstParentJoin N C H he) ≤ C.age v :=
  Classical.choose_spec (actual_first_join_exists N C H he)

/-- CutChild excludes a hidden later hybrid on either arm or the join. -/
theorem actual_first_join_nonhybrid (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) :
    ¬ N.graph.IsHybrid (firstParentJoin N C H he) := by
  have hm := (Finset.mem_inter.mp (actual_first_join_spec N C H he).1).1
  obtain ⟨e,hem,hs⟩ := (route_source_mem_iff N H he false _).mp hm
  rw [← hs]
  exact actual_parent_route_sources_nonhybrid N hc H he false hem

theorem actual_first_join_age_window (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) :
    C.age H.hybrid < C.age (firstParentJoin N C H he) ∧
      C.age (firstParentJoin N C H he) ≤ C.age entry := by
  have hm := (Finset.mem_inter.mp (actual_first_join_spec N C H he).1).1
  obtain ⟨e,hem,hs⟩ := (route_source_mem_iff N H he false _).mp hm
  have hl := C.age_le_of_directed ((parentRoute_path H he false).target_reaches_end_of_mem hem)
  have hu := (parentRoute_path H he false).source_age_le C hem
  rw [hs] at hu
  exact ⟨by rw [← hs]; exact hl.trans_lt (C.edge_older e),hu⟩

/-- No prefix edge enters h early; every original edge targeting h on this
route is the fixed last parent occurrence. -/
theorem actual_route_edge_into_h_is_original_parent (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (bit : Bool) {e : E}
    (hm : e ∈ parentRoute H he bit) (ht : N.graph.target e = H.hybrid) : e = H.parent bit := by
  rcases List.mem_append.mp hm with hpre | hlast
  · have hp := (Classical.choose_spec (parent_route_prefix_exists H he bit)).1
    have hle := C.age_le_of_directed (hp.target_reaches_end_of_mem hpre)
    rw [ht] at hle
    have hlt := C.edge_older (H.parent bit)
    rw [original_parent_target H bit] at hlt
    exact False.elim ((not_le_of_gt hlt) hle)
  · simpa using hlast

/-- A shared original edge has its target on both route-source lists. The
excluded endpoint h uses distinct ORIGINAL parent occurrences, not just vertices. -/
theorem actual_shared_edge_target_is_common_source (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {e : E}
    (h0 : e ∈ parentRoute H he false) (h1 : e ∈ parentRoute H he true) :
    N.graph.target e ∈ commonRouteSources N H he := by
  have hn : N.graph.target e ≠ H.hybrid := by
    intro ht
    have hsame := (actual_route_edge_into_h_is_original_parent N C H he false h0 ht).symm.trans
      (actual_route_edge_into_h_is_original_parent N C H he true h1 ht)
    exact Bool.false_ne_true (H.parent_injective hsame)
  refine Finset.mem_inter.mpr ⟨?_,?_⟩
  · exact (route_source_mem_iff N H he false _).mpr
      ((path_target_is_end_or_source (parentRoute_path H he false) h0).resolve_left hn)
  · exact (route_source_mem_iff N H he true _).mpr
      ((path_target_is_end_or_source (parentRoute_path H he true) h1).resolve_left hn)

/-- Genuine population separation for every actual cut below the first join. -/
theorem actual_parent_positions_distinct_before_join (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he)) :
    parentPosition C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2) false ≠
      parentPosition C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2) true := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  intro hh
  have h0 := (parentPosition_spec C H he hl hu false).1
  have h1 := (parentPosition_spec C H he hl hu true).1
  rw [← hh] at h1
  have hcommon := actual_shared_edge_target_is_common_source N C H he h0 h1
  have hmin := (actual_first_join_spec N C H he).2 _ hcommon
  have hactive := (parentPosition_spec C H he hl hu false).2.1
  exact (not_le_of_gt ht) (hmin.trans hactive)

/-- Every occupied original arm endpoint lies no older than the first join. -/
theorem actual_position_source_age_le_join (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he)) (bit : Bool) :
    C.age (N.graph.source (parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) bit)) ≤
      C.age (firstParentJoin N C H he) := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  have hv : firstParentJoin N C H he ∈ routeSourceVertices N H he bit := by
    cases bit
    · exact (Finset.mem_inter.mp (actual_first_join_spec N C H he).1).1
    · exact (Finset.mem_inter.mp (actual_first_join_spec N C H he).1).2
  exact path_active_source_not_older C (parentRoute_path H he bit)
    (parentPosition_spec C H he hl hu bit).1 ((route_source_mem_iff N H he bit _).mp hv)
    (parentPosition_spec C H he hl hu bit).2 ht

/-- The existing constructive next cut cannot overshoot the derived join. -/
theorem actual_next_parent_cut_le_join (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he)) :
    nextParentCut N C H he hl (ht.trans_le (actual_first_join_age_window N C H he).2) ≤
      C.age (firstParentJoin N C H he) :=
  (min_le_left _ _).trans (actual_position_source_age_le_join N C H he hl ht false)

/-- Equal age with the starting vertex forces a listed original source to
BE that vertex; strict edge ages exclude every later path vertex. -/
theorem path_source_at_equal_start_age {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E} (he : e ∈ es)
    (heq : C.age (G.source e) = C.age a) : G.source e = a := by
  cases p with
  | nil => simp at he
  | @cons a b g gs hs rest =>
      rcases List.mem_cons.mp he with heg | he
      · subst e; exact hs
      · have hle := rest.source_age_le C he
        have hlt := hle.trans_lt (C.edge_older g)
        rw [hs,heq] at hlt
        exact False.elim ((lt_irrefl _) hlt)

/-- Original graph-to-arm factor lists are CONSTRUCTED from the two inherited
routes. CutChild supplies unique incoming edges at every kept-edge source,
so their older stems agree. The only common source on the two younger arms
is the actual join. These are path identities, not desired source laws. -/
theorem actual_parent_routes_shared_stem_disjoint_arms (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) :
    ∃ stem arm0 arm1 : List E,
      parentRoute H he false = stem ++ arm0 ∧
      parentRoute H he true = stem ++ arm1 ∧
      EdgePath N.graph entry (firstParentJoin N C H he) stem ∧
      EdgePath N.graph (firstParentJoin N C H he) H.hybrid arm0 ∧
      EdgePath N.graph (firstParentJoin N C H he) H.hybrid arm1 ∧
      (∀ v, (∃ e ∈ arm0, N.graph.source e = v) →
        (∃ f ∈ arm1, N.graph.source f = v) → v = firstParentJoin N C H he) := by
  have hcommon := Finset.mem_inter.mp (actual_first_join_spec N C H he).1
  obtain ⟨e0,hm0,hsrc0⟩ := (route_source_mem_iff N H he false _).mp hcommon.1
  obtain ⟨e1,hm1,hsrc1⟩ := (route_source_mem_iff N H he true _).mp hcommon.2
  obtain ⟨pre0,post0,heq0,hpre0,hpost0⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (parentRoute_path H he false) hm0
  obtain ⟨pre1,post1,heq1,hpre1,hpost1⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (parentRoute_path H he true) hm1
  have hp0 : EdgePath N.graph entry (firstParentJoin N C H he) pre0 := by
    simpa only [hsrc0] using hpre0
  have hp1 : EdgePath N.graph entry (firstParentJoin N C H he) pre1 := by
    simpa only [hsrc1] using hpre1
  have hk0 : ∀ f ∈ pre0, ¬ N.graph.IsBridge f := by
    intro f hf
    apply parentRoute_nonbridge H he false f
    rw [heq0]
    exact List.mem_append_left _ hf
  have hk1 : ∀ f ∈ pre1, ¬ N.graph.IsBridge f := by
    intro f hf
    apply parentRoute_nonbridge H he true f
    rw [heq1]
    exact List.mem_append_left _ hf
  have hup0 := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hp0 hk0
  have hup1 := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hp1 hk1
  have hstemeq : pre0 = pre1 := List.reverse_inj.mp
    (hup0.unique_from_kept_source N.acyclic
      (GProgram.G5.NonbridgeRoutes.cut_child_nonbridge_incoming_unique N hc) hup1
      ⟨e0,parentRoute_nonbridge H he false e0 hm0,hsrc0⟩)
  subst pre1
  have harm0 : EdgePath N.graph (firstParentJoin N C H he) H.hybrid (e0 :: post0) :=
    .cons hsrc0 hpost0
  have harm1 : EdgePath N.graph (firstParentJoin N C H he) H.hybrid (e1 :: post1) :=
    .cons hsrc1 hpost1
  refine ⟨pre0,e0 :: post0,e1 :: post1,heq0,heq1,hp0,harm0,harm1,?_⟩
  intro v hv0 hv1
  obtain ⟨f,hf,hfv⟩ := hv0
  obtain ⟨g,hg,hgv⟩ := hv1
  have hfr : f ∈ parentRoute H he false := by rw [heq0]; exact List.mem_append_right _ hf
  have hgr : g ∈ parentRoute H he true := by rw [heq1]; exact List.mem_append_right _ hg
  have hvcommon : v ∈ commonRouteSources N H he := Finset.mem_inter.mpr
    ⟨(route_source_mem_iff N H he false v).mpr ⟨f,hfr,hfv⟩,
      (route_source_mem_iff N H he true v).mpr ⟨g,hgr,hgv⟩⟩
  have hmin := (actual_first_join_spec N C H he).2 v hvcommon
  have hle := harm0.source_age_le C hf
  have hage : C.age (N.graph.source f) = C.age (firstParentJoin N C H he) := by
    apply le_antisymm hle
    simpa only [hfv] using hmin
  exact hfv.symm.trans (path_source_at_equal_start_age C harm0 hf hage)

/-- Two fixed, distinct original arm populations supply the separator. -/
theorem actual_distinct_edge_panels_separated (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (inside outside : Finset Copy) (e0 e1 : E)
    (hne : e0 ≠ e1) (h0 : AtEdgePanel (state s) inside {e0})
    (h1 : AtEdgePanel (state s) outside {e1}) :
    PopulationSeparated (state s) inside outside := by
  intro x hx y hy heq
  obtain ⟨f,hf,hxpop⟩ := h0 x hx
  obtain ⟨g,hg,hypop⟩ := h1 y hy
  have hf : f = e0 := by simpa using hf
  have hg : g = e1 := by simpa using hg
  subst f; subst g
  exact hne (Location.edge.inj (hxpop.symm.trans (heq.trans hypop)))

/-- Every operation of the actual slice preserves EACH singleton arm panel,
so separation on every reachable prefix is a conclusion, not an agenda field. -/
theorem actual_two_edge_safe_agenda_separated (N : RootedBinary V E X)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (e0 e1 : E) (hne : e0 ≠ e1)
    (hsafe0 : ∀ op ∈ ops, EdgeSafeStep N R gamma common {e0} op)
    (hsafe1 : ∀ op ∈ ops, EdgeSafeStep N R gamma common {e1} op)
    (inside outside : Finset Copy) (s : Code N sample)
    (h0 : AtEdgePanel (state s) inside {e0}) (h1 : AtEdgePanel (state s) outside {e1}) :
    SeparatedAgenda N r inside outside ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
      refine ⟨actual_distinct_edge_panels_separated N s inside outside e0 e1 hne h0 h1,?_⟩
      intro d hd
      exact ih (fun p hp => hsafe0 p (List.mem_cons_of_mem op hp))
        (fun p hp => hsafe1 p (List.mem_cons_of_mem op hp)) d
        (actual_edge_safe_step_support N R gamma common r op {e0} (hsafe0 op (by simp)) s inside h0 hd)
        (actual_edge_safe_step_support N R gamma common r op {e1} (hsafe1 op (by simp)) s outside h1 hd)

/-- Actual original parent-route slice: the full two-panel genealogy,
population and SAME-register law factors CONDITIONALLY on this entering Code.
Outside operations execute in the same source; there is no global outside
independence claim and no desired-law/separation premise in this conclusion. -/
theorem actual_parent_slice_joint_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (ht : t < C.age (firstParentJoin N C H he))
    {sample : Copy → X} (r : PositivePairRates E) (inside outside : Finset Copy)
    (s : Code N sample)
    (h0 : AtEdgePanel (state s) inside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) false})
    (h1 : AtEdgePanel (state s) outside {parentPosition C H he hl
      (ht.trans_le (actual_first_join_age_window N C H he).2) true}) :
    let hu := ht.trans_le (actual_first_join_age_window N C H he).2
    let ops := parentPairSliceProgram N C R gamma common H he hl hu
    (sourceProgram N r ops s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s)) := by
  let hu := ht.trans_le (actual_first_join_age_window N C H he).2
  let e0 := parentPosition C H he hl hu false
  let e1 := parentPosition C H he hl hu true
  let cut := nextParentCut N C H he hl hu
  have hsafety (bit : Bool) : ∀ op ∈ parentPairSliceProgram N C R gamma common H he hl hu,
      EdgeSafeStep N R gamma common {parentPosition C H he hl hu bit} op := by
    apply actual_stop_tail_edge_safe_of_end_ge N C R gamma common _ cut
      _ (afterDate N C t) (original_after_ordered N C t)
      (actual_next_parent_cut_is_original_date N C H he hl hu) t
    intro e hem
    have heq : e = parentPosition C H he hl hu bit := by simpa using hem
    subst e
    cases bit
    · exact min_le_left _ _
    · exact min_le_right _ _
  exact actual_separated_joint_program_law N r inside outside _ s
    (actual_two_edge_safe_agenda_separated N R gamma common r _ e0 e1
      (actual_parent_positions_distinct_before_join N C H he hl ht)
      (hsafety false) (hsafety true) inside outside s h0 h1)

/-- Natural initialized frontier at the SOURCE of an original bridge child.
This does not require all original current roots to lie at the focal node. -/
theorem actual_initialized_bridge_source_descendant_frontier (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (child : E)
    (hbridge : N.graph.IsBridge child) (hr : N.graph.source child ≠ N.root)
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age (N.graph.source child)))
      (initialCode N sample register)).support)
    (x : Copy) (hx : N.graph.DReach (N.graph.target child) (N.leaf (sample x))) :
    copyLocation (state s) x = .node (N.graph.source child) := by
  obtain ⟨hready,hnatural,hstrict⟩ :=
    actual_initialized_frontier_support N C sample register R gamma common r _ hs
  have hleaf := (actual_bridge_target_side_descendant N child hbridge _).mpr hx
  have hvalid := s.property.original_descendant x
  have hp := hready.1 x
  cases hloc : copyLocation (state s) x with
  | node v =>
      rw [hloc] at hvalid hp
      change N.graph.DReach v (N.leaf (sample x)) at hvalid
      rcases N.graph.edge_side_cover child (N.underlying_connected (N.graph.source child) v) with hsource | htarget
      · have hcross := actual_bridge_source_descendant_crossing N child hbridge hsource hleaf hvalid
        have hvle : C.age v ≤ C.age (N.graph.source child) := by
          rcases hnatural x v hloc with hv | hv
          · rw [hv] at hsource
            exact False.elim (N.graph.bridge_sides_disjoint hbridge hsource hleaf)
          · exact hv
        have hv : v = N.graph.source child := by
          by_contra hne
          exact (not_lt_of_ge hvle)
            (actual_calendar_directed_age_strict N C hne hcross)
        exact congrArg Location.node hv
      · have hd := (actual_bridge_target_side_descendant N child hbridge v).mp htarget
        have hvle := (actual_calendar_directed_age N C hd).trans_lt (C.edge_older child)
        exact False.elim ((not_lt_of_ge hp) hvle)
  | edge f =>
      rw [hloc] at hvalid hp
      change N.graph.DReach (N.graph.target f) (N.leaf (sample x)) at hvalid
      rcases N.graph.edge_side_cover child
        (N.underlying_connected (N.graph.source child) (N.graph.target f)) with hsource | htarget
      · have hcross := actual_bridge_source_descendant_crossing N child hbridge hsource hleaf hvalid
        have hle := actual_calendar_directed_age N C hcross
        exact False.elim ((not_lt_of_ge hle) (hstrict x f hloc))
      · by_cases hf : f = child
        · subst f
          exact False.elim ((lt_irrefl _) (hready.2 x child hloc))
        · have hsrcside : N.graph.ReachWithout child (N.graph.target child) (N.graph.source f) :=
            htarget.tail ⟨f,hf,Or.inr ⟨rfl,rfl⟩⟩
          have hd := (actual_bridge_target_side_descendant N child hbridge _).mp hsrcside
          have hle := (actual_calendar_directed_age N C hd).trans_lt (C.edge_older child)
          exact False.elim ((not_lt_of_ge hle.le) (hready.2 x f hloc))
  | rootPopulation v =>
      rw [hloc] at hp
      have hstrictroot := actual_calendar_directed_age_strict N C hr.symm
        (N.rooted (N.graph.source child))
      exact False.elim ((not_lt_of_ge hp.2) hstrictroot)

/-- The original hybrid's child edge and its bridge property are DERIVED.
Every focal descendant is at h in every supported actual initialized prefix;
unrelated original roots and their old trees/register remain in the same Code. -/
theorem actual_initialized_hybrid_descendant_frontier (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age H.hybrid))
      (initialCode N sample register)).support)
    (x : Copy) (hx : N.graph.DReach H.hybrid (N.leaf (sample x))) :
    copyLocation (state s) x = .node H.hybrid := by
  obtain ⟨child,hsource,_⟩ := unique_child_edge N H.isHybrid.2
  have hhybrid : N.graph.IsHybrid (N.graph.source child) := by rw [hsource]; exact H.isHybrid
  have hbridge := hc child hhybrid
  have hr : N.graph.source child ≠ N.root := by
    rw [hsource]
    intro hh
    have hdeg := H.isHybrid.1
    rw [hh,N.root_degrees.1] at hdeg
    omega
  have hne : H.hybrid ≠ N.leaf (sample x) := by
    intro hh
    have hz := (N.leaf_degrees (sample x)).2
    rw [← hh,H.isHybrid.2] at hz
    omega
  have hxchild := (descendant_via_unique_child N H.isHybrid.2 hsource hne).mp hx
  have hschild : s ∈ (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age (N.graph.source child)))
      (initialCode N sample register)).support := by simpa only [hsource] using hs
  have hout := actual_initialized_bridge_source_descendant_frontier N C sample register R
    gamma common r child hbridge hr hschild x hxchild
  simpa only [hsource] using hout

/-- Exact focal membership, including absence of original outside labels from
node h; the reverse implication is inherited original descendant validity. -/
theorem actual_initialized_hybrid_descendant_frontier_iff (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) (sample : Copy → X) (register : V → Bool)
    (R : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C R gamma common (C.age H.hybrid))
      (initialCode N sample register)).support) (x : Copy) :
    N.graph.DReach H.hybrid (N.leaf (sample x)) ↔
      copyLocation (state s) x = .node H.hybrid := by
  constructor
  · exact actual_initialized_hybrid_descendant_frontier N hc C H sample register R gamma common r hs x
  · intro hx
    have hv := s.property.original_descendant x
    rw [hx] at hv
    exact hv

/-- Actual mixed-source pulse: the selected focal descendant follows its
CURRENT original owner coin; all unrelated roots may remain elsewhere. -/
theorem actual_selected_pulse_owner_bit (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample) (coin : AtNode (state s) H.hybrid → Bool)
    (x : Copy) (hx : copyLocation (state s) x = .node H.hybrid) :
    copyLocation (state (pulseCode H s coin)) x =
      .edge (H.parent (coin ⟨(state s).ancestor x,⟨s.property.forest.ancestor_live x,hx⟩⟩)) := by
  rw [show copyLocation (state (pulseCode H s coin)) x =
      copyLocation (pulse H (state s) coin) x from
    decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property coin).forest x]
  exact pulse_routes_current_ancestor H (state s) coin
    ⟨(state s).ancestor x,⟨s.property.forest.ancestor_live x,hx⟩⟩

/-- COMMON uses the SAME conditioned full-register bit, with no fresh draw. -/
theorem actual_selected_common_pulse_bit (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (x : Copy) (hx : copyLocation (state s) x = .node H.hybrid) :
    copyLocation (state (pulseCode H s (fun _ => (state s).register H.hybrid))) x =
      .edge (H.parent ((state s).register H.hybrid)) :=
  actual_selected_pulse_owner_bit N H s _ x hx

/-- Existing edges in a mixed node/edge panel are unaffected by every actual
original-node destination. This supports, but does not finish, whole mixed-batch
serialization. -/
theorem actual_node_kernel_keeps_existing_edge (N : RootedBinary V E X)
    {sample : Copy → X} (R : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N R gamma common v) s).support)
    (x : Copy) (e : E) (hx : copyLocation (state s) x = .edge e) :
    copyLocation (state d) x = .edge e := by
  have hm := actual_original_node_kernel_movement N R gamma common v s hd x
  unfold NodeMovement at hm
  have hn : copyLocation (state s) x ≠ .node v := by rw [hx]; intro h; cases h
  rw [if_neg hn] at hm
  exact hm.trans hx

end CloudG3.FirstParentJoin
