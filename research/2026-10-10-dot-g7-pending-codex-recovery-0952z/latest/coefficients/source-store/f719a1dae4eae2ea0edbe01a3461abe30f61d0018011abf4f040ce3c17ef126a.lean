import G7OrderedFrontierProduct

/-! Every literal original calendar supplies a complete compatible frontier
order. The whole-edge product is consequently calendar-order independent.
Internal uncompiled full-endpoint candidate, dot 2026-10-10. -/
namespace GProgram.G7.CalendarFrontierOrder
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open GProgram.G7.OriginalEdgeGathering GProgram.G7.ActualCalendarGathering
open GProgram.G7.CalendarExposureClosedForm GProgram.G7.OrderedFrontierProduct
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def atomAge (N : RootedBinary V E X) (C : Calendar N.graph) : Atom V E → ℝ
  | .exit e => C.age (N.graph.source e)
  | .node v => C.age v

noncomputable def boundaryAtoms (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) : List (Atom V E) :=
  ((Finset.univ.filter (fun e : E => C.age (N.graph.source e)=a)).toList.map Atom.exit) ++
  ((Finset.univ.filter (fun v : V => C.age v=a)).toList.map Atom.node)

noncomputable def calendarAtoms (N : RootedBinary V E X) (C : Calendar N.graph) : List (Atom V E) :=
  (sortedOriginalDates N C).flatMap (boundaryAtoms N C)

lemma mem_boundaryAtoms (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) (op : Atom V E) :
    op ∈ boundaryAtoms N C a ↔ atomAge N C op=a := by
  cases op <;> simp [boundaryAtoms,atomAge,List.mem_append,List.mem_map,Finset.mem_toList]

lemma boundaryAtoms_nodup (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) :
    (boundaryAtoms N C a).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(Finset.nodup_toList _).map (fun e f h => Atom.exit.inj h),
    (Finset.nodup_toList _).map (fun v w h => Atom.node.inj h),?_⟩
  intro x hx y hy hxy
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp hy
  cases hxy

lemma calendarAtoms_nodup (N : RootedBinary V E X) (C : Calendar N.graph) :
    (calendarAtoms N C).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun a _ => boundaryAtoms_nodup N C a,?_⟩
  apply (original_dates_strict N C).imp
  intro a b hab
  apply List.disjoint_left.mpr
  intro op ha hb
  have h₁ := (mem_boundaryAtoms N C a op).mp ha
  have h₂ := (mem_boundaryAtoms N C b op).mp hb
  exact (ne_of_lt hab) (h₁.symm.trans h₂)

lemma every_original_atom_scheduled (N : RootedBinary V E X) (C : Calendar N.graph) (op : Atom V E) :
    op ∈ calendarAtoms N C := by
  apply List.mem_flatMap.mpr
  refine ⟨atomAge N C op,?_,(mem_boundaryAtoms N C _ op).mpr rfl⟩
  cases op with
  | exit e => exact original_date_scheduled N C (N.graph.source e)
  | node v => exact original_date_scheduled N C v

/-- Exact same census of original node and EDGE OCCURRENCE atoms. -/
theorem calendarAtoms_perm (N : RootedBinary V E X) (C D : Calendar N.graph) :
    (calendarAtoms N C).Perm (calendarAtoms N D) := by
  apply (List.perm_ext_iff_of_nodup (calendarAtoms_nodup N C) (calendarAtoms_nodup N D)).mpr
  intro op
  exact iff_of_true (every_original_atom_scheduled N C op) (every_original_atom_scheduled N D op)

lemma required_age_le (N : RootedBinary V E X) (C : Calendar N.graph) (a b : Atom V E)
    (h : RequiredBefore N a b) : atomAge N C a ≤ atomAge N C b := by
  cases a with
  | exit e =>
    cases b with
    | exit f => exact False.elim h
    | node v => change v=N.graph.source e at h; subst v; exact le_rfl
  | node v =>
    cases b with
    | node u => exact False.elim h
    | exit e => change v=N.graph.target e at h; subst v; exact (C.edge_older e).le

lemma boundaryAtoms_compatible (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) :
    (boundaryAtoms N C a).Pairwise (Compatible N) := by
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · simp [List.pairwise_map,Compatible,RequiredBefore]
  · simp [List.pairwise_map,Compatible,RequiredBefore]
  · intro x hx y hy hbad
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
    have he' := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    have hv' := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
    change v=N.graph.target e at hbad
    subst v
    have h := C.edge_older e
    rw [he',hv'] at h
    exact lt_irrefl _ h

/-- Both original endpoint constraints are DERIVED from calendar strictness
and the literal exit-before-node phase at a common date. -/
theorem calendarAtoms_compatible (N : RootedBinary V E X) (C : Calendar N.graph) :
    (calendarAtoms N C).Pairwise (Compatible N) := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun a _ => boundaryAtoms_compatible N C a,?_⟩
  apply (original_dates_strict N C).imp
  intro a b hab x hx y hy hbad
  have hxy := required_age_le N C y x hbad
  rw [(mem_boundaryAtoms N C a x).mp hx,(mem_boundaryAtoms N C b y).mp hy] at hxy
  exact (not_lt_of_ge hxy) hab

theorem actual_calendar_frontier_order_independent (N : RootedBinary V E X) {sample : Copy → X}
    (C D : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (w : ExposureBank E) :
    ((calendarAtoms N C).map (atomMatrix N (sample:=sample) H gamma common w)).prod =
      ((calendarAtoms N D).map (atomMatrix N H gamma common w)).prod :=
  product_eq_of_compatible_orders _ (Compatible N)
    (compatible_atoms_commute N H gamma common w) _ _
    (calendarAtoms_perm N C D) (calendarAtoms_compatible N C) (calendarAtoms_compatible N D)

lemma wholeEdgeFrontier_matrix_atoms (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) :
    (wholeEdgeFrontier N C r (sortedOriginalDates N C)).map (gatheredMatrix N (sample:=sample) H gamma common) =
      (calendarAtoms N C).map (atomMatrix N H gamma common (wholeEdgeBank N C r)) := by
  simp [wholeEdgeFrontier,gatheredBoundary,calendarAtoms,boundaryAtoms,List.map_flatMap,
    List.map_append,List.map_map,Function.comp_def,gatheredMatrix,atomMatrix]

end GProgram.G7.CalendarFrontierOrder
