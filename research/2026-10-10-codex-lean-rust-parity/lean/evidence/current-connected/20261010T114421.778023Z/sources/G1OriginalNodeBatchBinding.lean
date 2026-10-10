import G1OriginalEpochPanelCompression

/-! Exact original node-batch binding at a component interface. Contributor:
dot, 2026-10-03. At D/H/U the whole original same-date node batch has the inside
law of its ONE original node operation. Foreign nodes remain processed in the
actual exterior; the equality is derived from actual movement/projection laws. -/
namespace G1OriginalNodeBatchBinding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceEpochSemigroup
open G1ActualJointProgram G1OriginalEpochPanelSilence G1OriginalEpochPanelCompression
open G1ExteriorBoundarySilence G1InterleavedEpochCompression
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

def AtNodePanel (s : State V E Copy) (keep : Finset Copy) (D : V) : Prop :=
  ∀ x ∈ keep, copyLocation s x = .node D

noncomputable def incomingEdges (N : RootedBinary V E X) (D : V) : Finset E :=
  Finset.univ.filter (fun e => N.graph.target e = D)

lemma actual_node_touched_site (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (v : V) :
    touchedPlace N (originalNodeOperation N H gamma common v) = .node v := by
  by_cases hr : v = N.root
  · simp [originalNodeOperation,hr,touchedPlace]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ <;>
        simp [originalNodeOperation,hr,hh,hc,touchedPlace,H.original_site]
    · simp [originalNodeOperation,hr,hh,touchedPlace,(defaultSelector N).target]

lemma actual_foreign_node_absent (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (D v : V) (hv : v ≠ D)
    (hs : AtNodePanel (state s) keep D) :
    PanelAbsent N (originalNodeOperation N H gamma common v) (state s) keep := by
  intro x hx heq
  rw [actual_node_touched_site,hs x hx] at heq
  exact hv (Location.node.inj heq).symm

lemma actual_foreign_node_preserves_panel (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (D v : V) (hv : v ≠ D)
    (hs : AtNodePanel (state s) keep D) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    AtNodePanel (state d) keep D := by
  intro x hx
  have hm := actual_original_node_kernel_movement N H gamma common v s hd x
  unfold NodeMovement at hm
  have hn : copyLocation (state s) x ≠ .node v := by
    rw [hs x hx]
    intro h; exact hv (Location.node.inj h).symm
  rw [if_neg hn] at hm
  exact hm.trans (hs x hx)

lemma actual_own_node_enters_edges (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (D : V) (hr : D ≠ N.root)
    (hs : AtNodePanel (state s) keep D) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common D) s).support) :
    AtEdgePanel (state d) keep (incomingEdges N D) := by
  intro x hx
  have hm := actual_original_node_kernel_movement N H gamma common D s hd x
  unfold NodeMovement at hm
  rw [if_pos (hs x hx),if_neg hr] at hm
  obtain ⟨e,he,hpop⟩ := hm
  exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩,hpop⟩

lemma actual_node_list_at_edges_identity (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (r : PositivePairRates E) (vs : List V) (s : Code N sample) (keep : Finset Copy) (edges : Finset E)
    (hs : AtEdgePanel (state s) keep edges) :
    (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s).map
        (projection N keep) = PMF.pure (projection N keep s) := by
  have hsafe : ∀ op ∈ vs.map (fun v => ProgramStep.boundary (originalNodeOperation N H gamma common v)),
      EdgeSafeStep N H gamma common edges op := by
    intro op hop
    obtain ⟨v,_,hv⟩ := List.mem_map.mp hop
    exact Or.inr (Or.inr ⟨v,hv.symm⟩)
  have hh := actual_interleaved_epoch_readout N r keep _ s
    (actual_edge_safe_agenda_silent N H gamma common r _ edges hsafe s keep hs)
  simpa [boundary_list_no_intervals,actual_source_time_zero,PMF.pure_map] using hh

/-- A complete actual original node list containing D has the exact inside
law of its one D operation. Later repeated D in the generic list are harmless
because the current panel has already entered original edges. -/
theorem actual_original_node_list_binding (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (r : PositivePairRates E) (vs : List V) (D : V) (hr : D ≠ N.root) (hD : D ∈ vs)
    (s : Code N sample) (keep : Finset Copy) (hs : AtNodePanel (state s) keep D) :
    (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s).map (projection N keep) =
      (boundaryKernel N (originalNodeOperation N H gamma common D) s).map (projection N keep) := by
  induction vs generalizing s with
  | nil => exact False.elim (List.not_mem_nil hD)
  | cons v vs ih =>
      by_cases hv : v = D
      · subst v
        simp only [List.map_cons,sourceProgram,sourceProgramStep,PMF.map_bind]
        calc
          _ = (boundaryKernel N (originalNodeOperation N H gamma common D) s).bind
              (fun d => PMF.pure (projection N keep d)) := by
            apply bind_eq_of_eq_on_support
            intro d hd
            exact actual_node_list_at_edges_identity N H gamma common r vs d keep (incomingEdges N D)
              (actual_own_node_enters_edges N H gamma common s keep D hr hs hd)
          _ = _ := rfl
      · have htail : D ∈ vs := (List.mem_cons.mp hD).resolve_left (Ne.symm hv)
        have habsent := actual_foreign_node_absent N H gamma common s keep D v hv hs
        simp only [List.map_cons,sourceProgram,sourceProgramStep,PMF.map_bind]
        calc
          _ = (boundaryKernel N (originalNodeOperation N H gamma common v) s).bind
              (fun d => (boundaryKernel N (originalNodeOperation N H gamma common D) d).map (projection N keep)) := by
            apply bind_eq_of_eq_on_support
            intro d hd
            exact ih htail d (actual_foreign_node_preserves_panel N H gamma common s keep D v hv hs hd)
          _ = (boundaryKernel N (originalNodeOperation N H gamma common v) s).bind
              (fun _ => (boundaryKernel N (originalNodeOperation N H gamma common D) s).map (projection N keep)) := by
            apply bind_eq_of_eq_on_support
            intro d hd
            have hvw := actual_untouched_boundary_panel N _ s keep habsent hd
            change projectedBoundary N keep _ d = projectedBoundary N keep _ s
            rw [actual_boundary_projection,actual_boundary_projection,hvw]
          _ = _ := PMF.bind_const _ _

end G1OriginalNodeBatchBinding
