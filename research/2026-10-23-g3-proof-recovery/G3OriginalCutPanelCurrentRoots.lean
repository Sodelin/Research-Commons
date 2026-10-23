import G1InitializedFrontierPrefix
import G1OriginalCurrentRootReconstruction
import G7PopulationPanelPolynomial

/-!
Existing-original-cut cohort -> fixed descendant panel -> CURRENT roots.
UNCOMPILED source candidate, 2026-10-22, existing G3 owner.
Reuses source-derived prefix support, node panel location and opaque grafting.
No all-full-Code colocation, numerical M/Phi, fresh graph or H/NO premise.
-/
namespace G3OriginalCutPanelCurrentRoots
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceForestSilentPruning
open G1OpaqueSourceGrafting G1ContextualForestReplacement
open G1InitializedFrontierPrefix G1OriginalCurrentRootReconstruction
open GProgram.G7.WholeAncestorPanelCode GProgram.G7.PopulationPanelPolynomial
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def descendantCopies (N : RootedBinary V E X)
    (sample : Copy → X) (e : E) : Finset Copy :=
  Finset.univ.filter (fun x => N.graph.DReach (N.graph.target e) (N.leaf (sample x)))

abbrev ActualCutState (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (e : E) :=
  {d : Code N sample // d ∈ (sourceProgram N r
    (actualFrontierProgram N C H gamma common (C.age (N.graph.target e)))
    (initialCode N sample register)).support}

/-- The selected carrier is STATIC across all actual entering cases. -/
theorem actual_cut_descendant_panel (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (e : E) (he : N.graph.IsBridge e)
    (d : ActualCutState N C sample register H gamma common r e) :
    descendantCopies N sample e = locationPanel (state d.val) (.node (N.graph.target e)) := by
  have h := (actual_initialized_cut_frontier N C sample register H gamma common r e he d.property).1
  ext x
  simp only [descendantCopies, locationPanel, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

theorem actual_cut_panel_closed (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (e : E) (he : N.graph.IsBridge e)
    (d : ActualCutState N C sample register H gamma common r e) :
    AncestorClosed (state d.val) (descendantCopies N sample e) := by
  rw [actual_cut_descendant_panel N C sample register H gamma common r e he d]
  exact locationPanel_closed (state d.val) d.val.property.forest (.node (N.graph.target e))

/-- On the smaller selected panel, copyLocation becomes the LIVE representative's
own location. This uses the general NODE lemma, not edge-only colocation. -/
theorem panel_live_at_place_of_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep)
    (place : Location V E) (hkeep : keep = locationPanel (state s) place) :
    ∀ l ∈ (state (panelCode N s keep hc)).live,
      (state (panelCode N s keep hc)).location l = place := by
  subst keep
  intro l hl
  have hloc := panelCode_location N s place l
  have hrep := (panelCode N s (locationPanel (state s) place) hc).property.forest.representative l hl
  change (state (panelCode N s (locationPanel (state s) place) hc)).location
    ((state (panelCode N s (locationPanel (state s) place) hc)).ancestor l) = place at hloc
  rw [hrep] at hloc
  exact hloc

noncomputable def actualCutPanelCase (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (e : E) (he : N.graph.IsBridge e)
    (d : ActualCutState N C sample register H gamma common r e) :
    EnteringAtPlace N (selectedSample sample (descendantCopies N sample e))
      (.node (N.graph.target e)) := by
  exact ⟨panelCode N d.val (descendantCopies N sample e)
      (actual_cut_panel_closed N C sample register H gamma common r e he d),
    panel_live_at_place_of_eq N d.val (descendantCopies N sample e)
      (actual_cut_panel_closed N C sample register H gamma common r e he d)
      (.node (N.graph.target e))
      (actual_cut_descendant_panel N C sample register H gamma common r e he d)⟩

/-- The smaller panel is connected to the ACTUAL full source selected program;
it is not an independently postulated Markov chain. -/
theorem actual_cut_panel_program (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (e : E)
    (he : N.graph.IsBridge e)
    (d : ActualCutState N C sample register H gamma common r e)
    (ops : List (ProgramStep N)) :
    let keep := descendantCopies N sample e
    let p := actualCutPanelCase N C sample register H gamma common r e he d
    (sourceProgram N r ops d.val).map (fun z => joinedProjection N keep (.inl z)) =
      (sourceProgram N r ops p.val).map (fun z => joinedProjection N keep (.inr z)) := by
  dsimp only
  exact actual_panel_program N r d.val (descendantCopies N sample e)
    (actual_cut_panel_closed N C sample register H gamma common r e he d) ops

/-- The actual node-panel full forest is reconstructed from its CURRENT
live representatives, carrying all original opaque input subtrees. -/
theorem actual_cut_panel_current_root_graft (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (e : E)
    (he : N.graph.IsBridge e)
    (d : ActualCutState N C sample register H gamma common r e)
    (ops : List (ProgramStep N)) :
    let p := actualCutPanelCase N C sample register H gamma common r e he d
    (sourceProgram N r ops p.val).map (rootForest N) =
      (smallerCurrentRootKernel N r ops p.val (.node (N.graph.target e)) p.property).map
        (fun F => F.image (graftUnranked (fun l => (state p.val).genealogy l.val))) := by
  dsimp only
  exact actual_current_roots_complete_graft_law N r ops
    (actualCutPanelCase N C sample register H gamma common r e he d).val
    (.node (N.graph.target e))
    (actualCutPanelCase N C sample register H gamma common r e he d).property

/-- Integrate the SAME actual entering case/history prior outside the
conditional graft law. The descendant-copy carrier stays fixed across cases. -/
theorem actual_cut_panel_joint_context (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (e : E)
    (he : N.graph.IsBridge e) (ops : List (ProgramStep N)) {History Obs : Type*}
    (prior : PMF (ActualCutState N C sample register H gamma common r e × History))
    (exterior : History × (V → Bool) ×
      Finset (UnrankedTree (SelectedCopy (descendantCopies N sample e))) → PMF Obs) :
    let pick := actualCutPanelCase N C sample register H gamma common r e he
    prior.bind (fun c => (sourceProgram N r ops (pick c.1).val).bind
      (fun d => exterior (c.2,(state d).register,rootForest N d))) =
    prior.bind (fun c => (smallerCurrentRootKernel N r ops (pick c.1).val
      (.node (N.graph.target e)) (pick c.1).property).bind
        (fun F => exterior (c.2,(state (pick c.1).val).register,
          F.image (graftUnranked (fun l => (state (pick c.1).val).genealogy l.val))))) := by
  dsimp only
  congr 1
  funext c
  exact actual_original_contextual_forest_replacement N r ops
    (actualCutPanelCase N C sample register H gamma common r e he c.1).val
    (.node (N.graph.target e))
    (actualCutPanelCase N C sample register H gamma common r e he c.1).property c.2 exterior

end G3OriginalCutPanelCurrentRoots
