import G1CanonicalCompactComponentRow

/-! Actual canonical single-exit support from the TRUE independently
initialized CURRENT-root source and the proven complete compact-word row.
Contributor: dot, 2026-10-03. Original descendant/exterior count is unbounded. -/
namespace G1CanonicalSingleExitSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceInitializedCalendar
open G1OriginalNodeBatchBinding G1CanonicalCompactComponentRow
open G1ExtractedComponentProgram G1OriginalRegistryBigon G1ActualCurrentPanelInitialization
open G1ActualJointOpaqueContext G1CutChildPorts G1ActualTwoPortBlob
open G1CanonicalComponentSegment G1ActualEnteringFrontier G1InitializedFrontierPrefix
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_canonical_component_single_exit (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (hkeep : keep ⊆ (state s).live)
    (hs : AtNodePanel (state s) keep (N.graph.target A.child)) :
    let B := registryAlignedBigon N hc b A H
    ∀ d ∈ (sourceProgram N r (componentAgenda N C b B H gamma common) s).support,
      ∀ x ∈ keep, copyLocation (state d) x = .node (N.graph.source B.entry) := by
  dsimp only
  let B := registryAlignedBigon N hc b A H
  let word := componentProgram N hc C b B (gamma (originalHybrid N b B)) (common (originalHybrid N b B))
  have hrow := congrArg (fun p => p.map Subtype.val)
    (actual_canonical_compact_component_row N hc C b A H gamma common r keep s hs)
  simp only [PMF.map_comp,Function.comp_def,projection] at hrow
  rw [actual_current_panel_program_law N r word s keep hkeep] at hrow
  have hinput : ∀ l ∈ (state (currentPanelCode N s keep hkeep)).live,
      (state (currentPanelCode N s keep hkeep)).location l = .node (N.graph.target B.child) := by
    intro l _
    rw [currentPanelCode_location]
    have hr := s.property.forest.representative l.val (hkeep l.property)
    change (state s).ancestor l.val = l.val at hr
    have hp := hs l.val l.property
    change (state s).location ((state s).ancestor l.val) = .node (N.graph.target A.child) at hp
    rw [hr] at hp
    exact hp
  intro d hd x hx
  have hviewSupport : selectedView (state d) keep ∈
      ((sourceProgram N r (componentAgenda N C b B H gamma common) s).map
        (fun z => selectedView (state z) keep)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨d,hd,rfl⟩
  rw [hrow] at hviewSupport
  obtain ⟨z,hz,hview⟩ := (PMF.mem_support_map_iff _ _ _).mp hviewSupport
  have hexit := actual_extracted_component_exit_population N hc C r b B
    (gamma (originalHybrid N b B)) (common (originalHybrid N b B))
    (currentPanelCode N s keep hkeep) hinput hz
  let l : SelectedCopy keep := ⟨x,hx⟩
  have hpop : copyLocation (state z) l = .node (N.graph.source B.entry) :=
    hexit _ (z.property.forest.ancestor_live l)
  have hp := congrArg (fun v => v.population x) hview
  change (liftView keep (selectedView (state z) Finset.univ)).population l.val =
    (selectedView (state d) keep).population x at hp
  rw [lifted_original_population] at hp
  have hp' : copyLocation (state z) l = copyLocation (state d) x := by
    simpa only [selectedView,selectedLocation,if_pos hx,Option.some.injEq] using hp
  exact hp'.symm.trans hpop

/-- For the actual initialized cut frontier, the canonical exit is DERIVED;
only CURRENT roots entering D are selected, with exterior roots retained. -/
theorem actual_initialized_canonical_single_exit (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age (N.graph.target A.child)))
      (initialCode N sample register)).support) :
    let B := registryAlignedBigon N hc b A H
    ∀ d ∈ (sourceProgram N r (componentAgenda N C b B H gamma common) s).support,
      ∀ x ∈ enteringRoots N s (N.graph.target A.child),
        copyLocation (state d) x = .node (N.graph.source A.entry) := by
  obtain ⟨_,hin,_⟩ := actual_initialized_cut_frontier N C sample register H gamma common r A.child A.child_bridge hs
  exact actual_canonical_component_single_exit N hc C b A H gamma common r
    (enteringRoots N s (N.graph.target A.child)) s (Finset.filter_subset _ _) hin

#print axioms actual_initialized_canonical_single_exit
end G1CanonicalSingleExitSupport
