import G1UnrankedActualEpoch

/-! Natural CURRENT-owner private pulses on the whole rooted unranked causal
view. Contributor: dot, 2026-10-03. Actual coin-product transport is derived. -/
namespace G1UnrankedNaturalPulse
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory ProbabilityTheory
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceForestPulseTransport
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def unrankedPopulationBlocks (v : UnrankedView V E Copy)
    (keep : Finset Copy) (place : Location V E) : Finset (Finset Copy) :=
  (keep.filter (fun x => v.population x = some place)).image
    (fun x => optionTreeLeaves (v.genealogy x))

lemma raw_unranked_population_blocks (v : SelectedView V E Copy) (keep : Finset Copy)
    (place : Location V E) : viewPopulationBlocks v keep place =
      unrankedPopulationBlocks (unrankedView v) keep place := by
  simp only [viewPopulationBlocks,unrankedPopulationBlocks,unrankedView,optionUnranked_leaves]

abbrev UnrankedBlockAtNode (v : UnrankedView V E Copy) (keep : Finset Copy) (node : V) :=
  {A : Finset Copy // A ∈ unrankedPopulationBlocks v keep (.node node)}

noncomputable def originalUnrankedBlockEquiv (v : SelectedView V E Copy)
    (keep : Finset Copy) (node : V) :
    ViewBlockAtNode v keep node ≃ UnrankedBlockAtNode (unrankedView v) keep node where
  toFun A := ⟨A.val,(raw_unranked_population_blocks v keep (.node node)) ▸ A.property⟩
  invFun A := ⟨A.val,(raw_unranked_population_blocks v keep (.node node)).symm ▸ A.property⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl

noncomputable def unrankedBlockCoin (v : SelectedView V E Copy) (keep : Finset Copy) (node : V)
    (coin : ViewBlockAtNode v keep node → Bool) : UnrankedBlockAtNode (unrankedView v) keep node → Bool :=
  fun A => coin ((originalUnrankedBlockEquiv v keep node).symm A)

noncomputable def unrankedProjectedPulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : UnrankedView V E Copy)
    (keep : Finset Copy) (coin : UnrankedBlockAtNode v keep H.hybrid → Bool) : UnrankedView V E Copy where
  genealogy := v.genealogy
  population x := if h : x ∈ keep ∧ v.population x = some (.node H.hybrid) then
    some (.edge (H.parent (coin ⟨optionTreeLeaves (v.genealogy x),
      Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩))) else v.population x
  register := v.register

theorem actual_unranked_projected_pulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy) (keep : Finset Copy)
    (coin : ViewBlockAtNode v keep H.hybrid → Bool) :
    unrankedView (projectedPulse H v keep coin) =
      unrankedProjectedPulse H (unrankedView v) keep (unrankedBlockCoin v keep H.hybrid coin) := by
  apply UnrankedView.ext
  · rfl
  · funext x
    change (if h : x ∈ keep ∧ v.population x = some (.node H.hybrid) then _ else _) = _
    unfold unrankedProjectedPulse
    dsimp only [unrankedView]
    split_ifs with hx
    · apply congrArg (fun bit => some (Location.edge (H.parent bit)))
      apply congrArg coin
      apply Subtype.ext
      exact (optionUnranked_leaves (v.genealogy x)).symm
    · rfl
  · rfl

theorem original_unranked_coin_measurePreserving (v : SelectedView V E Copy)
    (keep : Finset Copy) (node : V) (gamma : unitInterval) :
    MeasurePreserving (unrankedBlockCoin v keep node)
      (independentCoinMeasure (ViewBlockAtNode v keep node) gamma)
      (independentCoinMeasure (UnrankedBlockAtNode (unrankedView v) keep node) gamma) := by
  have he : (⇑(MeasurableEquiv.piCongrLeft
      (fun _ : UnrankedBlockAtNode (unrankedView v) keep node => Bool)
      (originalUnrankedBlockEquiv v keep node))) = unrankedBlockCoin v keep node := by
    funext c A
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,unrankedBlockCoin]
  have h := measurePreserving_piCongrLeft
    (fun _ : UnrankedBlockAtNode (unrankedView v) keep node => bitMeasure gamma)
    (originalUnrankedBlockEquiv v keep node)
  rw [he] at h
  exact h

local instance rawViewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤
local instance unrankedViewMeasurable : MeasurableSpace (UnrankedView V E Copy) := ⊤

noncomputable def unrankedPulseLaw {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : UnrankedView V E Copy)
    (keep : Finset Copy) (gamma : unitInterval) : Measure (UnrankedView V E Copy) :=
  (independentCoinMeasure (UnrankedBlockAtNode v keep H.hybrid) gamma).map
    (unrankedProjectedPulse H v keep)

/-- Exact CURRENT-block iid coin law and complete output on the UNRANKED
interface are derived by a true product-measure reindexing. -/
theorem actual_unranked_private_pulse_law {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) (gamma : unitInterval) :
    (selectedPulseLaw H v keep gamma).map unrankedView =
      unrankedPulseLaw H (unrankedView v) keep gamma := by
  have hp := original_unranked_coin_measurePreserving v keep H.hybrid gamma
  have hout : Measurable (unrankedProjectedPulse H (unrankedView v) keep) := measurable_of_countable _
  have hfun : unrankedView ∘ projectedPulse H v keep =
      unrankedProjectedPulse H (unrankedView v) keep ∘ unrankedBlockCoin v keep H.hybrid := by
    funext coin
    exact actual_unranked_projected_pulse H v keep coin
  unfold selectedPulseLaw unrankedPulseLaw
  rw [Measure.map_map measurable_from_top (measurable_of_countable _),hfun,
    ← Measure.map_map hout hp.measurable,hp.map_eq]

/-- GENUINE actual original-source private boundary law factors through
the exact rooted unranked view, with every original clade/population retained. -/
theorem actual_source_unranked_private_boundary_measure (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (s : Code N sample) (keep : Finset Copy) :
    ((independentPulseKernel H gamma s).map (fun d => unrankedView (selectedView (state d) keep))).toMeasure =
      unrankedPulseLaw H (unrankedView (selectedView (state s) keep)) keep gamma := by
  change ((independentPulseKernel H gamma s).map (unrankedView ∘ fun d => selectedView (state d) keep)).toMeasure = _
  rw [← PMF.map_comp,← PMF.toMeasure_map _ _ measurable_from_top,
    independent_pulse_kernel_view_measure,actual_unranked_private_pulse_law]

#print axioms actual_source_unranked_private_boundary_measure
end G1UnrankedNaturalPulse
