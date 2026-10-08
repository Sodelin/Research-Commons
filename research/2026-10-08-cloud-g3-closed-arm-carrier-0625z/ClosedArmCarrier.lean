import UnitArmGenerator
import UnifiedLean.Source.SourceStepGeneratorBinding

/-!
Actual singleton-edge source image is closed under every visible unit graft.
Cloud G3, 2026-10-08. SOURCE-only; compiler UNCHECKED. Admission is derived
from actual original pair operands and stepDestination, not a law field.
This is a carrier closure ingredient, not yet an exp(lambda*K) PMF theorem.
-/
namespace CloudG3.ClosedArmCarrier
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open UnifiedLean.Source.SourceStepGeneratorBinding
open G1OriginalEpochPanelSilence CloudG3.UnitArmGenerator
open scoped Classical
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- A visible unit graft has an ACTUAL original edge-merger operand and
admitted destination at that SAME edge, preserving arbitrary outside roots.
The selected graft and singleton-edge support are both derived. -/
theorem actual_edge_visible_graft_destination (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (keep : Finset Copy) (e : E)
    (hs : AtEdgePanel (state s) keep {e}) (p : Finset Copy × Finset Copy)
    (hp : p ∈ (forestBlocks (selectedView (state s) keep) keep).offDiag) :
    ∃ pc : Choice N s, pc.1 = some e ∧
      AtEdgePanel (state (stepDestination N s (some pc))) keep {e} ∧
      selectedView (state (stepDestination N s (some pc))) keep =
        projectedMerge (selectedView (state s) keep) p.1 p.2 := by
  have hv : ∀ x ∈ keep, (selectedView (state s) keep).population x = some (.edge e) := by
    intro x hx
    obtain ⟨f,hf,hpop⟩ := hs x hx
    have hfe : f = e := Finset.mem_singleton.mp hf
    simpa only [selectedView,selectedLocation,if_pos hx,hpop,hfe]
  have hcat : selectedActiveBlocks (state s) keep (populationRoots (state s) (.edge e)) =
      forestBlocks (selectedView (state s) keep) keep := by
    rw [selected_active_blocks_eq_intrinsic (state s) s.property.forest keep,
      actual_single_edge_blocks (selectedView (state s) keep) keep e hv,if_pos rfl]
  have hp' : p ∈ (selectedActiveBlocks (state s) keep
      (populationRoots (state s) (.edge e))).offDiag := by rw [hcat]; exact hp
  obtain ⟨q,hq,_⟩ := edge_projected_pair_has_unique_legal_preimage
    (state s) s.property.forest keep e p hp'
  have hqpop : q ∈ (populationRoots (state s) (.edge e)).offDiag :=
    visible_offDiag_subset (state s) keep (populationRoots (state s) (.edge e)) hq.1
  let pc : Choice N s := ⟨some e,⟨q,by simpa only [originalPlace] using hqpop⟩⟩
  have hview : selectedView (state (stepDestination N s (some pc))) keep =
      projectedMerge (selectedView (state s) keep) p.1 p.2 := by
    rw [merged_destination_selectedView N s keep pc]
    have hA := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hq.1).1).2
    have hB := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hq.1).2.1).2
    rw [selectedView_merge_visible (state s) s.property.forest keep hq.2.2 hA hB]
    have heq := hq.2.1
    change (selectedBlock (state s) keep q.1,selectedBlock (state s) keep q.2) = p at heq
    rw [congrArg Prod.fst heq,congrArg Prod.snd heq]
  refine ⟨pc,rfl,?_,hview⟩
  intro x hx
  have hpop := congrArg (fun v : SelectedView V E Copy => v.population x) hview
  simp only [selectedView,projectedMerge,selectedLocation,if_pos hx] at hpop
  have hpedge : copyLocation (state (stepDestination N s (some pc))) x = .edge e := by
    obtain ⟨f,hf,hfpop⟩ := hs x hx
    have hfe : f = e := Finset.mem_singleton.mp hf
    exact (Option.some.inj hpop).trans (by simpa only [hfe] using hfpop)
  exact ⟨e,Finset.mem_singleton_self e,hpedge⟩

/-- Actual finite ORIGINAL Codes with a selected singleton-edge panel. The
edge witness is allowed to vary; this avoids transporting hidden outside owners
to a common artificial reference edge. -/
abbrev SingleEdgeCode (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {s : Code N sample // ∃ e : E, AtEdgePanel (state s) keep {e}}

noncomputable instance singleEdgeCodeFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (SingleEdgeCode N sample keep) := by
  unfold SingleEdgeCode
  infer_instance

/-- One finite population-free ORIGINAL image across all original arm edges.
Membership is actual source admission, not a prescribed transition law. -/
abbrev ArmForestIndex (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {v : ((Copy → Option (UnifiedLean.Source.UnrankedGenealogyObservation.UnrankedTree Copy)) × (V → Bool)) //
    ∃ s : SingleEdgeCode N sample keep, forestRegister (selectedView (state s.val) keep) = v}

noncomputable def armForestProjection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : SingleEdgeCode N sample keep) : ArmForestIndex N sample keep :=
  ⟨forestRegister (selectedView (state s.val) keep),⟨s,rfl⟩⟩

noncomputable instance armForestIndexFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (ArmForestIndex N sample keep) :=
  Fintype.ofSurjective (armForestProjection N keep) (by
    intro v
    obtain ⟨s,hs⟩ := v.property
    exact ⟨s,Subtype.ext hs⟩)

/-- Every genuine positive-rate original merger choice has positive support
in the actual normalized sourceStep, not merely a source-valid destination. -/
theorem actual_merger_choice_destination_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (pc : Choice N s) :
    stepDestination N s (some pc) ∈ (sourceStep N r s).support := by
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨some pc,?_,rfl⟩
  change choicePMF N r s (some pc) ≠ 0
  intro hz
  have hm : 0 < choiceMass N r s (some pc) := by
    change 0 < (pairRate r pc.1 / 2) / globalRateBound (Copy := Copy) r
    exact div_pos (div_pos (pairRate_pos r pc.1) (by norm_num))
      (globalRateBound_positive (Copy := Copy) r)
  have hp : 0 < (choicePMF N r s (some pc)).toReal := by
    rw [choicePMF_real]
    exact hm
  rw [hz] at hp
  simpa only [ENNReal.toReal_zero] using hp

/-- Every visible graft from an actual singleton-edge witness stays in the
SAME finite ArmForestIndex image, with admission and edge support derived from
the original source pair. The matrix/normalized semigroup consumer is separate. -/
theorem actual_unit_graft_stays_in_arm_image (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : SingleEdgeCode N sample keep)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (forestBlocks (selectedView (state s.val) keep) keep).offDiag) :
    ∃ d : SingleEdgeCode N sample keep,
      forestRegister (selectedView (state d.val) keep) =
        forestRegister (projectedMerge (selectedView (state s.val) keep) p.1 p.2) := by
  obtain ⟨e,he⟩ := s.property
  obtain ⟨pc,_,hd,hview⟩ := actual_edge_visible_graft_destination N s.val keep e he p hp
  exact ⟨⟨stepDestination N s.val (some pc),⟨e,hd⟩⟩,congrArg forestRegister hview⟩

/-- Strong closure form: each visible unit graft is the readout of an actual
strictly positive supported original sourceStep outcome, in the SAME finite
singleton-edge forest image. The outside original Code remains admitted. -/
theorem actual_supported_unit_graft_in_arm_image (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : SingleEdgeCode N sample keep) (p : Finset Copy × Finset Copy)
    (hp : p ∈ (forestBlocks (selectedView (state s.val) keep) keep).offDiag) :
    ∃ d : SingleEdgeCode N sample keep, d.val ∈ (sourceStep N r s.val).support ∧
      forestRegister (selectedView (state d.val) keep) =
        forestRegister (projectedMerge (selectedView (state s.val) keep) p.1 p.2) := by
  obtain ⟨e,he⟩ := s.property
  obtain ⟨pc,_,hd,hview⟩ := actual_edge_visible_graft_destination N s.val keep e he p hp
  exact ⟨⟨stepDestination N s.val (some pc),⟨e,hd⟩⟩,
    actual_merger_choice_destination_support N r s.val pc,congrArg forestRegister hview⟩

end CloudG3.ClosedArmCarrier
