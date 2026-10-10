import UnifiedLean.Source.SourceCrossCarrierEpoch

/-!
# Actual CURRENT-owner small-copy pulse in original labelled coordinates

Contributor: dot, 2026-10-02. Derives the actual small live-owner/original-block
bijection and transports its real Bernoulli product measure. This supplies the
same original hybrid pulse law as the full selected source, with no copied-tip
coin redraw or assumed pulse/source-law equality.
-/
namespace UnifiedLean.Source.SourceSmallCarrierPulse
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory ProbabilityTheory
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceForestPulseTransport
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceSmallCarrierGenerator
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def smallOwnerBlock (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) (node : V) (a : AtNode s node) :
    ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep node := by
  refine ⟨liftedBlock keep s a.val,?_⟩
  rw [small_population_catalogue keep s hs (.node node)]
  exact Finset.mem_image.mpr ⟨a.val,Finset.mem_filter.mpr a.property,rfl⟩

lemma smallOwnerBlock_bijective (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) (node : V) : Function.Bijective (smallOwnerBlock keep s hs node) := by
  constructor
  · intro a b h
    exact Subtype.ext (liftedBlock_injective_live keep s hs a.property.1 b.property.1
      (congrArg Subtype.val h))
  · intro A
    have hA := A.property
    simp only [small_population_catalogue keep s hs (.node node)] at hA
    obtain ⟨a,ha,hA⟩ := Finset.mem_image.mp hA
    exact ⟨⟨a,Finset.mem_filter.mp ha⟩,Subtype.ext hA⟩

noncomputable def smallOwnerEquiv (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) (node : V) :
    AtNode s node ≃ ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep node :=
  Equiv.ofBijective _ (smallOwnerBlock_bijective keep s hs node)

noncomputable def smallInducedCoin (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) (node : V) (coin : AtNode s node → Bool) :
    ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep node → Bool :=
  fun A => coin ((smallOwnerEquiv keep s hs node).symm A)

lemma smallInducedCoin_at_owner (keep : Finset Copy) (s : State V E (SelectedCopy keep))
    (hs : Valid s) (node : V) (coin : AtNode s node → Bool) (a : AtNode s node) :
    smallInducedCoin keep s hs node coin (smallOwnerBlock keep s hs node a) = coin a := by
  change coin ((smallOwnerEquiv keep s hs node).symm ((smallOwnerEquiv keep s hs node) a)) = _
  rw [Equiv.symm_apply_apply]

/-- Whole original-labelled view commutes with the ACTUAL small-source current
owner pulse. Selected copies already in one ancestor are never split. -/
theorem small_current_owner_pulse_view {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (keep : Finset Copy)
    (s : State V E (SelectedCopy keep)) (hs : Valid s) (coin : AtNode s H.hybrid → Bool) :
    liftView keep (selectedView (pulse H s coin) Finset.univ) =
      projectedPulse H (liftView keep (selectedView s Finset.univ)) keep
        (smallInducedCoin keep s hs H.hybrid coin) := by
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep
    · let y : SelectedCopy keep := ⟨x,hx⟩
      change (liftView keep (selectedView (pulse H s coin) Finset.univ)).population y.val = _
      rw [lifted_original_population]
      by_cases hp : s.location (s.ancestor y) = .node H.hybrid
      · let a : AtNode s H.hybrid := ⟨s.ancestor y,hs.ancestor_live y,hp⟩
        have hv : y.val ∈ keep ∧
            (liftView keep (selectedView s Finset.univ)).population y.val = some (.node H.hybrid) := by
          rw [lifted_original_population]
          exact ⟨y.property,congrArg some hp⟩
        change some ((pulse H s coin).location (s.ancestor y)) =
          if h : y.val ∈ keep ∧ (liftView keep (selectedView s Finset.univ)).population y.val = some (.node H.hybrid) then _ else _
        rw [pulse_routes_current_ancestor H s coin a,dif_pos hv]
        have hA : (⟨Genealogy.optionLeaves ((liftView keep (selectedView s Finset.univ)).genealogy y.val),
            Finset.mem_image.mpr ⟨y.val,Finset.mem_filter.mpr hv,rfl⟩⟩ :
            ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep H.hybrid) =
            smallOwnerBlock keep s hs H.hybrid a := by
          apply Subtype.ext
          change Genealogy.optionLeaves ((liftView keep (selectedView s Finset.univ)).genealogy y.val) =
            liftedBlock keep s (s.ancestor y)
          rw [lifted_original_genealogy]
          exact mapLabels_leaves Subtype.val _
        rw [hA,smallInducedCoin_at_owner]
      · have hv : ¬(y.val ∈ keep ∧
            (liftView keep (selectedView s Finset.univ)).population y.val = some (.node H.hybrid)) := by
          rw [lifted_original_population]
          exact fun h => hp (Option.some.inj h.2)
        change some ((if h : s.ancestor y ∈ s.live ∧ s.location (s.ancestor y) = .node H.hybrid
          then .edge (H.parent (coin ⟨s.ancestor y,h⟩)) else s.location (s.ancestor y))) = _
        rw [dif_neg (fun h => hp h.2)]
        change some (copyLocation s y) =
          if h : y.val ∈ keep ∧ (liftView keep (selectedView s Finset.univ)).population y.val = some (.node H.hybrid) then _ else _
        rw [dif_neg hv]
        exact (lifted_original_population keep s y).symm
    · have hv : ¬(x ∈ keep ∧ (liftView keep (selectedView s Finset.univ)).population x = some (.node H.hybrid)) :=
        fun h => hx h.1
      simp [liftView,projectedPulse,hx,hv]
  · rfl

/-- Standard product-law reindexing uses the DERIVED actual small current-owner
bijection. There is no assumed independent small/source observation law. -/
theorem small_current_coin_measurePreserving (keep : Finset Copy)
    (s : State V E (SelectedCopy keep)) (hs : Valid s) (node : V) (gamma : unitInterval) :
    MeasurePreserving (smallInducedCoin keep s hs node)
      (independentCoinMeasure (AtNode s node) gamma)
      (independentCoinMeasure (ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep node) gamma) := by
  have h := measurePreserving_piCongrLeft
    (fun _ : ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep node => bitMeasure gamma)
    (smallOwnerEquiv keep s hs node)
  have he : (⇑(MeasurableEquiv.piCongrLeft
      (fun _ : ViewBlockAtNode (liftView keep (selectedView s Finset.univ)) keep node => Bool)
      (smallOwnerEquiv keep s hs node))) = smallInducedCoin keep s hs node := by
    funext c A
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply,smallInducedCoin]
  rw [he] at h
  exact h

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

/-- Actual small-source Bernoulli pulse output is exactly the SAME intrinsic
original-labelled selected pulse measure as the full source. -/
theorem small_original_pulse_law {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (keep : Finset Copy)
    (s : State V E (SelectedCopy keep)) (hs : Valid s) (gamma : unitInterval) :
    (independentCoinMeasure (AtNode s H.hybrid) gamma).map
      (fun c => liftView keep (selectedView (pulse H s c) Finset.univ)) =
      selectedPulseLaw H (liftView keep (selectedView s Finset.univ)) keep gamma := by
  let c := smallInducedCoin keep s hs H.hybrid
  let out := projectedPulse H (liftView keep (selectedView s Finset.univ)) keep
  have hc : Measurable c := (small_current_coin_measurePreserving keep s hs H.hybrid gamma).measurable
  have ho : Measurable out := measurable_of_countable out
  have he : (fun coin => liftView keep (selectedView (pulse H s coin) Finset.univ)) = out ∘ c := by
    funext coin
    exact small_current_owner_pulse_view H keep s hs coin
  rw [he,← Measure.map_map ho hc,(small_current_coin_measurePreserving keep s hs H.hybrid gamma).map_eq]
  rfl

#print axioms small_current_owner_pulse_view
#print axioms small_current_coin_measurePreserving
#print axioms small_original_pulse_law
end UnifiedLean.Source.SourceSmallCarrierPulse
