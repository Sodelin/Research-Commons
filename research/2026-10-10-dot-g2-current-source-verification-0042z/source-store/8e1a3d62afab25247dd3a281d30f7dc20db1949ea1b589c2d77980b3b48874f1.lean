import UnifiedLean.Source.SourceForestIntrinsicGenerator
import G2LiveLineageRouting

/-!
# Original-current-root pulse transported to the intrinsic selected view

Contributor: dot, 2026-10-02. The visible owner/block correspondence is derived
from the actual SourceForest invariant. Current-root coins are transported by
that equivalence; they are not assigned independently per selected original
copy. The deterministic original hybrid pulse commutes with whole-genealogy,
original-population and shared-register pruning. Natural Bernoulli measure
transport and calendar/continuous-time composition are subsequent gates.
-/
namespace UnifiedLean.Source.SourceForestPulseTransport
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev VisibleAtNode (s : State V E Copy) (keep : Finset Copy) (node : V) :=
  { l : AtNode s node // (selectedBlock s keep l.val).Nonempty }

abbrev ViewBlockAtNode (v : SelectedView V E Copy) (keep : Finset Copy) (node : V) :=
  { A : Finset Copy // A ∈ viewPopulationBlocks v keep (.node node) }

noncomputable def ownerToBlock (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (l : VisibleAtNode s keep node) :
    ViewBlockAtNode (selectedView s keep) keep node := by
  refine ⟨selectedBlock s keep l.val.val,?_⟩
  rw [← selected_active_blocks_eq_intrinsic s hs keep (.node node)]
  exact Finset.mem_image.mpr ⟨l.val.val,Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr l.val.property,l.property⟩,rfl⟩

lemma ownerToBlock_injective (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) :
    Function.Injective (ownerToBlock s hs keep node) := by
  intro l m h
  apply Subtype.ext
  apply Subtype.ext
  exact selectedBlock_injective_on_visible s hs keep
    (Finset.mem_filter.mpr ⟨l.val.property.1,l.property⟩)
    (Finset.mem_filter.mpr ⟨m.val.property.1,m.property⟩)
    (congrArg Subtype.val h)

lemma ownerToBlock_surjective (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) :
    Function.Surjective (ownerToBlock s hs keep node) := by
  intro A
  have hA := (Finset.ext_iff.mp (selected_active_blocks_eq_intrinsic s hs keep (.node node)) A.val).mpr A.property
  obtain ⟨l,hl,heq⟩ := Finset.mem_image.mp hA
  obtain ⟨hpop,hvis⟩ := Finset.mem_filter.mp hl
  refine ⟨⟨⟨l,Finset.mem_filter.mp hpop⟩,hvis⟩,?_⟩
  exact Subtype.ext heq

/-- The two finite coin-index sets are actually equivalent. Visible current
representatives need not lie in the selected original sample panel. -/
noncomputable def visibleOwnerEquiv (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) :
    VisibleAtNode s keep node ≃ ViewBlockAtNode (selectedView s keep) keep node :=
  Equiv.ofBijective (ownerToBlock s hs keep node)
    ⟨ownerToBlock_injective s hs keep node,ownerToBlock_surjective s hs keep node⟩

/-- Projected current-root parent pulse. Coin is indexed by the whole current
selected block, so two selected copies in one genealogy cannot split. -/
noncomputable def projectedPulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) (coin : ViewBlockAtNode v keep H.hybrid → Bool) :
    SelectedView V E Copy where
  genealogy := v.genealogy
  population x := if h : x ∈ keep ∧ v.population x = some (.node H.hybrid) then
    some (.edge (H.parent (coin ⟨Genealogy.optionLeaves (v.genealogy x),
      Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
    else v.population x
  register := v.register

noncomputable def inducedBlockCoin (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (coin : AtNode s node → Bool) :
    ViewBlockAtNode (selectedView s keep) keep node → Bool :=
  fun A => coin ((visibleOwnerEquiv s hs keep node).symm A).val

lemma inducedBlockCoin_at_owner (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (coin : AtNode s node → Bool)
    (l : VisibleAtNode s keep node) :
    inducedBlockCoin s hs keep node coin (ownerToBlock s hs keep node l) = coin l.val := by
  change coin (((visibleOwnerEquiv s hs keep node).symm
    ((visibleOwnerEquiv s hs keep node) l)).val) = _
  rw [Equiv.symm_apply_apply]

lemma original_selected_location_at_pulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (coin : AtNode s H.hybrid → Bool) {x : Copy}
    (hx : x ∈ keep) (hp : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid) :
    selectedLocation (pulse H s coin) keep x =
      some (.edge (H.parent (coin ⟨s.ancestor x,hp⟩))) := by
  rw [selectedLocation,if_pos hx]
  change some ((pulse H s coin).location (s.ancestor x)) = _
  rw [pulse_routes_current_ancestor H s coin ⟨s.ancestor x,hp⟩]

lemma original_selected_location_outside_pulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (keep : Finset Copy) (coin : AtNode s H.hybrid → Bool) {x : Copy}
    (hx : x ∈ keep) (hp : ¬(s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid)) :
    selectedLocation (pulse H s coin) keep x = selectedLocation s keep x := by
  rw [selectedLocation,if_pos hx,selectedLocation,if_pos hx]
  change some ((if h : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid
    then .edge (H.parent (coin ⟨s.ancestor x,h⟩)) else s.location (s.ancestor x))) = _
  rw [dif_neg hp]
  rfl

/-- Exact commutation for the EXISTING original source pulse. The induced
coin map is constructed, rather than a desired pulse law supplied as a field. -/
theorem original_pulse_selected_view {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (coin : AtNode s H.hybrid → Bool) :
    selectedView (pulse H s coin) keep = projectedPulse H (selectedView s keep) keep
      (inducedBlockCoin s hs keep H.hybrid coin) := by
  apply SelectedView.ext
  · rfl
  · funext x
    change selectedLocation (pulse H s coin) keep x = _
    by_cases hx : x ∈ keep
    · by_cases hn : s.location (s.ancestor x) = .node H.hybrid
      · have hp : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid :=
          ⟨hs.ancestor_live x,hn⟩
        let l : VisibleAtNode s keep H.hybrid :=
          ⟨⟨s.ancestor x,hp⟩,⟨x,(selectedBlock_eq_fiber s hs keep hp.1 x).mpr ⟨hx,rfl⟩⟩⟩
        have hv : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) := by
          simp [selectedView,selectedLocation,copyLocation,hx,hn]
        rw [original_selected_location_at_pulse H s hs keep coin hx hp]
        change some (.edge (H.parent (coin ⟨s.ancestor x,hp⟩))) =
          (if h : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) then
            some (.edge (H.parent (inducedBlockCoin s hs keep H.hybrid coin
              ⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
                Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
          else (selectedView s keep).population x)
        rw [dif_pos hv]
        have hA : (⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
            Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr hv,rfl⟩⟩ :
            ViewBlockAtNode (selectedView s keep) keep H.hybrid) =
            ownerToBlock s hs keep H.hybrid l := by
          apply Subtype.ext
          exact selected_view_block_leaves s keep hx
        rw [hA,inducedBlockCoin_at_owner]
      · have hp : ¬(s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid) :=
          fun h => hn h.2
        have hv : ¬(x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid)) := by
          simp only [selectedView,selectedLocation,if_pos hx,copyLocation]
          intro h
          exact hn (Option.some.inj h.2)
        rw [original_selected_location_outside_pulse H s keep coin hx hp]
        change (selectedView s keep).population x =
          (if h : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) then
            some (.edge (H.parent (inducedBlockCoin s hs keep H.hybrid coin
              ⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
                Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
          else (selectedView s keep).population x)
        rw [dif_neg hv]
    · have hv : ¬(x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid)) :=
        fun h => hx h.1
      change selectedLocation (pulse H s coin) keep x =
        (if h : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) then
          some (.edge (H.parent (inducedBlockCoin s hs keep H.hybrid coin
            ⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
              Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
        else (selectedView s keep).population x)
      rw [dif_neg hv]
      simp only [selectedView,selectedLocation,if_neg hx]
  · rfl

#print axioms ownerToBlock_injective
#print axioms ownerToBlock_surjective
#print axioms inducedBlockCoin_at_owner
#print axioms original_pulse_selected_view
end UnifiedLean.Source.SourceForestPulseTransport
