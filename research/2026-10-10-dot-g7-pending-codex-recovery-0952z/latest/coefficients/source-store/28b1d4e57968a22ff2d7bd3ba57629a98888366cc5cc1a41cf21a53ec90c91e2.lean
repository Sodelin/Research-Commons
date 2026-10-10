import UnifiedLean.Source.SourceCrossCarrierProgram
import G7SinglePopulationPolynomialKernel

/-! Actual subtype source state for a union of complete current ancestor blocks.
The original graph, sample labels and one shared register are retained. -/
namespace GProgram.G7.WholeAncestorPanelCode
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceBoundaryKernels
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def AncestorClosed (s : State V E Copy) (keep : Finset Copy) : Prop :=
  ∀ x, x ∈ keep ↔ s.ancestor x ∈ keep

noncomputable def restrictTree (keep : Finset Copy) :
    (g : Genealogy Copy) → g.leaves ⊆ keep → Genealogy (SelectedCopy keep)
  | .leaf x, h => .leaf ⟨x, h (by simp [Genealogy.leaves])⟩
  | .graft a b, h => .graft
      (restrictTree keep a (fun x hx => h (by simp [Genealogy.leaves, hx])))
      (restrictTree keep b (fun x hx => h (by simp [Genealogy.leaves, hx])))

lemma restrictTree_lift (keep : Finset Copy) (g : Genealogy Copy) (h : g.leaves ⊆ keep) :
    mapLabels Subtype.val (restrictTree keep g h) = g := by
  induction g with
  | leaf x => rfl
  | graft a b ia ib => simp only [restrictTree, mapLabels, ia, ib]

lemma mapLabels_wellLabelled_reflect {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → B) (g : Genealogy A)
    (h : (mapLabels f g).WellLabelled) : g.WellLabelled := by
  induction g with
  | leaf x => trivial
  | graft a b ia ib =>
    refine ⟨ia h.1, ib h.2.1, Finset.disjoint_left.mpr ?_⟩
    intro x ha hb
    apply Finset.disjoint_left.mp h.2.2
    · rw [mapLabels_leaves]; exact Finset.mem_image.mpr ⟨x,ha,rfl⟩
    · rw [mapLabels_leaves]; exact Finset.mem_image.mpr ⟨x,hb,rfl⟩

lemma restrictTree_valid (keep : Finset Copy) (g : Genealogy Copy)
    (h : g.leaves ⊆ keep) (hg : g.WellLabelled) :
    (restrictTree keep g h).WellLabelled := by
  apply mapLabels_wellLabelled_reflect Subtype.val
  rwa [restrictTree_lift]

lemma restrictTree_mem (keep : Finset Copy) (g : Genealogy Copy)
    (h : g.leaves ⊆ keep) (x : SelectedCopy keep) :
    x ∈ (restrictTree keep g h).leaves ↔ x.val ∈ g.leaves := by
  have hh := congrArg Genealogy.leaves (restrictTree_lift keep g h)
  rw [mapLabels_leaves] at hh
  rw [← hh]
  simp only [Finset.mem_image, Subtype.val_injective.eq_iff]
  exact ⟨fun hx => ⟨x,hx,rfl⟩,fun ⟨y,hy,he⟩ => he ▸ hy⟩

lemma live_tree_subset (s : State V E Copy) (hs : Valid s) (keep : Finset Copy)
    (hc : AncestorClosed s keep) (a : SelectedCopy keep) (ha : a.val ∈ s.live) :
    (s.genealogy a.val).leaves ⊆ keep := by
  intro x hx
  apply (hc x).mpr
  rw [(hs.leaf_fiber a.val ha x).mp hx]
  exact a.property

noncomputable def restrictState (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hc : AncestorClosed s keep) : State V E (SelectedCopy keep) where
  live := Finset.univ.filter (fun a => a.val ∈ s.live)
  ancestor x := ⟨s.ancestor x.val, (hc x.val).mp x.property⟩
  genealogy a := if ha : a.val ∈ s.live then
    restrictTree keep (s.genealogy a.val) (live_tree_subset s hs keep hc a ha)
    else .leaf a
  location a := s.location a.val
  register := s.register
  history := []

lemma restrictState_valid (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hc : AncestorClosed s keep) :
    Valid (restrictState s hs keep hc) := by
  constructor
  · intro x
    simp only [restrictState, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hs.ancestor_live x.val
  · intro a ha
    apply Subtype.ext
    exact hs.representative a.val (by simpa [restrictState] using ha)
  · intro a ha x
    have hal : a.val ∈ s.live := by simpa [restrictState] using ha
    simp only [restrictState, dif_pos hal]
    rw [restrictTree_mem]
    constructor
    · intro hx; exact Subtype.ext ((hs.leaf_fiber a.val hal x.val).mp hx)
    · intro hx; exact (hs.leaf_fiber a.val hal x.val).mpr (congrArg Subtype.val hx)
  · intro a ha
    have hal : a.val ∈ s.live := by simpa [restrictState] using ha
    simp only [restrictState, dif_pos hal]
    exact restrictTree_valid keep _ _ (hs.wellLabelled a.val hal)

noncomputable def panelCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep) :
    Code N (selectedSample sample keep) :=
  admittedCode N (selectedSample sample keep) (restrictState (state s) s.property.forest keep hc)
    ⟨restrictState_valid (state s) s.property.forest keep hc,
      fun x => s.property.original_descendant x.val⟩

lemma prune_whole (keep : Finset Copy) (g : Genealogy Copy) (h : g.leaves ⊆ keep) :
    g.prune keep = some g := by
  induction g with
  | leaf x =>
    have hx : x ∈ keep := h (by simp [Genealogy.leaves])
    simp [Genealogy.prune,hx]
  | graft a b ia ib =>
    have ha : a.leaves ⊆ keep := fun x hx => h (by simp [Genealogy.leaves,hx])
    have hb : b.leaves ⊆ keep := fun x hx => h (by simp [Genealogy.leaves,hx])
    simp [Genealogy.prune, ia ha, ib hb, Genealogy.joinPruned]

lemma restrictState_view (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hc : AncestorClosed s keep) :
    selectedView s keep = liftView keep
      (selectedView (restrictState s hs keep hc) Finset.univ) := by
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · let xx : SelectedCopy keep := ⟨x,hx⟩
      have hh := lifted_original_genealogy keep (restrictState s hs keep hc) xx
      rw [hh]
      have ha : s.ancestor x ∈ s.live := hs.ancestor_live x
      change (if x ∈ keep then (s.genealogy (s.ancestor x)).prune keep else none) = _
      rw [if_pos hx]
      simp only [restrictState, xx, dif_pos ha, restrictTree_lift]
      exact prune_whole keep _ (live_tree_subset s hs keep hc
        ⟨s.ancestor x,(hc x).mp hx⟩ ha)
    · simp [selectedView, selectedGenealogy, liftView, hx]
  · funext x
    by_cases hx : x ∈ keep
    · have hh := lifted_original_population keep (restrictState s hs keep hc) ⟨x,hx⟩
      rw [hh]
      simp [selectedView, selectedLocation, hx, copyLocation, restrictState]
    · simp [selectedView, selectedLocation, liftView, hx]
  · rfl

lemma panelCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep) :
    selectedView (state s) keep = liftView keep
      (selectedView (state (panelCode N s keep hc)) Finset.univ) := by
  change _ = liftView keep (selectedView
    (decodeSnapshot N.root (encodeSnapshot
      (restrictState (state s) s.property.forest keep hc)
      (restrictState_valid (state s) s.property.forest keep hc))) Finset.univ)
  rw [decode_encode_selectedView]
  exact restrictState_view (state s) s.property.forest keep hc

noncomputable def locationPanel (s : State V E Copy) (p : Location V E) : Finset Copy :=
  Finset.univ.filter (fun x => copyLocation s x = p)

lemma locationPanel_closed (s : State V E Copy) (hs : Valid s) (p : Location V E) :
    AncestorClosed s (locationPanel s p) := by
  intro x
  have h : s.ancestor (s.ancestor x) = s.ancestor x :=
    hs.representative _ (hs.ancestor_live x)
  simp [locationPanel, copyLocation, h]

lemma panelCode_colocated (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) :
    SinglePopulationPolynomialKernel.CoLocated N
      (panelCode N s (locationPanel (state s) (originalPlace N i))
        (locationPanel_closed (state s) s.property.forest (originalPlace N i))) i := by
  intro x
  change copyLocation (decodeSnapshot N.root (encodeSnapshot
    (restrictState (state s) s.property.forest
      (locationPanel (state s) (originalPlace N i))
      (locationPanel_closed (state s) s.property.forest (originalPlace N i)))
    (restrictState_valid (state s) s.property.forest _ _))) x = _
  rw [decode_encode_copyLocation]
  have hx : copyLocation (state s) x.val = originalPlace N i :=
    (Finset.mem_filter.mp x.property).2
  exact hx

theorem actual_panel_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hc : AncestorClosed (state s) keep) (ops : List (ProgramStep N)) :
    (sourceProgram N r ops s).map (fun d => joinedProjection N keep (.inl d)) =
      (sourceProgram N r ops (panelCode N s keep hc)).map
        (fun d => joinedProjection N keep (.inr d)) :=
  actual_cross_carrier_program_law N r keep ops s (panelCode N s keep hc)
    (panelCode_view N s keep hc)

theorem actual_panel_epoch (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (keep : Finset Copy)
    (hc : AncestorClosed (state s) keep) (t : ℝ≥0) :
    (sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inl d)) =
      (sourceTimeKernel N r t (panelCode N s keep hc)).map
        (fun d => joinedProjection N keep (.inr d)) := by
  simpa [sourceProgram,sourceProgramStep] using
    actual_panel_program N r s keep hc [.interval t]

theorem actual_population_marginal_own_rate (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i : Option E)
    (r rhat : PositivePairRates E) (t : ℝ≥0)
    (hr : pairRate r i = pairRate rhat i) :
    let keep := locationPanel (state s) (originalPlace N i)
    (sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inl d)) =
      (sourceTimeKernel N rhat t s).map (fun d => joinedProjection N keep (.inl d)) := by
  dsimp only
  let keep := locationPanel (state s) (originalPlace N i)
  have hc := locationPanel_closed (state s) s.property.forest (originalPlace N i)
  rw [actual_panel_epoch N r s keep hc t, actual_panel_epoch N rhat s keep hc t]
  rw [SinglePopulationPolynomialKernel.own_population_rate_only N
    (panelCode N s keep hc) i (panelCode_colocated N s i) r rhat t hr]

end GProgram.G7.WholeAncestorPanelCode
