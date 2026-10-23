import G3CurrentRootExchangeability
import G1NonrootBigonKernel

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
Bind the exact whole-root forest observer to the already existing smaller
current-root/bigon kernel. The complete numerical cap3 row derivation is
HAND in G3-ACTUAL-BIGON-CAP3-ROW.md, not an elaborated theorem here.
-/
namespace G3CurrentRootForestReceiver
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open G1ContextualForestReplacement G1OriginalCurrentRootReconstruction G1NonrootBigonKernel
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCrossCarrierEpoch UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceUnrankedCopyProjectivity
open G3CurrentRootExchangeability
open scoped Classical

variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The existing full-panel pruned observer and the actual rootForest are
equal on every source-valid Code, not merely on a supplied terminal row. -/
theorem full_source_forest_eq_rootForest (N : RootedBinary V E X)
    (sample : Copy → X) (s : Code N sample) :
    sourceUnrankedForest (state s) Finset.univ = rootForest N s := by
  ext q
  constructor
  · intro hq
    obtain ⟨x,_,t,ht,htq⟩ :=
      (mem_sourceUnrankedForest (state s) Finset.univ q).mp hq
    rw [full_prune] at ht
    have hg : (state s).genealogy ((state s).ancestor x) = t := Option.some.inj ht
    refine Finset.mem_image.mpr
      ⟨(state s).ancestor x,s.property.forest.ancestor_live x,?_⟩
    rw [hg]
    exact htq
  · intro hq
    obtain ⟨l,hl,htq⟩ := Finset.mem_image.mp hq
    apply (mem_sourceUnrankedForest (state s) Finset.univ q).mpr
    refine ⟨l,Finset.mem_univ _,(state s).genealogy l,?_,htq⟩
    rw [s.property.forest.representative l hl,full_prune]

/-- Distinct live genealogies cannot become the same unranked tree: their
disjoint, nonempty original-copy fibres remain visible in treeLeaves. -/
theorem rootForest_card_eq_liveCard (N : RootedBinary V E X)
    (sample : Copy → X) (s : Code N sample) : (rootForest N s).card = liveCard s := by
  change ((state s).live.image (fun l => toUnranked ((state s).genealogy l))).card =
    (state s).live.card
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  have hl := congrArg treeLeaves he
  change ((state s).genealogy a).leaves = ((state s).genealogy b).leaves at hl
  have haa : a ∈ ((state s).genealogy a).leaves :=
    (s.property.forest.leaf_fiber a ha a).mpr (s.property.forest.representative a ha)
  have hab : a ∈ ((state s).genealogy b).leaves := hl ▸ haa
  exact (s.property.forest.representative a ha).symm.trans
    ((s.property.forest.leaf_fiber b hb a).mp hab)

theorem smallerCurrentRootKernel_eq_enteringForestKernel (N : RootedBinary V E X)
    (sample : Copy → X) (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    smallerCurrentRootKernel N r ops s place hplace =
      enteringForestKernel N (selectedSample sample (state s).live) place
        (current_root_descendant N s place hplace) r ops (state s).register := by
  simp only [smallerCurrentRootKernel,actualCurrentRootCode,enteringForestKernel,sourceForestKernel]
  congr 1
  funext d
  exact full_source_forest_eq_rootForest N _ d

/-- Actual existing K, not only a new spelling of the singleton-root law. -/
theorem actual_smaller_current_root_exchangeable (N : RootedBinary V E X)
    (sample : Copy → X) (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (e : SelectedCopy (state s).live ≃ SelectedCopy (state s).live)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (smallerCurrentRootKernel N r ops s place hplace).map (copyForest e) =
      smallerCurrentRootKernel N r ops s place hplace := by
  rw [smallerCurrentRootKernel_eq_enteringForestKernel]
  exact actual_entering_forest_exchangeable N e (selectedSample sample (state s).live)
    place (state s).register (current_root_descendant N s place hplace) r ops

theorem actual_bigon_current_kernel_exchangeable (N : RootedBinary V E X)
    (sample : Copy → X) (s : Code N sample) (C : GProgram.G5.Calendar N.graph)
    (r : PositivePairRates E) (B : NonrootBigon N) (gamma : unitInterval) (common : Bool)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (e : SelectedCopy (state s).live ≃ SelectedCopy (state s).live) :
    (bigonCurrentKernel N C r B gamma common s hinput).map (copyForest e) =
      bigonCurrentKernel N C r B gamma common s hinput :=
  actual_smaller_current_root_exchangeable N sample s (.node B.parents.hybrid) hinput e r
    (bigonProgram N C B gamma common)

theorem actual_entering_ancestor (N : RootedBinary V E X) (sample : Copy → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ x, DescendsTo N place (sample x)) (x : Copy) :
    (state (enteringCode N sample place register descendant)).ancestor x = x := rfl

theorem actual_entering_location (N : RootedBinary V E X) (sample : Copy → X)
    (place : Location V E) (register : V → Bool)
    (descendant : ∀ x, DescendsTo N place (sample x)) (x : Copy) :
    (state (enteringCode N sample place register descendant)).location x = place :=
  decode_encode_live_population N.root _ (enteringState_valid place register) (Finset.mem_univ x)

/-- Literal field proof for ANY selected input-root panel, including a pair.
The source comparison is not given a desired initial-view equality. -/
theorem actual_entering_selected_initialization (N : RootedBinary V E X)
    (sample : Copy → X) (place : Location V E) (register : V → Bool)
    (descendant : ∀ x, DescendsTo N place (sample x)) (keep : Finset Copy) :
    selectedView (state (enteringCode N sample place register descendant)) keep =
      liftView keep (selectedView (state (enteringCode N (selectedSample sample keep)
        place register (fun x => descendant x.val))) Finset.univ) := by
  let s := enteringCode N sample place register descendant
  let z := enteringCode N (selectedSample sample keep) place register (fun x => descendant x.val)
  change selectedView (state s) keep = liftView keep (selectedView (state z) Finset.univ)
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · let l : SelectedCopy keep := ⟨x,hx⟩
      have hh := lifted_original_genealogy keep (state z) l
      change selectedGenealogy (state s) keep l.val = _
      rw [hh,selectedGenealogy,if_pos hx]
      rw [actual_entering_ancestor,actual_entering_ancestor,
        enteringCode_genealogy,enteringCode_genealogy]
      simp only [Genealogy.prune,hx,ite_true,mapLabels]
    · simp only [selectedView,selectedGenealogy,if_neg hx,liftView,dif_neg hx]
  · funext x
    by_cases hx : x ∈ keep
    · let l : SelectedCopy keep := ⟨x,hx⟩
      have hh := lifted_original_population keep (state z) l
      change selectedLocation (state s) keep l.val = _
      rw [hh,selectedLocation,if_pos hx]
      simp only [copyLocation,actual_entering_ancestor,actual_entering_location]
    · simp only [selectedView,selectedLocation,if_neg hx,liftView,dif_neg hx]
  · rfl

/-- Actual SAME-word selected forest law, from the literal enteringCode.
The existing cross-carrier source theorem handles distinct full/small
uniformization constants; no equality of those clocks is asserted here. -/
theorem actual_entering_unranked_copy_projectivity (N : RootedBinary V E X)
    (sample : Copy → X) (place : Location V E) (register : V → Bool)
    (descendant : ∀ x, DescendsTo N place (sample x)) (keep : Finset Copy)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    (sourceProgram N r ops (enteringCode N sample place register descendant)).map
        (fun d => sourceUnrankedForest (state d) keep) =
      ((sourceProgram N r ops (enteringCode N (selectedSample sample keep)
          place register (fun x => descendant x.val))).map (rootForest N)).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
  have h := congrArg (fun law : PMF (JoinedIndex N sample keep) =>
      law.map (fun v => unrankedForest v.val))
    (actual_cross_carrier_program_law N r keep ops
      (enteringCode N sample place register descendant)
      (enteringCode N (selectedSample sample keep) place register (fun x => descendant x.val))
      (actual_entering_selected_initialization N sample place register descendant keep))
  simp only [PMF.map_comp,Function.comp_def,joinedProjection,joinedView] at h
  simp_rw [actual_small_unranked_label_lift,full_source_forest_eq_rootForest] at h
  rw [PMF.map_comp]
  exact h

#print axioms full_source_forest_eq_rootForest
#print axioms rootForest_card_eq_liveCard
#print axioms actual_smaller_current_root_exchangeable
#print axioms actual_bigon_current_kernel_exchangeable
#print axioms actual_entering_selected_initialization
#print axioms actual_entering_unranked_copy_projectivity
end G3CurrentRootForestReceiver
