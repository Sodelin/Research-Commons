import G7PopulationPanelPolynomial
import ActualPopulationPanelSplit

/-! Deterministic full selected-forest reassembly of the inherited conditional
population/exterior product. All factors retain the same original register. -/
namespace GProgram.G7.PopulationForestReassembly
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G7.WholeAncestorPanelCode
open G1ActualJointEpoch G1ActualJointGenerator G1NonrootBigonKernel
open DotG6.ActualPopulationPanelSplit
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def joinViews (keep : Finset Copy) (a b : SelectedView V E Copy) :
    SelectedView V E Copy where
  genealogy x := if x ∈ keep then a.genealogy x else b.genealogy x
  population x := if x ∈ keep then a.population x else b.population x
  register := a.register

lemma closed_complement (s : State V E Copy) (keep : Finset Copy)
    (hc : AncestorClosed s keep) : AncestorClosed s (Finset.univ \ keep) := by
  intro x
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
  exact not_congr (hc x)

lemma selected_genealogy_whole (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hc : AncestorClosed s keep) {x : Copy} (hx : x ∈ keep) :
    (selectedView s keep).genealogy x = some (s.genealogy (s.ancestor x)) := by
  change (if x ∈ keep then (s.genealogy (s.ancestor x)).prune keep else none) = _
  rw [if_pos hx]
  exact prune_whole keep _ (live_tree_subset s hs keep hc
    ⟨s.ancestor x,(hc x).mp hx⟩ (hs.ancestor_live x))

lemma full_view_reassembly (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hc : AncestorClosed s keep) :
    selectedView s Finset.univ = joinViews keep (selectedView s keep)
      (selectedView s (Finset.univ \ keep)) := by
  apply SelectedView.ext
  · funext x
    have hall : AncestorClosed s Finset.univ := fun _ => by simp
    rw [selected_genealogy_whole s hs _ hall (Finset.mem_univ x)]
    change _ = if x ∈ keep then _ else _
    by_cases hx : x ∈ keep
    · rw [if_pos hx,selected_genealogy_whole s hs keep hc hx]
    · rw [if_neg hx,selected_genealogy_whole s hs _ (closed_complement s keep hc)
        (by simp [hx])]
  · funext x
    by_cases hx : x ∈ keep <;>
      simp [joinViews,selectedView,selectedLocation,hx]
  · rfl

lemma map_eq_on_support {A B : Type*} [Fintype A] (p : PMF A) (f g : A → B)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply,PMF.map_apply,tsum_fintype,tsum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa [PMF.mem_support_iff] using ha
    simp [hz]

lemma epoch_panel_closed (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (place : Location V E)
    {d : Code N sample} (hd : d ∈ (sourceTimeKernel N r t s).support) :
    AncestorClosed (state d) (populationPanel (state s) place) := by
  have he : populationPanel (state s) place = locationPanel (state d) place := by
    ext x
    simp only [populationPanel,locationPanel,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [actual_time_copy_population N r t s hd x]
  rw [he]
  exact locationPanel_closed (state d) d.property.forest place

theorem actual_full_forest_population_product (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (s : Code N sample) (place : Location V E) :
    (sourceTimeKernel N r t s).map (fun d => selectedView (state d) Finset.univ) =
      (independentProduct
        ((sourceTimeKernel N r t s).map (projection N (populationPanel (state s) place)))
        ((sourceTimeKernel N r t s).map (projection N (exteriorPanel (state s) place)))).map
        (fun ab => joinViews (populationPanel (state s) place) ab.1.val ab.2.val) := by
  rw [← actual_population_epoch_product N r t s place,PMF.map_comp]
  apply map_eq_on_support
  intro d hd
  exact full_view_reassembly (state d) d.property.forest _
    (epoch_panel_closed N r t s place hd)

theorem actual_panel_view_epoch (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (keep : Finset Copy)
    (hc : AncestorClosed (state s) keep) :
    (sourceTimeKernel N r t s).map (fun d => selectedView (state d) keep) =
      (sourceTimeKernel N r t (panelCode N s keep hc)).map
        (fun d => liftView keep (selectedView (state d) Finset.univ)) := by
  have h := congrArg (fun p : PMF (JoinedIndex N sample keep) => p.map Subtype.val)
    (actual_panel_epoch N r s keep hc t)
  simpa [PMF.map_comp,joinedProjection,joinedView,Function.comp_def] using h

lemma independentProduct_map {A B C D : Type*} (p : PMF A) (q : PMF B)
    (f : A → C) (g : B → D) :
    independentProduct (p.map f) (q.map g) =
      (independentProduct p q).map (fun ab => (f ab.1,g ab.2)) := by
  simp [independentProduct,PMF.bind_map,PMF.map_bind,PMF.map_comp,Function.comp_def]

theorem actual_full_forest_view_product (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (s : Code N sample) (place : Location V E) :
    (sourceTimeKernel N r t s).map (fun d => selectedView (state d) Finset.univ) =
      (independentProduct
        ((sourceTimeKernel N r t s).map (fun d => selectedView (state d) (populationPanel (state s) place)))
        ((sourceTimeKernel N r t s).map (fun d => selectedView (state d) (exteriorPanel (state s) place)))).map
        (fun ab => joinViews (populationPanel (state s) place) ab.1 ab.2) := by
  have h := actual_full_forest_population_product N r t s place
  simpa [independentProduct,PMF.bind_map,PMF.map_bind,PMF.map_comp,projection,Function.comp_def] using h

theorem actual_smaller_source_reassembly (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (s : Code N sample) (place : Location V E) :
    let keep := populationPanel (state s) place
    let hc : AncestorClosed (state s) keep :=
      locationPanel_closed (state s) s.property.forest place
    (sourceTimeKernel N r t s).map (fun d => selectedView (state d) Finset.univ) =
      (independentProduct
        ((sourceTimeKernel N r t (panelCode N s keep hc)).map
          (fun d => selectedView (state d) Finset.univ))
        ((sourceTimeKernel N r t (panelCode N s (Finset.univ \ keep)
          (closed_complement (state s) keep hc))).map
          (fun d => selectedView (state d) Finset.univ))).map
        (fun ab => joinViews keep (liftView keep ab.1) (liftView (Finset.univ \ keep) ab.2)) := by
  dsimp only
  let keep := populationPanel (state s) place
  have hc : AncestorClosed (state s) keep :=
    locationPanel_closed (state s) s.property.forest place
  rw [actual_full_forest_view_product N r t s place]
  change (independentProduct
    ((sourceTimeKernel N r t s).map (fun d => selectedView (state d) keep))
    ((sourceTimeKernel N r t s).map (fun d => selectedView (state d) (Finset.univ \ keep)))).map _ = _
  rw [actual_panel_view_epoch N r t s keep hc,
    actual_panel_view_epoch N r t s _ (closed_complement (state s) keep hc)]
  simp [independentProduct,PMF.bind_map,PMF.map_bind,PMF.map_comp,Function.comp_def,keep]

end GProgram.G7.PopulationForestReassembly
