import G1JointForestPreservation

/-!
# Original whole-forest joint exterior replacement

Contributor: dot, 2026-10-03. Only CURRENT entering component roots are capped.
All already-formed original trees are grafted back, while arbitrarily many
exterior roots follow their actual independent original-source program.
Arbitrary entering history/register correlations and later interaction are
retained by pointwise conditioning and subsequent PMF bind.
-/
namespace G1ActualJointOpaqueContext
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open G1JointSeparatedSourceGeometry G1ActualJointGenerator G1ActualJointEpoch G1ActualJointBoundary
open G1ActualJointProgram G1ActualCurrentPanelInitialization G1JointUnrankedForestAssembly G1JointForestPreservation
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma independentProduct_map {A B C D : Type*} (p : PMF A) (q : PMF B)
    (f : A → C) (g : B → D) :
    (independentProduct p q).map (fun v => (f v.1,g v.2)) =
      independentProduct (p.map f) (q.map g) := by
  simp only [independentProduct,PMF.map_bind,PMF.bind_map,PMF.map_comp,Function.comp_def]

noncomputable def currentPanelProgramLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (keep : Finset Copy) (hkeep : keep ⊆ (state s).live) : PMF (SelectedView V E Copy) :=
  (sourceProgram N r ops (currentPanelCode N s keep hkeep)).map
    (fun d => liftView keep (selectedView (state d) Finset.univ))

/-- The actual smaller panel has its own copy-dependent uniformization bound;
its original rates/operations and SAME entering register are unchanged. -/
theorem actual_current_panel_program_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (keep : Finset Copy) (hkeep : keep ⊆ (state s).live) :
    (sourceProgram N r ops s).map (fun d => selectedView (state d) keep) =
      currentPanelProgramLaw N r ops s keep hkeep := by
  have h := congrArg (fun p : PMF (JoinedIndex N sample keep) => p.map Subtype.val)
    (actual_cross_carrier_program_law N r keep ops s (currentPanelCode N s keep hkeep)
      (actual_current_panel_initialization N s keep hkeep))
  simpa [currentPanelProgramLaw,PMF.map_comp,Function.comp_def,joinedProjection,joinedView] using h

/-- BOTH components are independently initialized true current-root sources.
The full larger-source JOINT law is derived, including original label lift. -/
theorem actual_joint_smaller_current_sources (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hi : inside ⊆ (state s).live) (ho : outside ⊆ (state s).live)
    (hagenda : SeparatedAgenda N r inside outside ops s) :
    (sourceProgram N r ops s).map (fun d =>
        (selectedView (state d) inside,selectedView (state d) outside)) =
      independentProduct (currentPanelProgramLaw N r ops s inside hi)
        (currentPanelProgramLaw N r ops s outside ho) := by
  have h := congrArg (fun p : PMF (JointIndex N sample inside outside) =>
      p.map (fun v => (v.1.val,v.2.val)))
    (actual_separated_joint_program_law N r inside outside ops s hagenda)
  rw [independentProduct_map] at h
  simp only [PMF.map_comp,Function.comp_def,jointProjection] at h
  rw [← actual_source_program_projection N r inside ops s,
    ← actual_source_program_projection N r outside ops s] at h
  simp only [PMF.map_comp,Function.comp_def,projection] at h
  rw [actual_current_panel_program_law N r ops s inside hi,
    actual_current_panel_program_law N r ops s outside ho] at h
  exact h

noncomputable def assembledOriginalForest (input : Copy → Genealogy Copy)
    (v : SelectedView V E Copy × SelectedView V E Copy) : Finset (UnrankedTree Copy) :=
  (unrankedForest v.1 ∪ unrankedForest v.2).image (graftUnranked input)

/-- Every original carried descendant-labelled tree is restored from the
CURRENT-root component/exterior forests, including empty panels. -/
theorem actual_joint_whole_original_forest (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hpart : inside ∪ outside = (state s).live)
    (hdis : Disjoint inside outside) (hagenda : SeparatedAgenda N r inside outside ops s)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    rootForest N d = assembledOriginalForest (state s).genealogy
      (selectedView (state d) inside,selectedView (state d) outside) := by
  rw [actual_whole_forest_reconstruction N (state s).genealogy (state s).live d
    (actual_program_reconstruction_support N r ops s hd),← hpart]
  rw [actual_pruned_forest_union (state d) d.property.forest inside outside
    (actual_agenda_pruned_panel_separation N r inside outside ops s hagenda
      (current_root_partition_pure (state s) s.property.forest inside outside hpart hdis) hd)]
  rfl

/-- Complete rooted UNRANKED original forest law in the actual larger source.
There is NO original-descendant/exterior carrier bound; only inside.card is
the component input-root count. No target law is supplied as a premise. -/
theorem actual_joint_original_forest_kernel_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hpart : inside ∪ outside = (state s).live)
    (hdis : Disjoint inside outside) (hagenda : SeparatedAgenda N r inside outside ops s) :
    (sourceProgram N r ops s).map (rootForest N) =
      (independentProduct
        (currentPanelProgramLaw N r ops s inside (hpart ▸ Finset.subset_union_left))
        (currentPanelProgramLaw N r ops s outside (hpart ▸ Finset.subset_union_right))).map
          (assembledOriginalForest (state s).genealogy) := by
  rw [← actual_joint_smaller_current_sources N r inside outside ops s
    (hpart ▸ Finset.subset_union_left) (hpart ▸ Finset.subset_union_right) hagenda,PMF.map_comp]
  apply map_eq_of_eq_on_support
  intro d hd
  exact actual_joint_whole_original_forest N r inside outside ops s hpart hdis hagenda hd

/-- An arbitrary SAME-register/full-forest/exterior-state continuation may
couple the components again after their interface. Entering history is kept
as its exact conditioned value; it is never replaced by a new marginal. -/
theorem actual_joint_context_law {History Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (inside outside : Finset Copy) (ops : List (ProgramStep N)) (s : Code N sample)
    (hpart : inside ∪ outside = (state s).live) (hdis : Disjoint inside outside)
    (hagenda : SeparatedAgenda N r inside outside ops s) (history : History)
    (continuation : History → (V → Bool) → SelectedView V E Copy → SelectedView V E Copy →
      Finset (UnrankedTree Copy) → PMF Obs) :
    (sourceProgram N r ops s).bind (fun d => continuation history (state d).register
      (selectedView (state d) inside) (selectedView (state d) outside) (rootForest N d)) =
    (independentProduct
      (currentPanelProgramLaw N r ops s inside (hpart ▸ Finset.subset_union_left))
      (currentPanelProgramLaw N r ops s outside (hpart ▸ Finset.subset_union_right))).bind
        (fun v => continuation history (state s).register v.1 v.2
          (assembledOriginalForest (state s).genealogy v)) := by
  rw [← actual_joint_smaller_current_sources N r inside outside ops s
    (hpart ▸ Finset.subset_union_left) (hpart ▸ Finset.subset_union_right) hagenda,PMF.bind_map]
  apply bind_eq_of_eq_on_support
  intro d hd
  rw [actual_program_register_support N r ops s hd,
    actual_joint_whole_original_forest N r inside outside ops s hpart hdis hagenda hd]
  rfl

#print axioms actual_joint_smaller_current_sources
#print axioms actual_joint_original_forest_kernel_law
#print axioms actual_joint_context_law

/-- Correlated original entering states, complete exterior/root histories and
exposed/shared registers are mixed using EXACTLY the same prior. Only the
future private source choices are conditionally separated by the proved law. -/
theorem actual_correlated_entering_joint_context_law {History Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (prior : PMF (History × Code N sample))
    (inside outside : Code N sample → Finset Copy)
    (hpart : ∀ a ∈ prior.support, inside a.2 ∪ outside a.2 = (state a.2).live)
    (hdis : ∀ a ∈ prior.support, Disjoint (inside a.2) (outside a.2))
    (hagenda : ∀ a ∈ prior.support, SeparatedAgenda N r (inside a.2) (outside a.2) ops a.2)
    (continuation : History → (V → Bool) → SelectedView V E Copy → SelectedView V E Copy →
      Finset (UnrankedTree Copy) → PMF Obs) :
    prior.bindOnSupport (fun a _ => (sourceProgram N r ops a.2).bind (fun d =>
      continuation a.1 (state d).register (selectedView (state d) (inside a.2))
        (selectedView (state d) (outside a.2)) (rootForest N d))) =
    prior.bindOnSupport (fun a ha => (independentProduct
      (currentPanelProgramLaw N r ops a.2 (inside a.2) ((hpart a ha) ▸ Finset.subset_union_left))
      (currentPanelProgramLaw N r ops a.2 (outside a.2) ((hpart a ha) ▸ Finset.subset_union_right))).bind
        (fun v => continuation a.1 (state a.2).register v.1 v.2
          (assembledOriginalForest (state a.2).genealogy v))) := by
  congr 1
  funext a ha
  exact actual_joint_context_law N r (inside a.2) (outside a.2) ops a.2
    (hpart a ha) (hdis a ha) (hagenda a ha) a.1 continuation

theorem actual_inside_current_carrier_cap (inside : Finset Copy) (m : Nat)
    (hcap : inside.card ≤ m) : Fintype.card (SelectedCopy inside) ≤ m := by
  simpa only [SelectedCopy,Fintype.card_coe] using hcap

#print axioms actual_correlated_entering_joint_context_law
#print axioms actual_inside_current_carrier_cap
end G1ActualJointOpaqueContext
