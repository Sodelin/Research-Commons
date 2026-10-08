import StoppedArmOperators
import G1UnrankedSourceView

/-!
Actual ORIGINAL singleton-arm generator and population-label erasure.
Cloud G3, 2026-10-08. SOURCE-only, compiler UNCHECKED. This derives rate times
unit visible-block generator from actual original choices via the inherited
intrinsic-generator theorem. It is NOT yet an exp(lambda*K) PMF theorem:
a finite closed token quotient and rectangular exponential consumer remain.
-/
namespace CloudG3.UnitArmGenerator
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.UnrankedGenealogyObservation
open G1OriginalEpochPanelSilence G1UnrankedSourceView
open scoped Classical BigOperators
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Whole per-label rooted unranked genealogy and the SAME original register.
Only the changing population tag is forgotten, not labels, clades or old trees. -/
noncomputable def forestRegister (v : SelectedView V E Copy) :=
  (fun x => optionUnranked (v.genealogy x),v.register)

/-- CURRENT visible blocks reconstructed from actual selected genealogies. -/
noncomputable def forestBlocks (v : SelectedView V E Copy) (keep : Finset Copy) : Finset (Finset Copy) :=
  keep.image (fun x => Genealogy.optionLeaves (v.genealogy x))

/-- Functional unit-rate generator on the explicit forest/register readout.
Each unordered current-block pair occurs twice in offDiag. This is an
operator definition; no desired source row or normalization is a field. -/
noncomputable def unitForestGenerator (v : SelectedView V E Copy) (keep : Finset Copy)
    (F : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ p ∈ (forestBlocks v keep).offDiag,
    (F (forestRegister (projectedMerge v p.1 p.2)) - F (forestRegister v))

/-- The actual view's entire visible-block population catalogue is its forest
block set at the one occupied edge and EMPTY at every other population. -/
theorem actual_single_edge_blocks (v : SelectedView V E Copy) (keep : Finset Copy) (e : E)
    (hv : ∀ x ∈ keep, v.population x = some (.edge e)) (place : Location V E) :
    viewPopulationBlocks v keep place = if place = .edge e then forestBlocks v keep else ∅ := by
  unfold viewPopulationBlocks forestBlocks
  by_cases hplace : place = .edge e
  · rw [if_pos hplace]
    have hf : keep.filter (fun x => v.population x = some place) = keep := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      simpa only [hplace] using hv x hx
    rw [hf]
  · rw [if_neg hplace]
    have hf : keep.filter (fun x => v.population x = some place) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxk,hxp⟩ := Finset.mem_filter.mp hx
      have hp : place = .edge e := Option.some.inj (hxp.symm.trans (hv x hxk))
      exact hplace hp
    rw [hf,Finset.image_empty]

/-- One occupied original population has its actual rate times the SAME
unit block/graft operator; all other source populations contribute zero. -/
theorem actual_single_edge_population_generator (v : SelectedView V E Copy)
    (keep : Finset Copy) (e : E) (hv : ∀ x ∈ keep, v.population x = some (.edge e))
    (place : Location V E) (rate : ℝ)
    (F : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) → ℝ) :
    viewPopulationGenerator v keep place rate (F ∘ forestRegister) =
      if place = .edge e then rate * unitForestGenerator v keep F else 0 := by
  unfold viewPopulationGenerator
  rw [actual_single_edge_blocks v keep e hv place]
  by_cases hp : place = .edge e
  · rw [if_pos hp,if_pos hp]
    unfold unitForestGenerator
    simp only [Function.comp_apply]
    ring
  · simp [hp]

/-- Actual full ORIGINAL choices, including arbitrary outside roots, factor
through the selected arm and yield EXACTLY the positive original edge rate
multiplied by the unit forest/register generator. No fitted rate law, source
comparison, current-copy independence or desired PMF equality is a premise. -/
theorem actual_original_single_arm_generator (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (e : E) (hs : AtEdgePanel (state s) keep {e})
    (F : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) → ℝ) :
    nativeSourceGenerator N.root (state s) keep r.edge r.ancestral (F ∘ forestRegister) =
      r.edge e * unitForestGenerator (selectedView (state s) keep) keep F := by
  have hv : ∀ x ∈ keep, (selectedView (state s) keep).population x = some (.edge e) := by
    intro x hx
    obtain ⟨f,hf,hpop⟩ := hs x hx
    have hfe : f = e := Finset.mem_singleton.mp hf
    simp only [selectedView,selectedLocation,if_pos hx,hpop,hfe]
  rw [native_source_generator_intertwining N.root (state s) s.property.forest keep]
  unfold intrinsicSourceGenerator
  simp_rw [actual_single_edge_population_generator (selectedView (state s) keep) keep e hv]
  simp

/-- Population relabeling does not change any retained unranked tree or bit. -/
theorem forest_register_transport (v : SelectedView V E Copy) (f : Location V E → Location V E) :
    forestRegister (transportView v f) = forestRegister v := rfl

/-- Relabeling changes neither the block set nor the unit graft generator.
This is the exact functional intertwining needed between successive original
arm edges; the full finite token quotient/exponential proof remains separate. -/
theorem unit_generator_transport (v : SelectedView V E Copy)
    (f : Location V E → Location V E) (keep : Finset Copy)
    (F : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) → ℝ) :
    unitForestGenerator (transportView v f) keep F = unitForestGenerator v keep F := by
  unfold unitForestGenerator forestBlocks
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rfl

/-- Canonical population-free view used only to derive the rooted-unranked
functional quotient. This is a readout, not an admitted original source Code. -/
noncomputable def bareForestView (v : SelectedView V E Copy) : SelectedView V E Copy :=
  ⟨v.genealogy,fun _ => none,v.register⟩

/-- The unit operator depends on the rooted UNRANKED forest/register alone,
including invariance under changing implementation child orientations. No
membership or desired law is placed in the carrier interface. -/
theorem unit_generator_factors_through_forest_register
    (v w : SelectedView V E Copy) (keep : Finset Copy)
    (h : forestRegister v = forestRegister w)
    (F : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) → ℝ) :
    unitForestGenerator v keep F = unitForestGenerator w keep F := by
  have hq : unrankedView (bareForestView v) = unrankedView (bareForestView w) := by
    apply UnrankedView.ext
    · exact congrArg Prod.fst h
    · rfl
    · exact congrArg Prod.snd h
  have hb : forestBlocks v keep = forestBlocks w keep := by
    unfold forestBlocks
    apply Finset.image_congr
    intro x hx
    exact unranked_view_block_leaves (bareForestView v) (bareForestView w) hq x
  unfold unitForestGenerator
  rw [hb]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  have hm := actual_unranked_projected_merger (bareForestView v) (bareForestView w) hq p.1 p.2
  have hmr : forestRegister (projectedMerge v p.1 p.2) =
      forestRegister (projectedMerge w p.1 p.2) := by
    apply Prod.ext
    · exact congrArg UnrankedView.genealogy hm
    · exact congrArg UnrankedView.register hm
  rw [hmr,h]

/-- Actual finite source-image carrier for the population-free forest/register
readout. Finiteness does NOT by itself prove closure under the unit generator
at every graph location or admission of a relabelled old-root source. -/
abbrev ForestRegisterIndex (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {v : ((Copy → Option (UnrankedTree Copy)) × (V → Bool)) //
    ∃ s : Code N sample, forestRegister (selectedView (state s) keep) = v}

noncomputable def forestRegisterProjection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : ForestRegisterIndex N sample keep :=
  ⟨forestRegister (selectedView (state s) keep),⟨s,rfl⟩⟩

noncomputable instance forestRegisterIndexFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (ForestRegisterIndex N sample keep) :=
  Fintype.ofSurjective (forestRegisterProjection N keep) (by
    intro v
    obtain ⟨s,hs⟩ := v.property
    exact ⟨s,Subtype.ext hs⟩)

end CloudG3.UnitArmGenerator
