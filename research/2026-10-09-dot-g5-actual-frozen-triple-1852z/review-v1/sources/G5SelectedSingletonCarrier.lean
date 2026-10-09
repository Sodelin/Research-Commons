import G5OriginalSelectedPosterior

/-!
# Canonical actual singleton source carrier for a selected posterior state

Contributor: dot, 2026-10-09. SOURCE DRAFT / COMPILER UNCHECKED.
A selected-singleton view of an actual original state has a canonical source
realization on the actual selected-copy subtype. It inherits the original
population of each selected label and the SAME shared register. Original
source validity and the cross-carrier future law are proved from the source
constructors. Unselected live roots are integrated by the existing actual
projectivity theorem; they are not required to be absent or unmerged.
-/
namespace GProgram.G5.SelectedSingletonCarrier
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G5.OriginalProgramSurvival
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Selected singleton genealogy is hereditary under further original-label
selection. This uses the actual pruned old genealogy, not ancestor labels. -/
theorem actual_all_singleton_restrict (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample)
    (hs : SingletonSelected Finset.univ (selectedView (state s) Finset.univ))
    (keep : Finset Copy) : SingletonSelected keep (selectedView (state s) keep) := by
  intro x hx
  have h := hs x (Finset.mem_univ x)
  have hg : (state s).genealogy ((state s).ancestor x) = .leaf x := by
    simpa only [selectedView, selectedGenealogy, Finset.mem_univ, if_true,
      full_prune, Option.some.injEq] using h
  simp [selectedView, selectedGenealogy, hx, hg, Genealogy.prune]

noncomputable def selectedSingletonState (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample) :
    State V E (SelectedCopy keep) where
  live := Finset.univ
  ancestor := id
  genealogy := Genealogy.leaf
  location := fun x => copyLocation (state s) x.val
  register := (state s).register
  history := []

theorem selected_singleton_state_valid (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample) :
    SourceValid N (selectedSample sample keep) (selectedSingletonState N keep s) := by
  constructor
  · constructor
    · intro x; exact Finset.mem_univ x
    · intro x _; rfl
    · intro x _ y
      simp [selectedSingletonState, Genealogy.leaves, eq_comm]
    · intro x _; trivial
  · intro x
    exact s.property.original_descendant x.val

noncomputable def selectedSingletonCode (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample) :
    Code N (selectedSample sample keep) :=
  admittedCode N (selectedSample sample keep) (selectedSingletonState N keep s)
    (selected_singleton_state_valid N keep s)

theorem selected_singleton_code_ancestor (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample) :
    (state (selectedSingletonCode N keep s)).ancestor = id := rfl

theorem selected_singleton_code_register (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample) :
    (state (selectedSingletonCode N keep s)).register = (state s).register := rfl

theorem selected_singleton_code_population (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample)
    (x : SelectedCopy keep) :
    copyLocation (state (selectedSingletonCode N keep s)) x =
      copyLocation (state s) x.val := by
  exact decode_encode_copyLocation N.root (selectedSingletonState N keep s)
    (selected_singleton_state_valid N keep s).forest x

/-- This is an ACTUAL compatible small source state, constructed at the cut.
Only the selected-singleton event is assumed, as supplied by the posterior. -/
theorem actual_selected_singleton_diagram (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (s : Code N sample)
    (hs : SingletonSelected keep (selectedView (state s) keep)) :
    selectedView (state s) keep =
      liftView keep (selectedView (state (selectedSingletonCode N keep s)) Finset.univ) := by
  change selectedView (state s) keep =
    liftView keep (selectedView (decodeSnapshot N.root
      (encodeSnapshot (selectedSingletonState N keep s)
        (selected_singleton_state_valid N keep s).forest)) Finset.univ)
  rw [decode_encode_selectedView]
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ keep
    · rw [hs x hx]
      simp [liftView, selectedView, selectedGenealogy, selectedSingletonState,
        Genealogy.prune, mapLabels, hx]
    · simp [liftView, selectedView, selectedGenealogy, hx]
  · funext x
    by_cases hx : x ∈ keep <;>
      simp [liftView, selectedView, selectedLocation, selectedSingletonState,
        copyLocation, hx]
  · rfl

/-- An actual selected-singleton full source epoch is exactly the epoch from
the canonical actual smaller source. No latent register is redrawn. -/
theorem actual_selected_singleton_epoch (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (hs : SingletonSelected keep (selectedView (state s) keep))
    (t : ℝ≥0) :
    (sourceTimeKernel N r t s).map (fun d => joinedProjection N keep (.inl d)) =
      (sourceTimeKernel N r t (selectedSingletonCode N keep s)).map
        (fun d => joinedProjection N keep (.inr d)) :=
  actual_cross_carrier_source_time_law N r keep t s (selectedSingletonCode N keep s)
    (actual_selected_singleton_diagram N keep s hs)

#print axioms actual_all_singleton_restrict
#print axioms selected_singleton_state_valid
#print axioms selected_singleton_code_ancestor
#print axioms selected_singleton_code_register
#print axioms selected_singleton_code_population
#print axioms actual_selected_singleton_diagram
#print axioms actual_selected_singleton_epoch
end GProgram.G5.SelectedSingletonCarrier

