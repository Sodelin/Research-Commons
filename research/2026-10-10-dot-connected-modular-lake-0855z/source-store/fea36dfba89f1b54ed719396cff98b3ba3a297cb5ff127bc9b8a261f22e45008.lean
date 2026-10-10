import G1CanonicalPendingBoundaryMembership

/-! Exact source-to-AsyncOperation opening/closing interfaces. Opening moves
one full ORIGINAL opaque descendant panel out of base; closing delivers its
complete K-grafted original panel before the post-cut history observer. -/
namespace G1ActualOriginalOpenCloseAsyncInterface
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open G1UnrankedSourceView G1JointUnrankedForestAssembly G1OriginalUnrankedActorOpenClose
open G1ActualOriginalPrivateAsyncStep G1PendingActorInterfaceCommutation
open G1ActualGraphNormalization
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def emptyOriginalView {V E Copy : Type*} (register : V → Bool) : UnrankedView V E Copy :=
  ⟨fun _ => none,fun _ => none,register⟩

lemma actual_empty_original_panel {V E Copy : Type*} [Fintype V] [Fintype E] [Fintype Copy]
    [DecidableEq V] [DecidableEq E] [DecidableEq Copy] (s : State V E Copy) :
    unrankedView (selectedView s ∅) = emptyOriginalView s.register := by
  apply UnrankedView.ext
  · funext x; simp [unrankedView,selectedView,selectedGenealogy,emptyOriginalView,UnifiedLean.Source.UnrankedGenealogyObservation.optionUnranked]
  · funext x; simp [unrankedView,selectedView,selectedLocation,emptyOriginalView]
  · rfl

noncomputable def originalOpenKernel {V E Copy : Type*} [Fintype V] [Fintype E] [Fintype Copy]
    [DecidableEq V] [DecidableEq E] [DecidableEq Copy] (inside base : Finset Copy) :
    UnrankedView V E Copy × UnrankedView V E Copy → PMF (UnrankedView V E Copy × UnrankedView V E Copy) :=
  fun data => PMF.pure (openOriginalActor inside base data.1)

noncomputable def originalCloseKernel {V E Copy : Type*} [Fintype V] [Fintype E] [Fintype Copy]
    [DecidableEq V] [DecidableEq E] [DecidableEq Copy] (inside : Finset Copy) :
    UnrankedView V E Copy × UnrankedView V E Copy → PMF (UnrankedView V E Copy × UnrankedView V E Copy) :=
  fun data => PMF.pure (closeOriginalActor inside data.1 data.2,emptyOriginalView data.2.register)

/-- Opening changes no source genealogy/population/register. It is an ACTUAL
base split into full original descendant coordinates, with saved opaque input
subtrees. Other pending coordinates are untouched. -/
theorem actual_original_open_async_interface (O : Source.{u,v,w} X)
    {Copy I : Type*} [Fintype Copy] [DecidableEq Copy] [DecidableEq I] {sample : Copy → X}
    (s : Code O.network sample) (owner : I) (inside base : Finset Copy) (slots : I → Finset Copy)
    (hi : inside ⊆ base) :
    PMF.pure (originalAsyncProjection O (base \ inside) (Function.update slots owner inside) s) =
      asyncStep (.interface owner (originalOpenKernel inside base)) (originalAsyncProjection O base slots s) := by
  simp only [asyncStep,originalOpenKernel,PMF.pure_map]
  apply congrArg PMF.pure
  apply Prod.ext
  · exact (congrArg Prod.fst (actual_original_open_coordinates (state s) inside base hi)).symm
  · funext other
    by_cases he : other = owner
    · subst other
      simp only [originalAsyncProjection,Function.update_self]
      exact (congrArg Prod.snd (actual_original_open_coordinates (state s) inside base hi)).symm
    · simp only [originalAsyncProjection,Function.update_of_ne he]

/-- Closing is ACTUAL full-original causal coarsening. Its delivered subtree
is joined into base before any corresponding old post-cut root checkpoint;
the finished actor slot is cleared to the SAME original register. -/
theorem actual_original_close_async_interface (O : Source.{u,v,w} X)
    {Copy I : Type*} [Fintype Copy] [DecidableEq Copy] [DecidableEq I] {sample : Copy → X}
    (s : Code O.network sample) (owner : I) (inside base : Finset Copy) (slots : I → Finset Copy)
    (hslot : slots owner = inside) (hp : PrunedPanelSeparated (state s) inside base) :
    PMF.pure (originalAsyncProjection O (inside ∪ base) (Function.update slots owner ∅) s) =
      asyncStep (.interface owner (originalCloseKernel inside)) (originalAsyncProjection O base slots s) := by
  simp only [asyncStep,originalCloseKernel,PMF.pure_map]
  apply congrArg PMF.pure
  apply Prod.ext
  · simp only [originalAsyncProjection,hslot]
    exact (actual_original_actor_close (state s) s.property.forest inside base hp).symm
  · funext other
    by_cases he : other = owner
    · subst other
      simp only [originalAsyncProjection,Function.update_self,hslot,unrankedView,selectedView]
      exact actual_empty_original_panel (state s)
    · simp only [originalAsyncProjection,Function.update_of_ne he]

#print axioms actual_original_open_async_interface
#print axioms actual_original_close_async_interface
end G1ActualOriginalOpenCloseAsyncInterface
