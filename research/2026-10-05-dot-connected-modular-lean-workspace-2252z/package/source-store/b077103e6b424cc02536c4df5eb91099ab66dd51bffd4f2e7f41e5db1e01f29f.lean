import G1UnrankedActualFuture

/-!
# The canonical labelled UNRANKED forest K suffices at one original exit

Contributor: dot, 2026-10-03. The forest's original labelled clades determine
every selected subtree through actual source leaf fibres. No current owner ID,
child orientation, supplied desired law or count-only surrogate is retained.
-/
namespace G1UnrankedSingleExitLabel
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1UnrankedActualFuture
open G1JointUnrankedForestAssembly G1SameOriginalExteriorContinuation
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_unranked_subtree_from_forest (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (x : Copy) (hx : x ∈ keep) (q : UnrankedTree Copy)
    (hq : q ∈ sourceUnrankedForest s keep) (hxq : x ∈ treeLeaves q) :
    optionUnranked ((selectedView s keep).genealogy x) = some q := by
  obtain ⟨l,hl,hprune⟩ := forest_member_live_witness s hs keep hq
  rw [treeLeaves_from_prune hprune] at hxq
  have howner : s.ancestor x = l := (hs.leaf_fiber l hl x).mp (Finset.mem_inter.mp hxq).1
  simpa only [selectedView,selectedGenealogy,if_pos hx,howner] using hprune

/-- The exact whole labelled forest determines the entire per-label rooted
unranked genealogy map by source-derived fibres, with no partition field. -/
theorem actual_forest_determines_unranked_genealogies (s z : State V E Copy)
    (hs : Valid s) (hz : Valid z) (keep : Finset Copy)
    (hforest : sourceUnrankedForest s keep = sourceUnrankedForest z keep) :
    (unrankedView (selectedView s keep)).genealogy = (unrankedView (selectedView z keep)).genealogy := by
  funext x
  by_cases hx : x ∈ keep
  · obtain ⟨q,hq,hxq⟩ := (source_unranked_forest_covers s hs keep x).mpr hx
    have hqz : q ∈ sourceUnrankedForest z keep := hforest ▸ hq
    exact (actual_unranked_subtree_from_forest s hs keep x hx q hq hxq).trans
      (actual_unranked_subtree_from_forest z hz keep x hx q hqz hxq).symm
  · simp [unrankedView,selectedView,selectedGenealogy,hx]

/-- At the derived ONE original population exit, K plus that population and
the SAME register determines the complete unranked causal inside interface. -/
theorem actual_single_exit_unranked_label_view (s z : State V E Copy)
    (hs : Valid s) (hz : Valid z) (keep : Finset Copy) (p : Location V E)
    (hforest : sourceUnrankedForest s keep = sourceUnrankedForest z keep)
    (hsingle : ∀ x ∈ keep, copyLocation s x = p)
    (zsingle : ∀ x ∈ keep, copyLocation z x = p) (hregister : s.register = z.register) :
    unrankedView (selectedView s keep) = unrankedView (selectedView z keep) := by
  apply UnrankedView.ext
  · exact actual_forest_determines_unranked_genealogies s z hs hz keep hforest
  · funext x
    by_cases hx : x ∈ keep
    · simp [unrankedView,selectedView,selectedLocation,hx,hsingle x hx,zsingle x hx]
    · simp [unrankedView,selectedView,selectedLocation,hx]
  · exact hregister

noncomputable def unrankedJoinedPanelView (inside : Finset Copy)
    (v : UnrankedView V E Copy × UnrankedView V E Copy) : UnrankedView V E Copy where
  genealogy x := if x ∈ inside then v.1.genealogy x else v.2.genealogy x
  population x := if x ∈ inside then v.1.population x else v.2.population x
  register := v.1.register

lemma actual_unranked_joined_panel (inside : Finset Copy)
    (v : SelectedView V E Copy × SelectedView V E Copy) :
    unrankedView (joinedPanelView inside v) =
      unrankedJoinedPanelView inside (unrankedView v.1,unrankedView v.2) := by
  apply UnrankedView.ext
  · funext x
    by_cases hx : x ∈ inside <;> simp [unrankedView,joinedPanelView,unrankedJoinedPanelView,hx]
  · rfl
  · rfl

/-- Complete larger-state interface equality follows from ONLY the inside
labelled unranked forest K, its actual one-population exit, SAME register and
the preserved exterior unranked state. Source validity supplies every fibre. -/
theorem actual_K_only_complete_exit_view (s z : State V E Copy) (hs : Valid s) (hz : Valid z)
    (inside outside : Finset Copy) (p : Location V E)
    (hspure : PrunedPanelSeparated s inside outside) (hzpure : PrunedPanelSeparated z inside outside)
    (hK : sourceUnrankedForest s inside = sourceUnrankedForest z inside)
    (hsingle : ∀ x ∈ inside, copyLocation s x = p)
    (zsingle : ∀ x ∈ inside, copyLocation z x = p) (hregister : s.register = z.register)
    (houtside : unrankedView (selectedView s outside) = unrankedView (selectedView z outside)) :
    unrankedView (selectedView s (inside ∪ outside)) =
      unrankedView (selectedView z (inside ∪ outside)) := by
  rw [actual_joined_panel_view s hs inside outside hspure,
    actual_joined_panel_view z hz inside outside hzpure,actual_unranked_joined_panel,actual_unranked_joined_panel,
    actual_single_exit_unranked_label_view s z hs hz inside p hK hsingle zsingle hregister,houtside]

/-- The SAME actual original future can use arbitrary original root/cross-
panel operations. Its full unranked causal law depends only on the accepted
K label and retained exterior/register interface, not internal ordered state. -/
theorem actual_K_only_original_future {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (inside outside : Finset Copy)
    (future : List (ProgramStep N)) (s z : Code N sample) (p : Location V E)
    (hspure : PrunedPanelSeparated (state s) inside outside)
    (hzpure : PrunedPanelSeparated (state z) inside outside)
    (hK : sourceUnrankedForest (state s) inside = sourceUnrankedForest (state z) inside)
    (hsingle : ∀ x ∈ inside, copyLocation (state s) x = p)
    (zsingle : ∀ x ∈ inside, copyLocation (state z) x = p)
    (hregister : (state s).register = (state z).register)
    (houtside : unrankedView (selectedView (state s) outside) = unrankedView (selectedView (state z) outside))
    (readout : UnrankedView V E Copy → Obs) :
    (sourceProgram N r future s).map (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) =
      (sourceProgram N r future z).map (fun d => readout (unrankedView (selectedView (state d) (inside ∪ outside)))) := by
  exact actual_unranked_future_row_independent N r (inside ∪ outside) future s z
    (actual_K_only_complete_exit_view (state s) (state z) s.property.forest z.property.forest inside outside p
      hspure hzpure hK hsingle zsingle hregister houtside) readout

#print axioms actual_K_only_original_future
end G1UnrankedSingleExitLabel
