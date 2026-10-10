import G5ActualSingletonCalendarObservation

/-!
# Sharpness of maximum panel size two for fair-M2 quartet identification
Contributor: dot / OpenAI, 2026-10-03.
The accepted hand proof and independent review explicitly use ordinary quartet
trees to exclude singleton-only readout. This module uses TWO admitted actual
original sources, every original labelled singleton panel and the empty panel,
GENUINE source-pushforward full singleton CALENDAR laws, and exactly the
normalized Q target of the already formalized upper bound.
-/
namespace GProgram.G5.Sharpness
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.NativeFairCurrentPosition
open scoped Classical

/-- Every original singleton law matches, for ANY COMMON/I comparison. -/
theorem every_original_singleton_calendar_law_matches (commonA commonB : Bool) :
    ∀ x : Taxon,
      singletonCalendarLaw sourceA treeCalendar registryA (fairParameters sourceA) rates commonA x =
      singletonCalendarLaw sourceB treeCalendar registryB (fairParameters sourceB) rates commonB x := by
  intro x
  rw [actual_singleton_calendar_law,actual_singleton_calendar_law,tipsA,tipsB]

lemma empty_calendar_law_matches (commonA commonB : Bool) :
    emptyCalendarLaw sourceA treeCalendar registryA (fairParameters sourceA) rates commonA =
      emptyCalendarLaw sourceB treeCalendar registryB (fairParameters sourceB) rates commonB := by
  rw [actual_empty_calendar_law,actual_empty_calendar_law]

/-- The full family of original panels of maximum size ONE, including empty. -/
abbrev SmallPanel := {A : Finset Taxon // A.card ≤ 1}

noncomputable def smallPanelCalendarLaw (N : RootedBinary Vertex Edge Taxon)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (r : PositivePairRates Edge)
    (common : Bool) (A : SmallPanel) : PMF (Option (SingletonCalendarGenealogy Taxon)) :=
  if h : A.val.Nonempty then
    singletonCalendarLaw N C H (fairParameters N) r common (Classical.choose h)
  else emptyCalendarLaw N C H (fairParameters N) r common

/-- A nonempty permitted panel contains exactly the recorded ORIGINAL label;
no original label is silently discarded by the small-panel family. -/
lemma permitted_panel_is_singleton (A : SmallPanel) (h : A.val.Nonempty) :
    A.val = {Classical.choose h} := by
  ext x
  simp only [Finset.mem_singleton]
  constructor
  · intro hx
    exact (Finset.card_le_one.mp A.property) x hx _ (Classical.choose_spec h)
  · intro he
    rw [he]
    exact Classical.choose_spec h

/-- Equality of the COMPLETE original max-one panel CALENDAR family, rather
than a single selected one-tip example or a coarser topology-only law. -/
theorem complete_max_one_calendar_family_matches (commonA commonB : Bool) :
    ∀ A : SmallPanel,
      smallPanelCalendarLaw sourceA treeCalendar registryA rates commonA A =
        smallPanelCalendarLaw sourceB treeCalendar registryB rates commonB A := by
  intro A
  unfold smallPanelCalendarLaw
  split
  · exact every_original_singleton_calendar_law_matches commonA commonB _
  · exact empty_calendar_law_matches commonA commonB

/-- Extra source root metadata also agrees if a calendar encoding retains it.
It does not expose a hidden source root as an ordinary genealogy observation. -/
lemma shared_source_root_date : treeCalendar.age sourceA.root = treeCalendar.age sourceB.root := rfl
lemma shared_source_root_date_value : treeCalendar.age sourceA.root = 2 := rfl

/-- ACTUAL source counterexample for the accepted sharpness contract. The
source constants are admitted finite binary rooted-LSA original multigraphs;
cut-child geometry, fair natural priors, all positive clocks and simultaneous
age-zero original sampling are proved independently of this conclusion.
No output-assumption, abstract substitute source, sorry, or native axiom. -/
theorem fair_m2_sharpness_actual_source_counterexample (commonA commonB : Bool) :
    (∀ e, sourceA.graph.IsHybrid (sourceA.graph.source e) → sourceA.graph.IsBridge e) ∧
    (∀ e, sourceB.graph.IsHybrid (sourceB.graph.source e) → sourceB.graph.IsBridge e) ∧
    (∀ x, treeCalendar.age (sourceA.leaf x) = 0) ∧
    (∀ x, treeCalendar.age (sourceB.leaf x) = 0) ∧
    (∀ A : SmallPanel,
      smallPanelCalendarLaw sourceA treeCalendar registryA rates commonA A =
        smallPanelCalendarLaw sourceB treeCalendar registryB rates commonB A) ∧
    normalizedDisplayedCutQuartets sourceA quartet ≠ normalizedDisplayedCutQuartets sourceB quartet := by
  exact ⟨cut_childA,cut_childB,tipsA,tipsB,
    complete_max_one_calendar_family_matches commonA commonB,documented_normalized_quartet_targets_differ⟩

#print axioms every_original_singleton_calendar_law_matches
#print axioms complete_max_one_calendar_family_matches
#print axioms fair_m2_sharpness_actual_source_counterexample
#check fair_m2_identifies_documented_normalized_cut_quartets
#check fair_m2_sharpness_actual_source_counterexample
end GProgram.G5.Sharpness
