import FirstParentJoin
import Mathlib.Data.Fintype.Card

/-! Actual cut-child source graph coverage for the common-ancestor focal
hybrid census. Bridges derive comparability and STRICT cell-window separation;
no chronological coverage, source law or desired kernel is an input field.
Cloud G3, 2026-10-08. Compiler UNCHECKED, independent review pending.
This does not cover subset-only hybrids of an arbitrary coupled menu. -/
namespace CloudG3.FocalHybridWindow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.ParentCalendar
open G1CutChildPorts G1ActualCutDescendants CloudG3.FirstParentJoin
open scoped Classical
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- The component entry exists in the ACTUAL original graph: root component
or genuine incoming original bridge. This is not a coverage oracle. -/
theorem actual_component_entry_exists (N : RootedBinary V E X) (port : V) :
    ∃ entry, IsComponentEntryFor N entry port := by
  by_cases hb : N.graph.SameBlob N.root port
  · exact ⟨N.root,Or.inl ⟨rfl,hb⟩⟩
  · obtain ⟨e,he,hblob⟩ :=
      GProgram.G5.ComponentEntries.nonroot_component_has_incoming_bridge
        N.graph N.root N.rooted port hb
    exact ⟨N.graph.target e,Or.inr ⟨e,he,rfl,hblob⟩⟩

noncomputable def actualComponentEntry (N : RootedBinary V E X) (port : V) : V :=
  Classical.choose (actual_component_entry_exists N port)

theorem actual_component_entry_spec (N : RootedBinary V E X) (port : V) :
    IsComponentEntryFor N (actualComponentEntry N port) port :=
  Classical.choose_spec (actual_component_entry_exists N port)

/-- Two original hybrids ancestral to ONE same taxon are comparable because
the first one's actual child is a bridge. Avoid/cross is a graph dichotomy,
not a pathwise scalar or stochastic recurrence. -/
theorem actual_common_taxon_hybrids_comparable (N : RootedBinary V E X)
    (hc : CutChild N) {h k : V} (hh : N.graph.IsHybrid h) (hk : N.graph.IsHybrid k)
    (x : X) (hhx : N.graph.DReach h (N.leaf x)) (hkx : N.graph.DReach k (N.leaf x)) :
    N.graph.DReach h k ∨ N.graph.DReach k h := by
  obtain ⟨e,hes,_⟩ := unique_child_edge N hh.2
  have heb : N.graph.IsBridge e := hc e (by rw [hes]; exact hh)
  have hxside : N.graph.ReachWithout e (N.graph.target e) (N.leaf x) :=
    (hybrid_descendant_component N hh hes heb x).mp hhx
  rcases actual_directed_walk_avoids_or_crosses N.graph e hkx with havoid | ⟨hcross,_⟩
  · have hkside : N.graph.ReachWithout e (N.graph.target e) k :=
      hxside.trans (N.graph.ureach_symm havoid)
    have htk : N.graph.DReach (N.graph.target e) k :=
      (actual_bridge_target_side_descendant N e heb k).mp hkside
    exact Or.inl ((Relation.ReflTransGen.single ⟨e,hes,rfl⟩).trans htk)
  · exact Or.inr (by simpa only [hes] using hcross)

/-- Strict REAL calendar order resolves the actual ancestor comparison. -/
theorem actual_older_common_taxon_hybrid_reaches (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) {h k : V}
    (hh : N.graph.IsHybrid h) (hk : N.graph.IsHybrid k) (x : X)
    (hhx : N.graph.DReach h (N.leaf x)) (hkx : N.graph.DReach k (N.leaf x))
    (hage : C.age h < C.age k) : N.graph.DReach k h := by
  rcases actual_common_taxon_hybrids_comparable N hc hh hk x hhx hkx with hhk | hkh
  · exact False.elim ((not_le_of_gt hage) (actual_calendar_directed_age N C hhk))
  · exact hkh

/-- The younger hybrid's whole actual bridge-deleted component entry is
BELOW the older hybrid's child bridge. Its age is strictly younger. No
common-route membership or desired cell-window condition is assumed. -/
theorem actual_entry_before_strict_hybrid_ancestor (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {k : V}
    (hk : N.graph.IsHybrid k) (hne : k ≠ H.hybrid) (hkh : N.graph.DReach k H.hybrid) :
    C.age entry < C.age k := by
  obtain ⟨e,hes,_⟩ := unique_child_edge N hk.2
  have heb : N.graph.IsBridge e := hc e (by rw [hes]; exact hk)
  have hth : N.graph.DReach (N.graph.target e) H.hybrid :=
    (descendant_via_unique_child N hk.2 hes hne).mp hkh
  have hhside : N.graph.ReachWithout e (N.graph.target e) H.hybrid :=
    (actual_bridge_target_side_descendant N e heb H.hybrid).mpr hth
  have hentry : N.graph.ReachWithout e entry H.hybrid :=
    GProgram.G5.ComponentEntries.sameBlob_avoids_bridge N.graph heb
      (component_entry_sameBlob N he)
  have hteside : N.graph.ReachWithout e (N.graph.target e) entry :=
    hhside.trans (N.graph.ureach_symm hentry)
  have hte : N.graph.DReach (N.graph.target e) entry :=
    (actual_bridge_target_side_descendant N e heb entry).mp hteside
  exact (actual_calendar_directed_age N C hte).trans_lt
    (by simpa only [hes] using C.edge_older e)

/-- The actual first join is strictly BEFORE ANY older original hybrid
ancestral to the same taxon, including all original unequal-parent arms. -/
theorem actual_common_taxon_cell_window (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {k : V}
    (hk : N.graph.IsHybrid k) (x : X)
    (hhx : N.graph.DReach H.hybrid (N.leaf x)) (hkx : N.graph.DReach k (N.leaf x))
    (hage : C.age H.hybrid < C.age k) :
    C.age (firstParentJoin N C H he) < C.age k := by
  have hkh := actual_older_common_taxon_hybrid_reaches N hc C H.isHybrid hk x hhx hkx hage
  have hne : k ≠ H.hybrid := by
    intro h
    rw [h] at hage
    exact (lt_irrefl _) hage
  exact (actual_first_join_age_window N C H he).2.trans_lt
    (actual_entry_before_strict_hybrid_ancestor N hc C H he hk hne hkh)

/-- Original hybrid IDs ancestral to EVERY retained selected label. This is
a concrete finite graph census, not an asserted all-menu cell enumeration. -/
noncomputable def focalHybridVertices (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Finset V :=
  Finset.univ.filter (fun h => N.graph.IsHybrid h ∧
    ∀ x ∈ keep, N.graph.DReach h (N.leaf (sample x)))

theorem mem_focal_hybrid_vertices (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) (h : V) :
    h ∈ focalHybridVertices N sample keep ↔ N.graph.IsHybrid h ∧
      ∀ x ∈ keep, N.graph.DReach h (N.leaf (sample x)) := by
  simp only [focalHybridVertices,Finset.mem_filter,Finset.mem_univ,true_and]

/-- The census length is bounded by the TRUE TOTAL original Hybrid carrier,
not an independently supplied word length or a selected outcome count. -/
theorem actual_focal_hybrid_count_le_total (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) :
    (focalHybridVertices N sample keep).card ≤
      Fintype.card (UnifiedLean.Source.NativeParentRouting.Hybrid N) := by
  change _ ≤ Fintype.card {v : V // N.graph.IsHybrid v}
  rw [Fintype.card_subtype]
  apply Finset.card_le_card
  intro h hh
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    ((mem_focal_hybrid_vertices N sample keep h).mp hh).1⟩

/-- On a NONEMPTY panel, common-ancestor hybrid dates are all distinct.
Unrelated original nodes may still have tied dates; their actual batches stay. -/
theorem actual_focal_hybrid_age_injective (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (sample : Copy → X)
    (keep : Finset Copy) (hkeep : keep.Nonempty) :
    Function.Injective (fun h : focalHybridVertices N sample keep => C.age h.val) := by
  intro h k hage
  apply Subtype.ext
  by_contra hne
  obtain ⟨x,hx⟩ := hkeep
  have hh := (mem_focal_hybrid_vertices N sample keep h.val).mp h.property
  have hk := (mem_focal_hybrid_vertices N sample keep k.val).mp k.property
  rcases actual_common_taxon_hybrids_comparable N hc hh.1 hk.1 (sample x)
      (hh.2 x hx) (hk.2 x hx) with hhk | hkh
  · have hl := actual_calendar_directed_age_strict N C hne hhk
    rw [hage] at hl
    exact (lt_irrefl _) hl
  · have hl := actual_calendar_directed_age_strict N C hne.symm hkh
    rw [hage] at hl
    exact (lt_irrefl _) hl

/-- The nonoverlapping chronological-window condition in the finite-cell
hand composition is DERIVED for any pair from this real focal census. -/
theorem actual_focal_hybrid_cell_window (N : RootedBinary V E X)
    (hc : CutChild N) (C : Calendar N.graph) (sample : Copy → X)
    (keep : Finset Copy) (hkeep : keep.Nonempty)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid)
    (hh : H.hybrid ∈ focalHybridVertices N sample keep) {k : V}
    (hk : k ∈ focalHybridVertices N sample keep) (hage : C.age H.hybrid < C.age k) :
    C.age (firstParentJoin N C H he) < C.age k := by
  obtain ⟨x,hx⟩ := hkeep
  have hhp := (mem_focal_hybrid_vertices N sample keep H.hybrid).mp hh
  have hkp := (mem_focal_hybrid_vertices N sample keep k).mp hk
  exact actual_common_taxon_cell_window N hc C H he hkp.1 (sample x)
    (hhp.2 x hx) (hkp.2 x hx) hage

end CloudG3.FocalHybridWindow
