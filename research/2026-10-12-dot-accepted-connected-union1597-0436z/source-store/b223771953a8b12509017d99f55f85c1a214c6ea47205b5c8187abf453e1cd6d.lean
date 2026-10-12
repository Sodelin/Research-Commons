import G5FiniteAttainedDeletionTrace
import G5CommonSwitchingPersistence

/-!
# Original-label group maps follow retained originals in ALL COMMON switchings
Contributor: dot / OpenAI, 2026-10-03.
Initial groups and every simultaneous original-tip deletion have a proved
population-path invariant. Every future original population block is exactly
the lift of the representative block; ancestry includes none above the root.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E] [LinearOrder X]

lemma sharesPopulation_refl (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x : X) {t : ℝ} (hl : C.age (N.leaf x) ≤ t) :
    SharesPopulation N R C t x x := by
  by_cases ht : C.age N.root ≤ t
  · exact ⟨none,ht,ht⟩
  · obtain ⟨e,he,ha⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C (R.valid x) hl (lt_of_not_ge ht)
    exact ⟨some e,⟨he,ha⟩,⟨he,ha⟩⟩

lemma sharesPopulation_trans (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) {x y z : X} {t : ℝ}
    (hxy : SharesPopulation N R C t x y) (hyz : SharesPopulation N R C t y z) :
    SharesPopulation N R C t x z := by
  obtain ⟨p,hxp,hyp⟩ := hxy
  obtain ⟨q,hyq,hzq⟩ := hyz
  have he := occupies_unique N C R hyp hyq
  subst q
  exact ⟨p,hxp,hzq⟩

lemma shared_population_membership_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) {x y : X} {t : ℝ} (h : SharesPopulation N R C t x y) (p : Option E) :
    Occupies N R C t x p ↔ Occupies N R C t y p := by
  obtain ⟨q,hxq,hyq⟩ := h
  constructor
  · intro hxp
    have he := occupies_unique N C R hxp hxq
    exact he.symm ▸ hyq
  · intro hyp
    have he := occupies_unique N C R hyp hyq
    exact he.symm ▸ hxq

/-- Representative assignment uses the unique simultaneous exact block
containing x; an ungrouped original label maps to itself. -/
noncomputable def stepRepresentative (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) (x : X) : X :=
  if h : ∃ D ∈ simultaneousBlocks N C B t, x ∈ D then
    let D := Classical.choose h
    originalRepresentative D ((mem_simultaneousBlocks N C B D t).mp (Classical.choose_spec h).1).2.1
  else x

theorem stepRepresentative_mem_survivors (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) {x : X} (hx : x ∈ B) :
    stepRepresentative N C B t x ∈ survivors N C B t := by
  unfold stepRepresentative
  split_ifs with h
  · exact representative_survives N C B (Classical.choose h) t (Classical.choose_spec h).1
  · apply Finset.mem_filter.mpr
    refine ⟨hx,?_⟩
    intro D hD hxD
    exact False.elim (h ⟨D,hD,hxD⟩)

/-- Every original representative follows its newly retained ORIGINAL tip in
all COMMON switchings, including later shared hybrids and ancestral ages. -/
theorem stepRepresentative_all_common_persistence (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (B : Finset X) {u t : ℝ} (hut : u ≤ t)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ u) {x : X} (hx : x ∈ B) :
    ∀ a : CommonSeed N,
      SharesPopulation N (commonRoutes N C H a) C t x (stepRepresentative N C B u x) := by
  unfold stepRepresentative
  split_ifs with h
  · exact sure_block_original_representative_persistence N C H B (Classical.choose h) hut
      ((mem_simultaneousBlocks N C B (Classical.choose h) u).mp (Classical.choose_spec h).1).2.1
      ((mem_simultaneousBlocks N C B (Classical.choose h) u).mp (Classical.choose_spec h).1).2.2
      (Classical.choose_spec h).2
  · intro a
    exact sharesPopulation_refl N C (commonRoutes N C H a) x ((hl x hx).trans hut)

/-- The proposition is an inductive invariant. Initial validity and preservation
are THEOREMS below, not extra fields of the admitted source. -/
def GroupPathInvariant (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (A B : Finset X) (g : X → X) (s : ℝ) : Prop :=
  ∀ x ∈ A, g x ∈ B ∧ ∀ t : ℝ, s ≤ t → ∀ a : CommonSeed N,
    SharesPopulation N (commonRoutes N C H a) C t x (g x)

/-- Initial groups are genuine singleton original taxa. -/
theorem initial_original_group_paths (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (A : Finset X) {s : ℝ}
    (hl : ∀ x ∈ A, C.age (N.leaf x) ≤ s) : GroupPathInvariant N C H A A id s := by
  intro x hx
  refine ⟨hx,?_⟩
  intro t hst a
  exact sharesPopulation_refl N C (commonRoutes N C H a) x ((hl x hx).trans hst)

/-- Compose original groups with the new original-tip representative map.
Past groups are never re-coined or treated as independent original duplicates. -/
theorem group_paths_preserved_by_simultaneous_deletion
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (A B : Finset X) (g : X → X) {s u : ℝ} (hsu : s ≤ u)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ u) (hgroups : GroupPathInvariant N C H A B g s) :
    GroupPathInvariant N C H A (survivors N C B u) (fun x => stepRepresentative N C B u (g x)) u := by
  intro x hx
  have hgx := hgroups x hx
  refine ⟨stepRepresentative_mem_survivors N C B u hgx.1,?_⟩
  intro t hut a
  exact sharesPopulation_trans N C (commonRoutes N C H a) (hgx.2 t (hsu.trans hut) a)
    (stepRepresentative_all_common_persistence N C H B hut hl hgx.1 a)

/-- The representative partition really lifts to the original population
blocks in each consistent common switching. -/
theorem original_population_block_is_group_lift (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (A B : Finset X) (g : X → X) {s t : ℝ}
    (hgroups : GroupPathInvariant N C H A B g s) (hst : s ≤ t)
    (a : CommonSeed N) (p : Option E) :
    populationBlock N (commonRoutes N C H a) A C t p =
      A.filter (fun x => g x ∈ populationBlock N (commonRoutes N C H a) B C t p) := by
  ext x
  simp only [populationBlock,Finset.mem_filter]
  constructor
  · rintro ⟨hx,hxp⟩
    have hg := hgroups x hx
    exact ⟨hx,hg.1,(shared_population_membership_iff N C (commonRoutes N C H a) (hg.2 t hst a) p).mp hxp⟩
  · rintro ⟨hx,_,hgp⟩
    exact ⟨hx,(shared_population_membership_iff N C (commonRoutes N C H a) ((hgroups x hx).2 t hst a) p).mpr hgp⟩

/-- Every stage of the constructed source chronology carries a composed
original-label group map. -/
theorem deletionTrace_preserves_original_group_paths (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    {B F : Finset X} {s u : ℝ} {n : Nat} (trace : DeletionTrace N C B s F u n)
    (A : Finset X) (g : X → X) (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s)
    (hgroups : GroupPathInvariant N C H A B g s) :
    ∃ gF : X → X, GroupPathInvariant N C H A F gF u := by
  induction trace generalizing g with
  | terminal B s hB => exact ⟨g,hgroups⟩
  | @step B s hs hc F u n rest ih =>
    let τ := firstGroupingAge N C B hs hc
    have hτ := (firstGroupingAge_attained N C B hs hc).2.1
    apply ih (fun x => stepRepresentative N C B τ (g x))
    · intro x hx
      exact (hl x (survivors_subset N C B τ hx)).trans hτ
    · exact group_paths_preserved_by_simultaneous_deletion N C H A B g hτ
        (fun x hx => (hl x hx).trans hτ) hgroups

/-- Connected finite original-tip chronology plus ALL-COMMON original group
paths; valid even if the later pair observer uses I-mode. -/
theorem contemporaneous_chronology_with_original_group_paths
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (A : Finset X) {s : ℝ} (hA : A.Nonempty)
    (htips : ∀ x ∈ A, C.age (N.leaf x) = s) :
    ∃ (F : Finset X) (u : ℝ) (n : Nat) (g : X → X), DeletionTrace N C A s F u n ∧ F.card = 1 ∧ F ⊆ A ∧
      s ≤ u ∧ u ≤ C.age N.root ∧ SafeAt N C F u ∧ n ≤ A.card-1 ∧
      GroupPathInvariant N C H A F g u := by
  obtain ⟨F,u,n,ht,hF,hFA,hsu,hu,hFs,hbound⟩ := contemporaneous_original_tip_chronology N C hcut A hA htips
  have hl : ∀ x ∈ A, C.age (N.leaf x) ≤ s := fun x hx => (htips x hx).le
  obtain ⟨g,hg⟩ := deletionTrace_preserves_original_group_paths N C H ht A id hl
    (initial_original_group_paths N C H A hl)
  exact ⟨F,u,n,g,ht,hF,hFA,hsu,hu,hFs,hbound,hg⟩

#print axioms stepRepresentative_all_common_persistence
#print axioms initial_original_group_paths
#print axioms group_paths_preserved_by_simultaneous_deletion
#print axioms original_population_block_is_group_lift
#print axioms deletionTrace_preserves_original_group_paths
#print axioms contemporaneous_chronology_with_original_group_paths
end GProgram.G5.AttainedChronology
