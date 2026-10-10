import G5AttainedOriginalTipChronology

/-!
# Simultaneous exact-block deletion keeps deterministic ORIGINAL tips
Contributor: dot / OpenAI, 2026-10-03.
One fixed original-label order selects one tip per simultaneous sure block.
The actual original source/calendar remains unchanged; no grouped pseudo-taxon,
posterior law or new coin is introduced. SafeAt is preserved by a proved subset.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

lemma occupies_unique (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) {t : ℝ} {x : X} {p q : Option E}
    (hp : Occupies N R C t x p) (hq : Occupies N R C t x q) : p = q := by
  cases p with
  | none =>
    cases q with
    | none => rfl
    | some e =>
      have ha := (R.valid x).source_age_le C hq.1
      exact False.elim (not_lt_of_ge (ha.trans hp) hq.2.2)
  | some e =>
    cases q with
    | none =>
      have ha := (R.valid x).source_age_le C hp.1
      exact False.elim (not_lt_of_ge (ha.trans hq) hp.2.2)
    | some f => exact congrArg some ((R.valid x).active_unique C hp.1 hq.1 hp.2 hq.2)

/-- Distinct simultaneous sure exact blocks are disjoint, even when uncertain
other occupancy blocks differ from one original route assignment to another. -/
theorem sureBlocks_eq_of_intersection (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D F : Finset X) {t : ℝ} (hD : SureBlock N C B D t) (hF : SureBlock N C B F t)
    {x : X} (hxD : x ∈ D) (hxF : x ∈ F) : D = F := by
  obtain ⟨R⟩ := routeFamily_exists N
  obtain ⟨p,hp⟩ := hD R
  obtain ⟨q,hq⟩ := hF R
  have hxp : Occupies N R C t x p := by
    have hx : x ∈ populationBlock N R B C t p := by rwa [hp]
    exact (Finset.mem_filter.mp hx).2
  have hxq : Occupies N R C t x q := by
    have hx : x ∈ populationBlock N R B C t q := by rwa [hq]
    exact (Finset.mem_filter.mp hx).2
  have heq := occupies_unique N C R hxp hxq
  rw [heq] at hp
  exact hp.symm.trans hq

noncomputable def simultaneousBlocks (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) : Finset (Finset X) :=
  B.powerset.filter (fun D => 2 ≤ D.card ∧ SureBlock N C B D t)

lemma mem_simultaneousBlocks (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) :
    D ∈ simultaneousBlocks N C B t ↔ D ⊆ B ∧ 2 ≤ D.card ∧ SureBlock N C B D t := by
  simp [simultaneousBlocks]

lemma simultaneousBlocks_pairwise_disjoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) : (↑(simultaneousBlocks N C B t) : Set (Finset X)).Pairwise Disjoint := by
  intro D hD F hF hne
  apply Finset.disjoint_left.mpr
  intro x hxD hxF
  exact hne (sureBlocks_eq_of_intersection N C B D F
    ((mem_simultaneousBlocks N C B D t).mp hD).2.2
    ((mem_simultaneousBlocks N C B F t).mp hF).2.2 hxD hxF)

section FixedOriginalOrder
variable [LinearOrder X]

noncomputable def originalRepresentative (D : Finset X) (hD : 2 ≤ D.card) : X :=
  D.min' (Finset.card_pos.mp (by omega))

lemma originalRepresentative_mem (D : Finset X) (hD : 2 ≤ D.card) :
    originalRepresentative D hD ∈ D := Finset.min'_mem _ _

/-- All simultaneous blocks lose every original label except their own fixed
least original label. Original tips outside those blocks remain untouched. -/
noncomputable def survivors (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) : Finset X :=
  B.filter (fun x => ∀ D, ∀ hD : D ∈ simultaneousBlocks N C B t,
    x ∈ D → x = originalRepresentative D ((mem_simultaneousBlocks N C B D t).mp hD).2.1)

lemma survivors_subset (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) : survivors N C B t ⊆ B := Finset.filter_subset _ _

lemma representative_survives (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) (hD : D ∈ simultaneousBlocks N C B t) :
    originalRepresentative D ((mem_simultaneousBlocks N C B D t).mp hD).2.1 ∈ survivors N C B t := by
  let x := originalRepresentative D ((mem_simultaneousBlocks N C B D t).mp hD).2.1
  have hxD : x ∈ D := originalRepresentative_mem D _
  apply Finset.mem_filter.mpr
  refine ⟨((mem_simultaneousBlocks N C B D t).mp hD).1 hxD,?_⟩
  intro F hF hxF
  have heq := sureBlocks_eq_of_intersection N C B D F
    ((mem_simultaneousBlocks N C B D t).mp hD).2.2
    ((mem_simultaneousBlocks N C B F t).mp hF).2.2 hxD hxF
  subst F
  rfl

/-- Every simultaneous sure block has exactly one surviving original tip. -/
theorem survivors_inter_sureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) (hD : D ∈ simultaneousBlocks N C B t) :
    survivors N C B t ∩ D =
      {originalRepresentative D ((mem_simultaneousBlocks N C B D t).mp hD).2.1} := by
  ext x
  simp only [Finset.mem_inter,Finset.mem_singleton]
  constructor
  · rintro ⟨hx,hxD⟩
    exact (Finset.mem_filter.mp hx).2 D hD hxD
  · intro hx
    subst x
    exact ⟨representative_survives N C B D t hD,originalRepresentative_mem D _⟩

/-- Deletion of all attained sure blocks has strict original-tip cardinal
progress. It never relies on an arbitrary abstract reduced source. -/
theorem survivors_card_lt (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (t : ℝ) (hex : ∃ D, D ∈ simultaneousBlocks N C B t) :
    (survivors N C B t).card < B.card := by
  obtain ⟨D,hD⟩ := hex
  have hDinfo := (mem_simultaneousBlocks N C B D t).mp hD
  let r := originalRepresentative D hDinfo.2.1
  have hx : ∃ x ∈ D, x ≠ r := by
    by_contra hn
    have hc : D.card ≤ 1 := Finset.card_le_one.mpr (by
      intro x hx y hy
      have hxr : x = r := by by_contra h; exact hn ⟨x,hx,h⟩
      have hyr : y = r := by by_contra h; exact hn ⟨y,hy,h⟩
      exact hxr.trans hyr.symm)
    omega
  obtain ⟨x,hxD,hxr⟩ := hx
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨survivors_subset N C B t,?_⟩
  intro heq
  have hxS : x ∈ survivors N C B t := by rw [heq]; exact hDinfo.1 hxD
  exact hxr ((Finset.mem_filter.mp hxS).2 D hD hxD)

lemma safeAt_subset (N : RootedBinary V E X) (C : Calendar N.graph)
    {A B : Finset X} {t : ℝ} (hAB : A ⊆ B) (hB : SafeAt N C B t) : SafeAt N C A t := by
  intro h hh ht
  apply (Finset.card_le_card (show selectedDescendants N A h ⊆ selectedDescendants N B h from ?_)).trans
    (hB h hh ht)
  intro x hx
  obtain ⟨hxA,hxd⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hAB hxA,hxd⟩

theorem attained_deletion_safe_and_descends (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card)
    (hstart : SafeAt N C B s) :
    let τ := firstGroupingAge N C B hs hc
    SafeAt N C (survivors N C B τ) τ ∧ (survivors N C B τ).card < B.card := by
  dsimp
  have hsafe := safeAt_firstGroupingAge N C hcut B hs hc hstart
  refine ⟨safeAt_subset N C (survivors_subset N C B _) hsafe,?_⟩
  apply survivors_card_lt
  obtain ⟨D,hDB,hD,hblock⟩ := (firstGroupingAge_attained N C B hs hc).2.2.2
  exact ⟨D,(mem_simultaneousBlocks N C B D _).mpr ⟨hDB,hD,hblock⟩⟩

#print axioms sureBlocks_eq_of_intersection
#print axioms simultaneousBlocks_pairwise_disjoint
#print axioms survivors_inter_sureBlock
#print axioms survivors_card_lt
#print axioms attained_deletion_safe_and_descends
end FixedOriginalOrder
end GProgram.G5.AttainedChronology
