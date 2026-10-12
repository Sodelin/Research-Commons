import G5PairOnlySureBlockChronology

/-!
# Attained chronology on the original finite calendar
Contributor: dot / OpenAI, 2026-10-03.
Original edge occurrences and the ancestral population have separate carriers.
The first grouping age is constructed from finite actual vertex ages and the
older-side convention. Its attainment is a conclusion, never an input field.
This module does not assert observation-law recovery or displayed quartets.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.SafePast
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Strict original ages force every proper ancestor to be older. -/
theorem proper_descendant_age_lt (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (hab : N.graph.DReach a b) (hne : a ≠ b) : C.age b < C.age a := by
  rcases Relation.ReflTransGen.cases_head hab with h | ⟨v,he,hv⟩
  · exact False.elim (hne h)
  · obtain ⟨e,hs,ht⟩ := he
    have hh := C.edge_older e
    rw [hs,ht] at hh
    exact (C.age_le_of_directed hv).trans_lt hh

/-- The actual initial invariant follows from contemporaneous original tips,
not from a supplied invariant or modified source. -/
theorem safeAt_sampling_age (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s : ℝ) (htips : ∀ x ∈ B, C.age (N.leaf x) = s) :
    SafeAt N C B s := by
  intro h hh hage
  have hz : selectedDescendants N B h = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxB,hd⟩ := Finset.mem_filter.mp hx
    have hne : h ≠ N.leaf x := by
      intro he
      have hout := hh.2
      rw [he,(N.leaf_degrees x).2] at hout
      omega
    have hlt := proper_descendant_age_lt N C hd hne
    rw [htips x hxB] at hlt
    exact (not_lt_of_ge hage) hlt
  rw [hz]
  simp

/-- Original populations use some e; none is the original ancestral population.
All labels pool at and above the root, without pretending an E edge exists. -/
def Occupies (N : RootedBinary V E X) (R : RouteFamily N) (C : Calendar N.graph)
    (t : ℝ) (x : X) : Option E → Prop
  | some e => e ∈ R.edges x ∧ C.Active t e
  | none => C.age N.root ≤ t

noncomputable def populationBlock (N : RootedBinary V E X) (R : RouteFamily N)
    (B : Finset X) (C : Calendar N.graph) (t : ℝ) (p : Option E) : Finset X :=
  B.filter (fun x => Occupies N R C t x p)

def SureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  ∀ R : RouteFamily N, ∃ p : Option E, populationBlock N R B C t p = D

lemma ancestral_block (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (B : Finset X) {t : ℝ} (ht : C.age N.root ≤ t) :
    populationBlock N R B C t none = B := by
  simp [populationBlock,Occupies,ht]

theorem terminal_sure_block (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) {t : ℝ} (ht : C.age N.root ≤ t) : SureBlock N C B B t :=
  fun R => ⟨none,ancestral_block N C R B ht⟩

lemma sureExactBlock_implies_sureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) (h : SureExactBlock N C B D t) : SureBlock N C B D t := by
  intro R
  obtain ⟨e,he⟩ := h R
  refine ⟨some e,?_⟩
  have hp : populationBlock N R B C t (some e) = selectedPopulationBlock N R B C t e := by
    ext x
    simp [populationBlock,Occupies,selectedPopulationBlock]
  exact hp.trans he

/-- The hidden original vertex grid is used to prove attainment, not supplied
as an observed input. The arbitrary stage start is included explicitly. -/
noncomputable def eventAges {G : EdgeGraph V E} (C : Calendar G)
    (s : ℝ) : Finset ℝ := insert s (Finset.univ.image C.age)

lemma vertex_age_mem_events {G : EdgeGraph V E} (C : Calendar G) (s : ℝ) (v : V) :
    C.age v ∈ eventAges C s := by
  simp [eventAges]

lemma eligible_floor_nonempty {G : EdgeGraph V E} (C : Calendar G) {s t : ℝ}
    (hst : s ≤ t) : ((eventAges C s).filter (fun u => u ≤ t)).Nonempty :=
  ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,hst⟩⟩

noncomputable def eventFloor {G : EdgeGraph V E} (C : Calendar G) {s t : ℝ}
    (hst : s ≤ t) : ℝ :=
  ((eventAges C s).filter (fun u => u ≤ t)).max' (eligible_floor_nonempty C hst)

lemma eventFloor_mem {G : EdgeGraph V E} (C : Calendar G) {s t : ℝ} (hst : s ≤ t) :
    eventFloor C hst ∈ eventAges C s ∧ eventFloor C hst ≤ t :=
  Finset.mem_filter.mp (Finset.max'_mem _ _)

lemma le_eventFloor {G : EdgeGraph V E} (C : Calendar G) {s t : ℝ} (hst : s ≤ t) :
    s ≤ eventFloor C hst :=
  Finset.le_max' ((eventAges C s).filter (fun u => u ≤ t)) s
    (Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,hst⟩)

lemma vertex_age_le_floor_iff {G : EdgeGraph V E} (C : Calendar G) {s t : ℝ}
    (hst : s ≤ t) (v : V) : C.age v ≤ eventFloor C hst ↔ C.age v ≤ t := by
  constructor
  · exact fun h => h.trans (eventFloor_mem C hst).2
  · intro h
    exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨vertex_age_mem_events C s v,h⟩)

/-- Older-side original-edge activity is identical at t and the attained
preceding original event. This includes every edge occurrence in parallel. -/
theorem active_at_eventFloor_iff {G : EdgeGraph V E} (C : Calendar G) {s t : ℝ}
    (hst : s ≤ t) (e : E) : C.Active (eventFloor C hst) e ↔ C.Active t e := by
  simp only [Calendar.Active,vertex_age_le_floor_iff C hst,←not_le]

theorem populationBlock_eventFloor (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (B : Finset X) {s t : ℝ} (hst : s ≤ t) (p : Option E) :
    populationBlock N R B C (eventFloor C hst) p = populationBlock N R B C t p := by
  apply Finset.filter_congr
  intro x _
  cases p with
  | none => exact vertex_age_le_floor_iff C hst N.root
  | some e => exact and_congr_right (fun _ => active_at_eventFloor_iff C hst e)

theorem sureBlock_eventFloor_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) {s t : ℝ} (hst : s ≤ t) :
    SureBlock N C B D (eventFloor C hst) ↔ SureBlock N C B D t := by
  unfold SureBlock
  simp only [populationBlock_eventFloor N C _ B hst]

noncomputable def groupingEvents (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s : ℝ) : Finset ℝ :=
  (eventAges C s).filter (fun t => s ≤ t ∧ t ≤ C.age N.root ∧
    ∃ D : Finset X, D ⊆ B ∧ 2 ≤ D.card ∧ SureBlock N C B D t)

lemma groupingEvents_nonempty (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card) :
    (groupingEvents N C B s).Nonempty := by
  refine ⟨C.age N.root,Finset.mem_filter.mpr ⟨vertex_age_mem_events C s N.root,hs,le_rfl,?_⟩⟩
  exact ⟨B,Finset.Subset.refl _,hc,terminal_sure_block N C B le_rfl⟩

noncomputable def firstGroupingAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card) : ℝ :=
  (groupingEvents N C B s).min' (groupingEvents_nonempty N C B hs hc)

/-- Attainment, root-boundedness and the exact sure block are all proved from
finite source events. There is no assumption that a minimum is attained. -/
theorem firstGroupingAge_attained (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card) :
    firstGroupingAge N C B hs hc ∈ eventAges C s ∧
    s ≤ firstGroupingAge N C B hs hc ∧ firstGroupingAge N C B hs hc ≤ C.age N.root ∧
    ∃ D : Finset X, D ⊆ B ∧ 2 ≤ D.card ∧ SureBlock N C B D (firstGroupingAge N C B hs hc) :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

/-- The first attained age is genuinely first over ALL real ages, not merely
first on a provided grid. -/
theorem no_sure_block_before_firstGroupingAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card)
    {u : ℝ} (hsu : s ≤ u) (hu : u < firstGroupingAge N C B hs hc)
    {D : Finset X} (hDB : D ⊆ B) (hD : 2 ≤ D.card) : ¬SureBlock N C B D u := by
  intro hd
  have hat := firstGroupingAge_attained N C B hs hc
  have hroot : u ≤ C.age N.root := hu.le.trans hat.2.2.1
  have hmem : eventFloor C hsu ∈ groupingEvents N C B s := by
    apply Finset.mem_filter.mpr
    exact ⟨(eventFloor_mem C hsu).1,le_eventFloor C hsu,
      (eventFloor_mem C hsu).2.trans hroot,D,hDB,hD,(sureBlock_eventFloor_iff N C B D hsu).mpr hd⟩
  have hmin := Finset.min'_le (groupingEvents N C B s) _ hmem
  have hfloor := (eventFloor_mem C hsu).2
  exact (not_lt_of_ge (hmin.trans hfloor)) hu

/-- Entire-past safety reaches the first attained age, including the root
terminal age, by the actual positive hybrid-child bridge argument. -/
theorem safeAt_firstGroupingAge (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s : ℝ} (hs : s ≤ C.age N.root) (hc : 2 ≤ B.card)
    (hstart : SafeAt N C B s) : SafeAt N C B (firstGroupingAge N C B hs hc) := by
  apply safeAt_of_no_earlier_sure_block N C hcut B hstart
  intro u hsu hu D hDB hD hblock
  exact no_sure_block_before_firstGroupingAge N C B hs hc hsu hu hDB hD
    (sureExactBlock_implies_sureBlock N C B D u hblock)

#print axioms safeAt_sampling_age
#print axioms firstGroupingAge_attained
#print axioms no_sure_block_before_firstGroupingAge
#print axioms safeAt_firstGroupingAge
end GProgram.G5.AttainedChronology
