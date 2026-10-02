import G5SafePastHybridDisjointness

/-!
# Pair-only sure exact blocks on actual original route families

Contributor: dot, 2026-10-02. At a valid calendar age, a nonempty selected
original-label set is a sure exact population block iff all its DISTINCT
inside pairs are surely together and every inside/outside pair is surely
separate. No diagonal pair observation is required. This deterministic
source-support identity advances the safe-past theorem using pair predicates;
recovering these predicates from observed genealogy laws is still separate.
-/
namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Actual simultaneous original-population occupancy on one original route
family. This is not a survival-conditioned stochastic moment. -/
def CoOccupy (N : RootedBinary V E X) (R : RouteFamily N)
    (C : Calendar N.graph) (t : ℝ) (x y : X) : Prop :=
  ∃ e : E, e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e

/-- All predicates use distinct original-label pair readouts. -/
def PairSureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ D, x ≠ y → CoOccupy N R C t x y) ∧
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ B, y ∉ D → ¬CoOccupy N R C t x y)

/-- Complete exact-fiber equivalence, with active positions derived from the
original calendar. The only source-age premises guarantee occupancy exists. -/
theorem sureExactBlock_iff_distinct_pair_predicates
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (hu : t < C.age N.root) :
    SureExactBlock N C B D t ↔ PairSureBlock N C B D t := by
  classical
  constructor
  · intro hsure
    constructor
    · intro R x hx y hy _
      obtain ⟨e,he⟩ := hsure R
      have hxm : x ∈ selectedPopulationBlock N R B C t e := by rw [he]; exact hx
      have hym : y ∈ selectedPopulationBlock N R B C t e := by rw [he]; exact hy
      have hxp := (Finset.mem_filter.mp hxm).2
      have hyp := (Finset.mem_filter.mp hym).2
      exact ⟨e,hxp.1,hyp.1,hxp.2⟩
    · intro R x hx y hyB hyD hco
      obtain ⟨e,he⟩ := hsure R
      have hxm : x ∈ selectedPopulationBlock N R B C t e := by rw [he]; exact hx
      have hxp := (Finset.mem_filter.mp hxm).2
      obtain ⟨f,hfx,hfy,hfa⟩ := hco
      have hef := (R.valid x).active_unique C hxp.1 hfx hxp.2 hfa
      subst f
      have hym : y ∈ selectedPopulationBlock N R B C t e :=
        Finset.mem_filter.mpr ⟨hyB,hfy,hxp.2⟩
      exact hyD (by rw [he] at hym; exact hym)
  · intro hpair R
    obtain ⟨x,hxD⟩ := hD
    obtain ⟨e,hem,hea⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists
      C (R.valid x) (hl x (hDB hxD)) hu
    refine ⟨e,?_⟩
    ext y
    constructor
    · intro hym
      have hyp := Finset.mem_filter.mp hym
      by_contra hyD
      exact hpair.2 R x hxD y hyp.1 hyD ⟨e,hem,hyp.2.1,hea⟩
    · intro hyD
      apply Finset.mem_filter.mpr
      refine ⟨hDB hyD,?_,hea⟩
      by_cases hxy : x = y
      · subst y
        exact hem
      · obtain ⟨f,hfx,hfy,hfa⟩ := hpair.1 R x hxD y hyD hxy
        have hef := (R.valid x).active_unique C hem hfx hea hfa
        subst f
        exact hfy

/-- The stage's absence test can be stated entirely in pair predicates. -/
def NoPairSureNontrivialBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s t : ℝ) : Prop :=
  ∀ u : ℝ, s ≤ u → u < t → ∀ D : Finset X, D ⊆ B → 2 ≤ D.card →
    ¬PairSureBlock N C B D u

/-- At valid original-tip ages the pair-only absence test equals the full
sure-exact-block absence test, without a triple or four-label input. -/
theorem noSureNontrivialBlock_iff_pair_predicates
    (N : RootedBinary V E X) (C : Calendar N.graph) (B : Finset X)
    {s t : ℝ} (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hu : t ≤ C.age N.root) :
    NoSureNontrivialBlock N C B s t ↔ NoPairSureNontrivialBlock N C B s t := by
  have heq (u : ℝ) (hs : s ≤ u) (ht : u < t) (D : Finset X)
      (hDB : D ⊆ B) (hc : 2 ≤ D.card) :
      SureExactBlock N C B D u ↔ PairSureBlock N C B D u := by
    apply sureExactBlock_iff_distinct_pair_predicates N C B D hDB
    · apply Finset.card_pos.mp
      omega
    · intro x hx
      exact (hl x hx).trans hs
    · exact ht.trans_le hu
  constructor
  · intro hquiet u hs ht D hDB hc hp
    exact hquiet u hs ht D hDB hc ((heq u hs ht D hDB hc).mpr hp)
  · intro hquiet u hs ht D hDB hc hp
    exact hquiet u hs ht D hDB hc ((heq u hs ht D hDB hc).mp hp)

/-- The advanced entire-safe-past invariant needs only the distinct-label
pair sure-together / sure-separate predicates on its stage interval. -/
theorem safeAt_of_no_earlier_pair_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hu : t ≤ C.age N.root)
    (hquiet : NoPairSureNontrivialBlock N C B s t) : SafeAt N C B t :=
  safeAt_of_no_earlier_sure_block N C hcut B hstart
    ((noSureNontrivialBlock_iff_pair_predicates N C B hl hu).mpr hquiet)

#print axioms sureExactBlock_iff_distinct_pair_predicates
#print axioms noSureNontrivialBlock_iff_pair_predicates
#print axioms safeAt_of_no_earlier_pair_sure_block
end GProgram.G5.SafePast
