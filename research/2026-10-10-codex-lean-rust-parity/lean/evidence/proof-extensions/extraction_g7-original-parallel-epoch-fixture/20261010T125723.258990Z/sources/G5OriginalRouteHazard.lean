import G5SafePastMeetingPermanence
import G5UnknownRateSupport
import Mathlib.Data.Finset.Max

/-!
# Original calendar route-pair hazard and its exact local exponential germ

Contributor: dot, 2026-10-02. Exposure is constructed from every original
edge's actual active interval and positive edge-specific pair rates. A safe
currently separated route pair has zero ENTIRE-past exposure. Finiteness of
original node clocks supplies a right-hand event-free window. The route
functional exp(-hazard) then has its actual current-rate exponential germ.
Identifying this functional with a continuous-time source probability law is
a separate stochastic construction, not a premise hidden in this definition.
-/
namespace GProgram.G5.RouteHazard
open Nanuq.Source
open GProgram.G5
open GProgram.G5.SafePast
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Length of this original edge's active interval below calendar age t. -/
noncomputable def exposure (G : EdgeGraph V E) (C : Calendar G) (t : ℝ) (e : E) : ℝ :=
  max 0 (min t (C.age (G.source e)) - C.age (G.target e))

/-- Actual finite original-edge overlap exposure, retaining parallel IDs. -/
noncomputable def accumulatedHazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (R : RouteFamily N) (x y : X) (t : ℝ) : ℝ := by
  classical
  exact ∑ e : E, if e ∈ R.edges x ∧ e ∈ R.edges y then rate e * exposure N.graph C t e else 0

noncomputable def currentPairRate (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (R : RouteFamily N) (x y : X) (t : ℝ) : ℝ := by
  classical
  exact ∑ e : E, if e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e then rate e else 0

noncomputable def routeSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (R : RouteFamily N) (x y : X) (t : ℝ) : ℝ :=
  Real.exp (-accumulatedHazard N C rate R x y t)

theorem currentPairRate_nonnegative (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (hr : ∀ e, 0 ≤ rate e) (R : RouteFamily N) (x y : X) (t : ℝ) :
    0 ≤ currentPairRate N C rate R x y t := by
  classical
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact hr e
  · exact le_refl _

/-- Strict source rates make zero current rate equivalent to true separation. -/
theorem currentPairRate_zero_iff_separated (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (hr : ∀ e, 0 < rate e)
    (R : RouteFamily N) (x y : X) (t : ℝ) :
    currentPairRate N C rate R x y t = 0 ↔ ¬CoOccupy N R C t x y := by
  classical
  have hn : ∀ e ∈ (Finset.univ : Finset E),
      0 ≤ (if e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e then rate e else 0) := by
    intro e _
    split_ifs
    · exact (hr e).le
    · exact le_refl _
  rw [currentPairRate,Finset.sum_eq_zero_iff_of_nonneg hn]
  constructor
  · intro hz hm
    obtain ⟨e,hex,hey,hea⟩ := hm
    have hez := hz e (Finset.mem_univ e)
    simp only [hex,hey,hea,and_self,if_true] at hez
    exact (hr e).ne' hez
  · intro hs e _
    have he : ¬(e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e) := by
      rintro ⟨hx,hy,ha⟩
      exact hs ⟨e,hx,hy,ha⟩
    simp only [he,if_false]

/-- Full safe-past permanence gives zero overlap duration, rather than merely
zero current occupancy, for every separated original route pair. -/
theorem separated_safe_accumulatedHazard_zero (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hs : ¬CoOccupy N R C t x y) : accumulatedHazard N C rate R x y t = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  by_cases hm : e ∈ R.edges x ∧ e ∈ R.edges y
  · have ht : t ≤ C.age (N.graph.target e) := by
      by_contra hn
      exact (separated_at_safe_age_never_previously_met N C B R hu hsafe hx hy hne hs)
        (C.age (N.graph.target e)) (le_of_lt (lt_of_not_ge hn))
        ⟨e,hm.1,hm.2,le_refl _,C.edge_older e⟩
    have he : exposure N.graph C t e = 0 := by
      apply max_eq_left
      exact sub_nonpos.mpr ((min_le_left _ _).trans ht)
    simp [hm,he]
  · simp only [hm,if_false]

theorem separated_safe_routeSurvival_one (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hs : ¬CoOccupy N R C t x y) : routeSurvival N C rate R x y t = 1 := by
  rw [routeSurvival,separated_safe_accumulatedHazard_zero N C rate B R hu hsafe hx hy hne hs]
  simp

/-- A right event-free window does not assume the unknown clock grid is observed. -/
def EndpointGap (G : EdgeGraph V E) (C : Calendar G) (t ε : ℝ) : Prop :=
  ∀ v : V, t < C.age v → t + ε ≤ C.age v

theorem positive_endpoint_gap_exists (N : RootedBinary V E X)
    (C : Calendar N.graph) (t : ℝ) : ∃ ε : ℝ, 0 < ε ∧ EndpointGap N.graph C t ε := by
  classical
  let S : Finset ℝ := (Finset.univ.image C.age).filter (fun a => t < a)
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS - t,?_,?_⟩
    · exact sub_pos.mpr (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    · intro v hv
      have hm : C.age v ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,hv⟩
      have hmin := Finset.min'_le S (C.age v) hm
      linarith
  · refine ⟨1,by norm_num,?_⟩
    intro v hv
    apply False.elim
    apply hS
    exact ⟨C.age v,Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,hv⟩⟩

/-- The exact slope of original-edge exposure on a right event-free window. -/
theorem exposure_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε)
    (hu : 0 ≤ u) (huε : u < ε) (e : E) :
    exposure N.graph C (t + u) e = exposure N.graph C t e +
      if C.Active t e then u else 0 := by
  classical
  have htu : t ≤ t + u := by linarith
  by_cases hy : C.age (N.graph.target e) ≤ t
  · by_cases hs : t < C.age (N.graph.source e)
    · have hst : t + u < C.age (N.graph.source e) := by
        have hg := hgap (N.graph.source e) hs
        linarith
      simp only [exposure,min_eq_left hs.le,min_eq_left hst.le,
        max_eq_right (sub_nonneg.mpr hy),max_eq_right (sub_nonneg.mpr (hy.trans htu)),
        Calendar.Active,hy,hs,and_self,if_true]
      ring
    · have hst : C.age (N.graph.source e) ≤ t := le_of_not_gt hs
      have ha : ¬C.Active t e := fun h => hs h.2
      simp only [exposure,min_eq_right hst,min_eq_right (hst.trans htu),ha,if_false,add_zero]
  · have hyt : t < C.age (N.graph.target e) := lt_of_not_ge hy
    have hyu : t + u < C.age (N.graph.target e) := by
      have hg := hgap (N.graph.target e) hyt
      linarith
    have ht0 : min t (C.age (N.graph.source e)) - C.age (N.graph.target e) ≤ 0 :=
      sub_nonpos.mpr ((min_le_left _ _).trans hyt.le)
    have htu0 : min (t+u) (C.age (N.graph.source e)) - C.age (N.graph.target e) ≤ 0 :=
      sub_nonpos.mpr ((min_le_left _ _).trans hyu.le)
    have ha : ¬C.Active t e := fun h => hy h.1
    simp only [exposure,max_eq_left ht0,max_eq_left htu0,ha,if_false,add_zero]

/-- Actual calendar exposure produces the current-rate linear germ. -/
theorem accumulatedHazard_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (R : RouteFamily N) (x y : X)
    {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε) (hu : 0 ≤ u) (huε : u < ε) :
    accumulatedHazard N C rate R x y (t+u) = accumulatedHazard N C rate R x y t +
      currentPairRate N C rate R x y t * u := by
  classical
  rw [accumulatedHazard,accumulatedHazard,currentPairRate,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [exposure_add_on_endpoint_gap N C hgap hu huε]
  by_cases hm : e ∈ R.edges x ∧ e ∈ R.edges y <;>
    by_cases ha : C.Active t e <;> simp [hm,ha] <;> ring

/-- The exponential route functional has the exact constructed local source
rate. The actual continuous-time no-merger-law interpretation remains open. -/
theorem routeSurvival_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (R : RouteFamily N) (x y : X)
    {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε) (hu : 0 ≤ u) (huε : u < ε) :
    routeSurvival N C rate R x y (t+u) = routeSurvival N C rate R x y t *
      Real.exp ((-currentPairRate N C rate R x y t) * u) := by
  rw [routeSurvival,accumulatedHazard_add_on_endpoint_gap N C rate R x y hgap hu huε,
    neg_add,Real.exp_add]
  simp only [routeSurvival,neg_mul]

#print axioms currentPairRate_zero_iff_separated
#print axioms separated_safe_accumulatedHazard_zero
#print axioms separated_safe_routeSurvival_one
#print axioms positive_endpoint_gap_exists
#print axioms exposure_add_on_endpoint_gap
#print axioms accumulatedHazard_add_on_endpoint_gap
#print axioms routeSurvival_add_on_endpoint_gap
end GProgram.G5.RouteHazard
