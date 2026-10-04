import G1SharpCoreCombDefinition
import Mathlib.Analysis.Convex.Segment

/-! Elementary geometry of actual straight segments between parabola points.
Laminar endpoint intervals give noncrossing original edge segments, while
an explicit downward ray at every vertex witnesses access to the unbounded
complement. All statements concern points of ℝ×ℝ and ordinary segments. -/
namespace G1ConvexOriginalEdgeDrawing
open scoped Classical

def parabola (a : ℝ) : ℝ × ℝ := (a,a^2)

lemma actual_segment_coordinates (a b : ℝ) (hab : a ≤ b) (p : ℝ × ℝ)
    (hp : p ∈ segment ℝ (parabola a) (parabola b)) :
    a ≤ p.1 ∧ p.1 ≤ b ∧ p.2 = p.1*(a+b)-a*b := by
  obtain ⟨s,t,hs,ht,hst,rfl⟩ := hp
  have hs' : s = 1-t := by linarith
  subst s
  change a ≤ (1-t)*a+t*b ∧ (1-t)*a+t*b ≤ b ∧
    (1-t)*a^2+t*b^2 = ((1-t)*a+t*b)*(a+b)-a*b
  refine ⟨?_,?_,?_⟩
  · nlinarith [mul_nonneg ht (sub_nonneg.mpr hab)]
  · nlinarith [mul_nonneg hs (sub_nonneg.mpr hab)]
  · ring

lemma segment_at_left (a b : ℝ) (hab : a ≤ b) (p : ℝ × ℝ)
    (hp : p ∈ segment ℝ (parabola a) (parabola b)) (hx : p.1 = a) : p = parabola a := by
  have hy := (actual_segment_coordinates a b hab p hp).2.2
  apply Prod.ext hx
  dsimp [parabola]
  rw [hx] at hy
  nlinarith

lemma segment_at_right (a b : ℝ) (hab : a ≤ b) (p : ℝ × ℝ)
    (hp : p ∈ segment ℝ (parabola a) (parabola b)) (hx : p.1 = b) : p = parabola b := by
  have hy := (actual_segment_coordinates a b hab p hp).2.2
  apply Prod.ext hx
  dsimp [parabola]
  rw [hx] at hy
  nlinarith

lemma nested_chord_intersection_endpoints (a b c d x : ℝ)
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b)
    (hne : a ≠ c ∨ b ≠ d) (hcx : c ≤ x) (hxd : x ≤ d)
    (heq : x*(a+b)-a*b = x*(c+d)-c*d) :
    (x = a ∧ a = c) ∨ (x = b ∧ b = d) := by
  by_cases hlow : a = c
  · subst c
    have hbd : b ≠ d := by rcases hne with h | h; exact False.elim (h rfl); exact h
    have hp : (b-d)*(x-a) = 0 := by nlinarith [heq]
    have hba : b-d ≠ 0 := sub_ne_zero.mpr hbd
    exact Or.inl ⟨sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hba),rfl⟩
  · by_cases hhigh : b = d
    · subst d
      have hp : (c-a)*(b-x) = 0 := by nlinarith [heq]
      have hca : c-a ≠ 0 := sub_ne_zero.mpr (Ne.symm hlow)
      exact Or.inr ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hca)).symm,rfl⟩
    · have hdb' : d < b := lt_of_le_of_ne hdb (Ne.symm hhigh)
      have hac' : a < c := lt_of_le_of_ne hac hlow
      have hxa : 0 < x-a := sub_pos.mpr (hac'.trans_le hcx)
      have hfirst := mul_pos (sub_pos.mpr hdb') hxa
      have hsecond := mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hxd)
      exfalso
      nlinarith [heq]

theorem laminar_actual_segments_intersect_only_at_endpoints (a b c d : ℝ)
    (hab : a < b) (hcd : c < d) (hne : a ≠ c ∨ b ≠ d)
    (hlam : b ≤ c ∨ d ≤ a ∨ (a ≤ c ∧ d ≤ b) ∨ (c ≤ a ∧ b ≤ d))
    (p : ℝ × ℝ) (hp : p ∈ segment ℝ (parabola a) (parabola b))
    (hq : p ∈ segment ℝ (parabola c) (parabola d)) :
    (p = parabola a ∨ p = parabola b) ∧ (p = parabola c ∨ p = parabola d) := by
  obtain ⟨hax,hxb,hy⟩ := actual_segment_coordinates a b hab.le p hp
  obtain ⟨hcx,hxd,hy'⟩ := actual_segment_coordinates c d hcd.le p hq
  rcases hlam with hbc | hda | ⟨hac,hdb⟩ | ⟨hca,hbd⟩
  · have hxb' : p.1 = b := by linarith
    have hxc' : p.1 = c := by linarith
    exact ⟨Or.inr (segment_at_right a b hab.le p hp hxb'),Or.inl (segment_at_left c d hcd.le p hq hxc')⟩
  · have hxa' : p.1 = a := by linarith
    have hxd' : p.1 = d := by linarith
    exact ⟨Or.inl (segment_at_left a b hab.le p hp hxa'),Or.inr (segment_at_right c d hcd.le p hq hxd')⟩
  · have hend := nested_chord_intersection_endpoints a b c d p.1 hac hcd hdb hne hcx hxd (hy.symm.trans hy')
    rcases hend with ⟨hxa,he⟩ | ⟨hxb,he⟩
    · exact ⟨Or.inl (segment_at_left a b hab.le p hp hxa),Or.inl (segment_at_left c d hcd.le p hq (hxa.trans he))⟩
    · exact ⟨Or.inr (segment_at_right a b hab.le p hp hxb),Or.inr (segment_at_right c d hcd.le p hq (hxb.trans he))⟩
  · have hne' : c ≠ a ∨ d ≠ b := by simpa [ne_comm] using hne
    have hend := nested_chord_intersection_endpoints c d a b p.1 hca hab hbd hne' hax hxb (hy'.symm.trans hy)
    rcases hend with ⟨hxc,he⟩ | ⟨hxd,he⟩
    · exact ⟨Or.inl (segment_at_left a b hab.le p hp (hxc.trans he)),Or.inl (segment_at_left c d hcd.le p hq hxc)⟩
    · exact ⟨Or.inr (segment_at_right a b hab.le p hp (hxd.trans he)),Or.inr (segment_at_right c d hcd.le p hq hxd)⟩

def tangentHeight (a : ℝ) (p : ℝ × ℝ) : ℝ := p.2-2*a*p.1+a^2

lemma every_parabola_point_above_tangent (a b : ℝ) :
    tangentHeight a (parabola b) = (b-a)^2 := by dsimp [tangentHeight,parabola]; ring

theorem entire_actual_segment_above_tangent (a b c : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ segment ℝ (parabola b) (parabola c)) : 0 ≤ tangentHeight a p := by
  obtain ⟨s,t,hs,ht,hst,rfl⟩ := hp
  have h1 := mul_nonneg hs (sq_nonneg (b-a))
  have h2 := mul_nonneg ht (sq_nonneg (c-a))
  have hheight : tangentHeight a (s • parabola b+t • parabola c) = s*(b-a)^2+t*(c-a)^2 := by
    have hs' : s = 1-t := by linarith
    subst s
    dsimp [tangentHeight,parabola]
    ring
  rw [hheight]
  exact add_nonneg h1 h2

def outerRay (a s : ℝ) : ℝ × ℝ := (a,a^2-s)

theorem unbounded_outer_ray_avoids_every_actual_segment (a b c s : ℝ) (hs : 0 < s) :
    outerRay a s ∉ segment ℝ (parabola b) (parabola c) := by
  intro hp
  have h := entire_actual_segment_above_tangent a b c _ hp
  dsimp [tangentHeight,outerRay] at h
  nlinarith

theorem parabola_point_on_actual_segment_is_endpoint (a b c : ℝ)
    (hp : parabola a ∈ segment ℝ (parabola b) (parabola c)) : a = b ∨ a = c := by
  have line : a^2 = a*(b+c)-b*c := by
    rcases le_total b c with hbc | hcb
    · exact (actual_segment_coordinates b c hbc (parabola a) hp).2.2
    · rw [segment_symm] at hp
      have h := (actual_segment_coordinates c b hcb (parabola a) hp).2.2
      dsimp [parabola] at h
      nlinarith
  have hz : (a-b)*(a-c) = 0 := by nlinarith [line]
  exact (mul_eq_zero.mp hz).imp sub_eq_zero.mp sub_eq_zero.mp

#print axioms laminar_actual_segments_intersect_only_at_endpoints
#print axioms unbounded_outer_ray_avoids_every_actual_segment
end G1ConvexOriginalEdgeDrawing
