import PairedFairGuard
import G4IndependentRoutingBridge

namespace DotG34.PairedGuardRouting
open DotG34.PairedFairGuard GProgram.G4.IndependentRouting

def arm (q : ℝ) (n : ℕ) : ℝ := q^(n.choose 2)

/-- Derived from the existing finite sum over independent CURRENT-root routes. -/
theorem routed_two (q g : ℝ) :
    privateNoMerger 2 g (arm q) (arm q) = q+2*(g*(1-g))*(1-q) := by
  rw [generic_two]
  norm_num [arm, Nat.choose]
  ring

theorem routed_three (q g : ℝ) :
    privateNoMerger 3 g (arm q) (arm q) = (1-3*(g*(1-g)))*q^3+3*(g*(1-g))*q := by
  rw [generic_three]
  norm_num [arm, Nat.choose]
  ring

lemma coin_bounds {g : ℝ} (hg : 0<g) (hg1 : g<1) :
    0<g*(1-g) ∧ g*(1-g)≤1/4 := by
  constructor
  · exact mul_pos hg (by linarith)
  · nlinarith [sq_nonneg (g-1/2)]

lemma coin_fair {g : ℝ} : g*(1-g)=1/4 ↔ g=1/2 := by
  constructor
  · intro h
    nlinarith [sq_nonneg (g-1/2)]
  · rintro rfl
    norm_num

noncomputable def cellOf (q g : ℝ) (hq : 0<q) (hq1 : q<1) (hg : 0<g) (hg1 : g<1) : Cell where
  p := g*(1-g)
  u := q⁻¹-1
  p_pos := (coin_bounds hg hg1).1
  p_le := (coin_bounds hg hg1).2
  u_pos := by
    have hi : q*q⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hq)
    have hn : 0<q⁻¹ := inv_pos.mpr hq
    nlinarith

theorem normalized_two (q g : ℝ) (hq : 0<q) (hq1 : q<1) (hg : 0<g) (hg1 : g<1) :
    privateNoMerger 2 g (arm q) (arm q)/q = r (cellOf q g hq hq1 hg hg1) := by
  rw [routed_two]
  simp only [r,cellOf]
  field_simp
  <;> ring

theorem normalized_three (q g : ℝ) (hq : 0<q) (hq1 : q<1) (hg : 0<g) (hg1 : g<1) :
    privateNoMerger 3 g (arm q) (arm q)/q^3 = s (cellOf q g hq hq1 hg hg1) := by
  rw [routed_three]
  simp only [s,cellOf]
  field_simp
  <;> ring

/-- The normalized cell inequality now refers to the existing routing sum. -/
theorem actual_routing_guard (q g : ℝ) (hq : 0<q) (hq1 : q<1) (hg : 0<g) (hg1 : g<1) :
    f (privateNoMerger 2 g (arm q) (arm q)/q) ≤
      privateNoMerger 3 g (arm q) (arm q)/q^3 := by
  rw [normalized_two q g hq hq1 hg hg1, normalized_three q g hq hq1 hg hg1]
  exact cell_bound _

theorem actual_routing_guard_equality (q g : ℝ) (hq : 0<q) (hq1 : q<1) (hg : 0<g) (hg1 : g<1) :
    privateNoMerger 3 g (arm q) (arm q)/q^3 =
      f (privateNoMerger 2 g (arm q) (arm q)/q) ↔ g=1/2 := by
  rw [normalized_two q g hq hq1 hg hg1, normalized_three q g hq hq1 hg hg1,
    cell_equality]
  exact coin_fair

structure StrictEqualArm where
  q : ℝ
  g : ℝ
  q_pos : 0<q
  q_lt : q<1
  g_pos : 0<g
  g_lt : g<1

noncomputable def encoded (c : StrictEqualArm) : Cell :=
  cellOf c.q c.g c.q_pos c.q_lt c.g_pos c.g_lt

/-- All finite strict equal-arm physical parameter lists are covered. -/
theorem word_guard_forces_one (cs : List StrictEqualArm)
    (hr : 1<R (cs.map encoded)) (he : S (cs.map encoded)=f (R (cs.map encoded))) :
    ∃ c : StrictEqualArm, cs=[c] ∧ c.g=1/2 := by
  obtain ⟨d,hd,hfair⟩ := equality_forces_one_fair (cs.map encoded) hr he
  cases cs with
  | nil => simp at hd
  | cons c cs =>
      cases cs with
      | nil =>
          have hed : encoded c=d := by simpa using hd
          refine ⟨c,rfl,coin_fair.mp ?_⟩
          have hh : (encoded c).p=1/4 := hed ▸ hfair
          exact hh
      | cons c' cs' => simp at hd

#print axioms routed_three
#print axioms actual_routing_guard_equality
end DotG34.PairedGuardRouting
