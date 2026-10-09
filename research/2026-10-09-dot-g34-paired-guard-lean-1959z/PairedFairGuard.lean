import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

/-! Algebraic all-length core of the accepted paired private fair-cell guard.
The original source/tomography adapter is not assumed proved by this module. -/
namespace DotG34.PairedFairGuard

def f (r : ℝ) : ℝ := 3*r^2-3*r+1

lemma f_pos {r : ℝ} (hr : 1 ≤ r) : 0 < f r := by
  unfold f
  nlinarith [sq_nonneg (r-1)]

lemma f_mul_gap (a b : ℝ) :
    f a * f b - f (a*b) = 3*(a-1)*(b-1)*(2*a*b-a-b) := by
  unfold f
  ring

lemma f_mul_strict {a b : ℝ} (ha : 1<a) (hb : 1<b) :
    f (a*b) < f a * f b := by
  have hab : 0 < 2*a*b-a-b := by nlinarith
  have hg : 0 < 3*(a-1)*(b-1)*(2*a*b-a-b) := by positivity
  rw [← f_mul_gap] at hg
  linarith

structure Cell where
  p : ℝ
  u : ℝ
  p_pos : 0 < p
  p_le : p ≤ 1/4
  u_pos : 0 < u

def r (c : Cell) : ℝ := 1+2*c.p*c.u
def s (c : Cell) : ℝ := 1+6*c.p*c.u+3*c.p*c.u^2

lemma r_gt (c : Cell) : 1 < r c := by
  have := mul_pos c.p_pos c.u_pos
  unfold r
  nlinarith

lemma cell_gap (c : Cell) : s c-f (r c)=3*c.p*(1-4*c.p)*c.u^2 := by
  unfold s r f
  ring

lemma cell_bound (c : Cell) : f (r c) ≤ s c := by
  have hp : 0 ≤ 1-4*c.p := by linarith [c.p_le]
  have hcp := c.p_pos
  have hg : 0 ≤ 3*c.p*(1-4*c.p)*c.u^2 := by positivity
  rw [← cell_gap] at hg
  linarith

lemma cell_equality (c : Cell) : s c=f (r c) ↔ c.p=1/4 := by
  have hcp := c.p_pos
  have hcu := c.u_pos
  have hfac : 0 < 3*c.p*c.u^2 := by positivity
  constructor
  · intro h
    have hz : (3*c.p*c.u^2)*(1-4*c.p)=0 := by
      calc
        _ = s c-f (r c) := by rw [cell_gap]; ring
        _ = 0 := by rw [h]; ring
    have := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hfac)
    linarith
  · intro h
    have hg := cell_gap c
    rw [h] at hg
    norm_num at hg
    linarith

def R : List Cell → ℝ
  | [] => 1
  | c::cs => r c * R cs

def S : List Cell → ℝ
  | [] => 1
  | c::cs => s c * S cs

lemma R_ge (cs : List Cell) : 1 ≤ R cs := by
  induction cs with
  | nil => simp [R]
  | cons c cs ih =>
      have hc := r_gt c
      have hmul : 1*1 ≤ r c * R cs := mul_le_mul (le_of_lt hc) ih (by norm_num) (by linarith)
      simpa [R] using hmul

lemma R_gt_cons (c : Cell) (cs : List Cell) : 1 < R (c::cs) := by
  have h := R_ge cs
  have hc := r_gt c
  have hm : r c * 1 ≤ r c * R cs := mul_le_mul_of_nonneg_left h (by linarith)
  simp only [mul_one] at hm
  change 1 < r c * R cs
  linarith

lemma word_bound (cs : List Cell) : f (R cs) ≤ S cs := by
  induction cs with
  | nil => norm_num [R,S,f]
  | cons c cs ih =>
      cases cs with
      | nil => simpa [R,S] using cell_bound c
      | cons d ds =>
          have hc := cell_bound c
          have hfp := f_pos (le_of_lt (r_gt c))
          have hft := f_pos (R_ge (d::ds))
          have hmul : f (r c)*f (R (d::ds)) ≤ s c*S (d::ds) :=
            mul_le_mul hc ih (le_of_lt hft) (le_trans (le_of_lt hfp) hc)
          have hstrict := f_mul_strict (r_gt c) (R_gt_cons d ds)
          exact le_trans (le_of_lt hstrict) hmul

lemma word_strict (c d : Cell) (cs : List Cell) :
    f (R (c::d::cs)) < S (c::d::cs) := by
  have hc := cell_bound c
  have ht := word_bound (d::cs)
  have hfp := f_pos (le_of_lt (r_gt c))
  have hft := f_pos (R_ge (d::cs))
  have hmul : f (r c)*f (R (d::cs)) ≤ s c*S (d::cs) :=
    mul_le_mul hc ht (le_of_lt hft) (le_trans (le_of_lt hfp) hc)
  exact lt_of_lt_of_le (f_mul_strict (r_gt c) (R_gt_cons d cs)) hmul

/-- Unknown finite word length is quantified, not supplied as a bound. -/
theorem equality_forces_one_fair (cs : List Cell)
    (hr : 1 < R cs) (he : S cs = f (R cs)) :
    ∃ c : Cell, cs=[c] ∧ c.p=1/4 := by
  cases cs with
  | nil => simp [R] at hr
  | cons c cs =>
      cases cs with
      | nil =>
          refine ⟨c,rfl,?_⟩
          apply (cell_equality c).mp
          simpa [S,R] using he
      | cons d ds =>
          have h := word_strict c d ds
          rw [he] at h
          exact False.elim (lt_irrefl _ h)

lemma common_jensen_gap (x y g : ℝ) :
    g*x^3+(1-g)*y^3-(g*x+(1-g)*y)^3 =
      g*(1-g)*(x-y)^2*((1+g)*x+(2-g)*y) := by ring

lemma common_jensen_equality {x y g : ℝ}
    (hx : 0<x) (hy : 0<y) (hg : 0<g) (hg1 : g<1) :
    g*x^3+(1-g)*y^3=(g*x+(1-g)*y)^3 ↔ x=y := by
  have h2g : 0 < 2-g := by linarith
  have h1g : 0 < 1-g := by linarith
  have ha : 0 < (1+g)*x+(2-g)*y := by positivity
  have hf : 0 < g*(1-g)*((1+g)*x+(2-g)*y) := by positivity
  constructor
  · intro he
    have hz : (g*(1-g)*((1+g)*x+(2-g)*y))*(x-y)^2=0 := by
      calc
        _ = g*x^3+(1-g)*y^3-(g*x+(1-g)*y)^3 := by rw [common_jensen_gap]; ring
        _ = 0 := sub_eq_zero.mpr he
    have hsq := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hf)
    nlinarith [sq_nonneg (x-y)]
  · rintro rfl
    ring

def P : List ℝ → ℝ
  | [] => 1
  | a::as => a * P as

lemma P_ge (as : List ℝ) (h : ∀ a ∈ as, 1 ≤ a) : 1 ≤ P as := by
  induction as with
  | nil => simp [P]
  | cons a as ih =>
      have ha := h a (by simp)
      have ht := ih (fun b hb => h b (by simp [hb]))
      have hm : 1*1 ≤ a*P as := mul_le_mul ha ht (by norm_num) (by linarith)
      simpa [P] using hm

/-- COMMON ratios >=1 cannot cancel even with unknown finite word length. -/
theorem product_one_forces_each (as : List ℝ) (h : ∀ a ∈ as, 1 ≤ a)
    (he : P as=1) : ∀ a ∈ as, a=1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
      have ha := h a (by simp)
      have ht := P_ge as (fun b hb => h b (by simp [hb]))
      have hm : a ≤ a*P as := by nlinarith
      have ha1 : a=1 := by simpa [P] using (show a=1 from by
        change a*P as=1 at he
        nlinarith)
      have ht1 : P as=1 := by simpa [P,ha1] using he
      intro b hb
      rcases List.mem_cons.mp hb with hb | hb
      · simpa [hb] using ha1
      · exact ih (fun c hc => h c (by simp [hc])) ht1 b hb

#print axioms equality_forces_one_fair
#print axioms common_jensen_equality
end DotG34.PairedFairGuard
