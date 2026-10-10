import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! Classical strict Fourier--Motzkin elimination, formalized by dot, 2026-10-09.
A total rational Boolean decider with complete correctness over ordered fields
and a derived real/rational feasibility equivalence. Rational witness existence
is proved, but this module does not implement a witness-returning function.
Source-chart compilation and full G6 assembly are separate. See exact receipts. -/
namespace UnifiedLean.G6.StrictAffineElimination
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def Rel (s : Bool) (x y : K) : Prop := if s then x < y else x ≤ y

lemma rel_le {s : Bool} {x y : K} (h : Rel s x y) : x ≤ y := by
  cases s <;> simp [Rel] at h ⊢ <;> first | exact h | exact le_of_lt h

lemma rel_of_lt (s : Bool) {x y : K} (h : x < y) : Rel s x y := by
  cases s <;> simp [Rel]
  exact le_of_lt h
  exact h

lemma rel_or_left {s t : Bool} {x y : K} (h : Rel (s || t) x y) : Rel s x y := by
  cases s <;> cases t <;> simp [Rel] at h ⊢ <;> first | exact h | exact le_of_lt h

lemma rel_or_right {s t : Bool} {x y : K} (h : Rel (s || t) x y) : Rel t x y := by
  cases s <;> cases t <;> simp [Rel] at h ⊢ <;> first | exact h | exact le_of_lt h

lemma rel_trans {s t : Bool} {x y z : K} (h : Rel s x y) (k : Rel t y z) :
    Rel (s || t) x z := by
  cases s <;> cases t <;> simp [Rel] at h k ⊢ <;> order

/-- The complete one-coordinate projection criterion, including weak singleton
solutions, open ends, empty lower/upper lists and unbounded domains. -/
theorem finite_bounds_iff (L U : Finset (K × Bool)) :
    (∃ z : K, (∀ l ∈ L, Rel l.2 l.1 z) ∧ (∀ u ∈ U, Rel u.2 z u.1)) ↔
    (∀ l ∈ L, ∀ u ∈ U, Rel (l.2 || u.2) l.1 u.1) := by
  classical
  constructor
  · rintro ⟨z, hL, hU⟩ l hl u hu
    exact rel_trans (hL l hl) (hU u hu)
  · intro h
    by_cases hL : L.Nonempty
    · let A := L.image Prod.fst
      have hA : A.Nonempty := hL.image _
      let a := A.max' hA
      have ha : a ∈ A := A.max'_mem hA
      obtain ⟨l₀, hl₀, hlval⟩ := Finset.mem_image.mp ha
      have lower_le : ∀ l ∈ L, l.1 ≤ a := by
        intro l hl
        exact A.le_max' _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
      by_cases hU : U.Nonempty
      · let B := U.image Prod.fst
        have hB : B.Nonempty := hU.image _
        let b := B.min' hB
        have hb : b ∈ B := B.min'_mem hB
        obtain ⟨u₀, hu₀, huval⟩ := Finset.mem_image.mp hb
        have upper_le : ∀ u ∈ U, b ≤ u.1 := by
          intro u hu
          exact B.min'_le _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
        have hab : a ≤ b := by
          have hz := rel_le (h l₀ hl₀ u₀ hu₀)
          simpa only [hlval, huval] using hz
        by_cases hlt : a < b
        · obtain ⟨z, haz, hzb⟩ := exists_between hlt
          refine ⟨z, ?_, ?_⟩
          · intro l hl
            exact rel_of_lt _ (lt_of_le_of_lt (lower_le l hl) haz)
          · intro u hu
            exact rel_of_lt _ (lt_of_lt_of_le hzb (upper_le u hu))
        · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
          refine ⟨a, ?_, ?_⟩
          · intro l hl
            have hz := rel_or_left (h l hl u₀ hu₀)
            simpa only [huval, ← heq] using hz
          · intro u hu
            have hz := rel_or_right (h l₀ hl₀ u hu)
            simpa only [hlval] using hz
      · refine ⟨a + 1, ?_, ?_⟩
        · intro l hl
          apply rel_of_lt
          have := lower_le l hl
          linarith
        · intro u hu
          exact False.elim (hU ⟨u, hu⟩)
    · by_cases hU : U.Nonempty
      · let B := U.image Prod.fst
        have hB : B.Nonempty := hU.image _
        let b := B.min' hB
        have upper_le : ∀ u ∈ U, b ≤ u.1 := by
          intro u hu
          exact B.min'_le _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
        refine ⟨b - 1, ?_, ?_⟩
        · intro l hl
          exact False.elim (hL ⟨l, hl⟩)
        · intro u hu
          apply rel_of_lt
          have := upper_le u hu
          linarith
      · refine ⟨0, ?_, ?_⟩
        · intro l hl
          exact False.elim (hL ⟨l, hl⟩)
        · intro u hu
          exact False.elim (hU ⟨u, hu⟩)

lemma rel_upper {s : Bool} {a b r z : K} (ha : 0 < a) :
    Rel s (r + a*z) b ↔ Rel s z ((b-r)/a) := by
  cases s <;> simp only [Rel, Bool.false_eq_true, if_false, if_true]
  · rw [le_div_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  · rw [lt_div_iff₀ ha]
    constructor <;> intro h <;> nlinarith

lemma rel_lower {s : Bool} {a b r z : K} (ha : a < 0) :
    Rel s (r + a*z) b ↔ Rel s ((b-r)/a) z := by
  cases s <;> simp only [Rel, Bool.false_eq_true, if_false, if_true]
  · rw [div_le_iff_of_neg ha]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_iff_of_neg ha]
    constructor <;> intro h <;> nlinarith

lemma rel_pair {s : Bool} {ap am bp bm rp rm : K}
    (hp : 0 < ap) (hm : am < 0) :
    Rel s ((bm-rm)/am) ((bp-rp)/ap) ↔
      Rel s ((-am)*rp + ap*rm) ((-am)*bp + ap*bm) := by
  have hm' : 0 < -am := neg_pos.mpr hm
  have he : (bm-rm)/am = (rm-bm)/(-am) := by field_simp; ring
  rw [he]
  cases s <;> simp only [Rel, Bool.false_eq_true, if_false, if_true]
  · rw [div_le_div_iff₀ hm' hp]
    constructor <;> intro h <;> nlinarith
  · rw [div_lt_div_iff₀ hm' hp]
    constructor <;> intro h <;> nlinarith

structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  bound : ℚ
  strict : Bool
  deriving DecidableEq

open scoped BigOperators

def Row.eval {n : ℕ} (r : Row n) (x : Fin n → K) : K :=
  ∑ i, (r.coeff i : K) * x i

def Row.Holds {n : ℕ} (r : Row n) (x : Fin n → K) : Prop :=
  Rel r.strict (r.eval x) (r.bound : K)

def Row.last {n : ℕ} (r : Row (n+1)) : ℚ := r.coeff (Fin.last n)

def Row.drop {n : ℕ} (r : Row (n+1)) : Row n :=
  ⟨fun i => r.coeff i.castSucc, r.bound, r.strict⟩

lemma Row.eval_snoc {n : ℕ} (r : Row (n+1)) (x : Fin n → K) (z : K) :
    r.eval (Fin.snoc x z) = r.drop.eval x + (r.last : K)*z := by
  simp [Row.eval, Fin.sum_univ_castSucc, Row.drop, Row.last]

def Row.endpoint {n : ℕ} (r : Row (n+1)) (x : Fin n → K) : K :=
  ((r.bound : K) - r.drop.eval x)/(r.last : K)

lemma Row.holds_pos {n : ℕ} (r : Row (n+1)) (x : Fin n → K) (z : K)
    (hr : 0 < r.last) : r.Holds (Fin.snoc x z) ↔ Rel r.strict z (r.endpoint x) := by
  unfold Row.Holds Row.endpoint
  rw [Row.eval_snoc]
  exact rel_upper (by exact_mod_cast hr)

lemma Row.holds_neg {n : ℕ} (r : Row (n+1)) (x : Fin n → K) (z : K)
    (hr : r.last < 0) : r.Holds (Fin.snoc x z) ↔ Rel r.strict (r.endpoint x) z := by
  unfold Row.Holds Row.endpoint
  rw [Row.eval_snoc]
  exact rel_lower (by exact_mod_cast hr)

lemma Row.holds_zero {n : ℕ} (r : Row (n+1)) (x : Fin n → K) (z : K)
    (hr : r.last = 0) : r.Holds (Fin.snoc x z) ↔ r.drop.Holds x := by
  unfold Row.Holds
  rw [Row.eval_snoc, hr]
  simp only [Rat.cast_zero, zero_mul, add_zero, Row.drop]

def Row.combine {n : ℕ} (p m : Row (n+1)) : Row n where
  coeff i := (-m.last)*p.coeff i.castSucc + p.last*m.coeff i.castSucc
  bound := (-m.last)*p.bound + p.last*m.bound
  strict := m.strict || p.strict

lemma Row.eval_combine {n : ℕ} (p m : Row (n+1)) (x : Fin n → K) :
    (p.combine m).eval x = (-(m.last : K))*p.drop.eval x + (p.last : K)*m.drop.eval x := by
  simp only [Row.eval, Row.combine, Row.drop, Rat.cast_add, Rat.cast_mul, Rat.cast_neg,
    add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

lemma Row.holds_combine {n : ℕ} (p m : Row (n+1)) (x : Fin n → K)
    (hp : 0 < p.last) (hm : m.last < 0) :
    (p.combine m).Holds x ↔ Rel (m.strict || p.strict) (m.endpoint x) (p.endpoint x) := by
  rw [Row.Holds, Row.eval_combine]
  simp only [Row.combine, Rat.cast_add, Rat.cast_mul, Rat.cast_neg]
  exact (rel_pair (by exact_mod_cast hp) (by exact_mod_cast hm)).symm

/-- A finite computable rational projection: retain zero-leading rows and
combine every positive-leading row with every negative-leading row. -/
def project {n : ℕ} (R : Finset (Row (n+1))) : Finset (Row n) :=
  ((R.filter fun r => r.last = 0).image Row.drop) ∪
  (((R.filter fun r => 0 < r.last).product (R.filter fun r => r.last < 0)).image
    fun pm => pm.1.combine pm.2)

theorem project_iff {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → K) :
    (∃ z : K, ∀ r ∈ R, r.Holds (Fin.snoc x z)) ↔
      (∀ q ∈ project R, q.Holds x) := by
  classical
  constructor
  · rintro ⟨z, h⟩ q hq
    rcases Finset.mem_union.mp hq with hz | hp
    · rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
      rcases Finset.mem_filter.mp hr with ⟨hr, hzero⟩
      exact (r.holds_zero x z hzero).mp (h r hr)
    · rcases Finset.mem_image.mp hp with ⟨⟨p,m⟩, hpm, rfl⟩
      rcases Finset.mem_product.mp hpm with ⟨hp,hm⟩
      rcases Finset.mem_filter.mp hp with ⟨hp,hpos⟩
      rcases Finset.mem_filter.mp hm with ⟨hm,hneg⟩
      apply (p.holds_combine m x hpos hneg).mpr
      exact rel_trans ((m.holds_neg x z hneg).mp (h m hm))
        ((p.holds_pos x z hpos).mp (h p hp))
  · intro h
    let L : Finset (K × Bool) := (R.filter fun r => r.last < 0).image
      (fun r => (r.endpoint x, r.strict))
    let U : Finset (K × Bool) := (R.filter fun r => 0 < r.last).image
      (fun r => (r.endpoint x, r.strict))
    have hcomp : ∀ l ∈ L, ∀ u ∈ U, Rel (l.2 || u.2) l.1 u.1 := by
      intro l hl u hu
      rcases Finset.mem_image.mp hl with ⟨m, hm, rfl⟩
      rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
      rcases Finset.mem_filter.mp hm with ⟨hm,hneg⟩
      rcases Finset.mem_filter.mp hp with ⟨hp,hpos⟩
      apply (p.holds_combine m x hpos hneg).mp
      apply h
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(p,m), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp,hpos⟩,
        Finset.mem_filter.mpr ⟨hm,hneg⟩⟩
    obtain ⟨z, hL, hU⟩ := (finite_bounds_iff L U).mpr hcomp
    refine ⟨z, ?_⟩
    intro r hr
    rcases lt_trichotomy r.last 0 with hneg | hzero | hpos
    · apply (r.holds_neg x z hneg).mpr
      exact hL (r.endpoint x,r.strict)
        (Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,hneg⟩,rfl⟩)
    · apply (r.holds_zero x z hzero).mpr
      apply h
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,hzero⟩,rfl⟩
    · apply (r.holds_pos x z hpos).mpr
      exact hU (r.endpoint x,r.strict)
        (Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,hpos⟩,rfl⟩)

def Feasible (K : Type*) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (R : Finset (Row n)) : Prop := ∃ x : Fin n → K, ∀ r ∈ R, r.Holds x

theorem feasible_project_iff {n : ℕ} (R : Finset (Row (n+1))) :
    Feasible K R ↔ Feasible K (project R) := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨Fin.init x, (project_iff R (Fin.init x)).mp ?_⟩
    refine ⟨x (Fin.last n), ?_⟩
    simpa only [Fin.snoc_init_self] using hx
  · rintro ⟨x,hx⟩
    obtain ⟨z,hz⟩ := (project_iff R x).mpr hx
    exact ⟨Fin.snoc x z,hz⟩

instance relDecidable (s : Bool) (x y : K) : Decidable (Rel s x y) := by
  unfold Rel
  infer_instance

lemma rat_rel_cast (s : Bool) (a b : ℚ) :
    Rel s (a : K) (b : K) ↔ Rel s a b := by
  cases s <;> simp [Rel]

theorem feasible_zero_iff (R : Finset (Row 0)) :
    Feasible K R ↔ ∀ r ∈ R, Rel r.strict (0 : ℚ) r.bound := by
  constructor
  · rintro ⟨x,hx⟩ r hr
    have h := hx r hr
    have hz : Rel r.strict (0 : K) (r.bound : K) := by
      simpa only [Row.Holds, Row.eval, Finset.univ_eq_empty, Finset.sum_empty] using h
    exact (rat_rel_cast r.strict 0 r.bound).mp (by simpa only [Rat.cast_zero] using hz)
  · intro h
    refine ⟨Fin.elim0, ?_⟩
    intro r hr
    have hz := (rat_rel_cast (K := K) r.strict 0 r.bound).mpr (h r hr)
    simpa only [Row.Holds, Row.eval, Finset.univ_eq_empty, Finset.sum_empty,
      Rat.cast_zero] using hz

/-- A total executable decision procedure. It recursively removes exactly one
coordinate and uses only finite rational arithmetic and decidable comparisons.
No real feasibility, QE, attainment or termination provider is supplied. -/
def decideFeasible : (n : ℕ) → Finset (Row n) → Bool
  | 0, R => decide (∀ r ∈ R, Rel r.strict (0 : ℚ) r.bound)
  | n+1, R => decideFeasible n (project R)

theorem decideFeasible_correct (n : ℕ) (R : Finset (Row n)) :
    decideFeasible n R = true ↔ Feasible K R := by
  induction n with
  | zero =>
      rw [feasible_zero_iff]
      simp only [decideFeasible, decide_eq_true_eq]
  | succ n ih =>
      rw [decideFeasible, feasible_project_iff]
      exact ih (project R)

/-- Rational witness existence is derived, not assumed: the same finite
rational decision computation is complete in both ℚ and ℝ. -/
theorem real_feasible_iff_rational {n : ℕ} (R : Finset (Row n)) :
    Feasible ℝ R ↔ Feasible ℚ R :=
  (decideFeasible_correct (K := ℝ) n R).symm.trans
    (decideFeasible_correct (K := ℚ) n R)

theorem rational_witness_of_real {n : ℕ} (R : Finset (Row n))
    (h : Feasible ℝ R) : ∃ q : Fin n → ℚ, ∀ r ∈ R, r.Holds q :=
  real_feasible_iff_rational R |>.mp h

#print axioms decideFeasible_correct
#print axioms real_feasible_iff_rational
#print axioms rational_witness_of_real
#print axioms project_iff
#print axioms feasible_project_iff
#print axioms finite_bounds_iff
end UnifiedLean.G6.StrictAffineElimination
