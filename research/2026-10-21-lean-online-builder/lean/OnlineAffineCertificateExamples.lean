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

/-!
# Executable rational witnesses for strict affine source cells

Contributor: Codex / lean_reuse, 10 October 2026.
This fills the witness-returning gap of the existing Boolean Fourier--Motzkin
decider. It reuses the exact emitted rational rows and elimination criterion.
It does not supply an original graph, a source chart, nonlinear law constraints,
an unknown-size source census, or general G3 exact recognition.

The chosen coordinate is the midpoint of distinct finite extremal bounds,
their shared endpoint when equal, one unit beyond a lone finite bound, or zero.
All executable definitions use rational arithmetic and decidable finite data.
-/
namespace UnifiedLean.G6.RationalAffineWitness

open UnifiedLean.G6.StrictAffineElimination

instance rationalRowHoldsDecidable {n : ℕ} (r : Row n) (q : Fin n → ℚ) :
    Decidable (r.Holds q) := by
  unfold Row.Holds
  infer_instance

theorem rat_cast_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    (↑(∑ i ∈ s, f i) : ℝ) = ∑ i ∈ s, (f i : ℝ) :=
  map_sum (Rat.castHom ℝ) f s

/-- A deterministic rational coordinate for a compatible finite interval. -/
def boundsWitness (L U : Finset (ℚ × Bool)) : ℚ :=
  if hL : L.Nonempty then
    let a := (L.image Prod.fst).max' (hL.image _)
    if hU : U.Nonempty then
      let b := (U.image Prod.fst).min' (hU.image _)
      if a < b then (a + b) / 2 else a
    else a + 1
  else if hU : U.Nonempty then
    (U.image Prod.fst).min' (hU.image _) - 1
  else 0

/-- Strict and weak bounds, empty sides, and feasible singleton intervals
are handled by the same executable coordinate selection. -/
theorem boundsWitness_spec (L U : Finset (ℚ × Bool))
    (h : ∀ l ∈ L, ∀ u ∈ U, Rel (l.2 || u.2) l.1 u.1) :
    (∀ l ∈ L, Rel l.2 l.1 (boundsWitness L U)) ∧
    (∀ u ∈ U, Rel u.2 (boundsWitness L U) u.1) := by
  by_cases hL : L.Nonempty
  · let A := L.image Prod.fst
    have hA : A.Nonempty := hL.image _
    let a := A.max' hA
    obtain ⟨l₀, hl₀, hlval⟩ := Finset.mem_image.mp (A.max'_mem hA)
    have lower_le : ∀ l ∈ L, l.1 ≤ a := by
      intro l hl
      exact A.le_max' _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    by_cases hU : U.Nonempty
    · let B := U.image Prod.fst
      have hB : B.Nonempty := hU.image _
      let b := B.min' hB
      obtain ⟨u₀, hu₀, huval⟩ := Finset.mem_image.mp (B.min'_mem hB)
      have upper_le : ∀ u ∈ U, b ≤ u.1 := by
        intro u hu
        exact B.min'_le _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      have hab : a ≤ b := by
        have hz := rel_le (h l₀ hl₀ u₀ hu₀)
        simpa only [hlval, huval] using hz
      by_cases hlt : a < b
      · have hw : boundsWitness L U = (a + b) / 2 := by
          simp only [boundsWitness, dif_pos hL, dif_pos hU]
          change (if a < b then (a + b) / 2 else a) = (a + b) / 2
          exact if_pos hlt
        rw [hw]
        constructor
        · intro l hl
          apply rel_of_lt
          have := lower_le l hl
          linarith
        · intro u hu
          apply rel_of_lt
          have := upper_le u hu
          linarith
      · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
        have hw : boundsWitness L U = a := by
          simp only [boundsWitness, dif_pos hL, dif_pos hU]
          change (if a < b then (a + b) / 2 else a) = a
          exact if_neg hlt
        rw [hw]
        constructor
        · intro l hl
          have hz := rel_or_left (h l hl u₀ hu₀)
          have hbu : u₀.1 = b := huval
          rw [hbu, ← heq] at hz
          exact hz
        · intro u hu
          have hz := rel_or_right (h l₀ hl₀ u hu)
          simpa only [hlval] using hz
    · have hw : boundsWitness L U = a + 1 := by
        simp only [boundsWitness, dif_pos hL, dif_neg hU]
        rfl
      rw [hw]
      constructor
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
      have hw : boundsWitness L U = b - 1 := by
        simp only [boundsWitness, dif_neg hL, dif_pos hU]
        rfl
      rw [hw]
      constructor
      · intro l hl
        exact False.elim (hL ⟨l, hl⟩)
      · intro u hu
        apply rel_of_lt
        have := upper_le u hu
        linarith
    · have hw : boundsWitness L U = 0 := by
        simp only [boundsWitness, dif_neg hL, dif_neg hU]
      rw [hw]
      exact ⟨fun l hl => False.elim (hL ⟨l, hl⟩),
        fun u hu => False.elim (hU ⟨u, hu⟩)⟩

def lowerBounds {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ) :
    Finset (ℚ × Bool) :=
  (R.filter fun r => r.last < 0).image (fun r => (r.endpoint x, r.strict))

def upperBounds {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ) :
    Finset (ℚ × Bool) :=
  (R.filter fun r => 0 < r.last).image (fun r => (r.endpoint x, r.strict))

/-- Back-substitute one coordinate, without an existence oracle. -/
def liftWitness {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ) : ℚ :=
  boundsWitness (lowerBounds R x) (upperBounds R x)

theorem liftWitness_correct {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ)
    (hx : ∀ q ∈ project R, q.Holds x) :
    ∀ r ∈ R, r.Holds (Fin.snoc x (liftWitness R x)) := by
  obtain ⟨z, hz⟩ := (project_iff R x).mpr hx
  have hL : ∀ l ∈ lowerBounds R x, Rel l.2 l.1 z := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hr, hneg⟩ := Finset.mem_filter.mp hr
    exact (r.holds_neg x z hneg).mp (hz r hr)
  have hU : ∀ u ∈ upperBounds R x, Rel u.2 z u.1 := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hr, hpos⟩ := Finset.mem_filter.mp hr
    exact (r.holds_pos x z hpos).mp (hz r hr)
  have hb := boundsWitness_spec (lowerBounds R x) (upperBounds R x)
    ((finite_bounds_iff _ _).mp ⟨z, hL, hU⟩)
  intro r hr
  rcases lt_trichotomy r.last 0 with hneg | hzero | hpos
  · apply (r.holds_neg x (liftWitness R x) hneg).mpr
    exact hb.1 (r.endpoint x, r.strict)
      (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hneg⟩, rfl⟩)
  · apply (r.holds_zero x (liftWitness R x) hzero).mpr
    exact (r.holds_zero x z hzero).mp (hz r hr)
  · apply (r.holds_pos x (liftWitness R x) hpos).mpr
    exact hb.2 (r.endpoint x, r.strict)
      (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hpos⟩, rfl⟩)

/-- A total rational witness-returning solver. `none` means infeasible;
`some q` returns a vector on the original, jointly compiled variables. -/
def solveRational : (n : ℕ) → Finset (Row n) → Option (Fin n → ℚ)
  | 0, R =>
    if ∀ r ∈ R, Rel r.strict (0 : ℚ) r.bound then some Fin.elim0 else none
  | n+1, R =>
    (solveRational n (project R)).map (fun x => Fin.snoc x (liftWitness R x))

/-- An independently executable positive-output certificate checker. -/
def checkRationalWitness {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ) : Bool :=
  decide (∀ r ∈ R, r.Holds q)

theorem checkRationalWitness_correct {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ) :
    checkRationalWitness R q = true ↔ ∀ r ∈ R, r.Holds q := by
  simp only [checkRationalWitness, decide_eq_true_eq]

theorem solveRational_isSome (n : ℕ) (R : Finset (Row n)) :
    (solveRational n R).isSome = decideFeasible n R := by
  induction n with
  | zero =>
    simp only [solveRational, decideFeasible]
    split <;> simp_all
  | succ n ih =>
    simp only [solveRational, Option.isSome_map, decideFeasible, ih]

theorem solveRational_sound {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ)
    (h : solveRational n R = some q) : ∀ r ∈ R, r.Holds q := by
  induction n with
  | zero =>
    simp only [solveRational] at h
    split at h
    · rename_i hx
      have hq : Fin.elim0 = q := Option.some.inj h
      intro r hr
      rw [← hq]
      simpa only [Row.Holds, Row.eval, Finset.univ_eq_empty, Finset.sum_empty,
        Rat.cast_id] using hx r hr
    · contradiction
  | succ n ih =>
    simp only [solveRational] at h
    cases hx : solveRational n (project R) with
    | none => simp only [hx, Option.map_none] at h; contradiction
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact liftWitness_correct R x (ih (project R) x hx)

/-- Row evaluation commutes with the canonical rational-to-real embedding. -/
theorem rationalWitness_real {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ)
    (hq : ∀ r ∈ R, r.Holds q) :
    ∀ r ∈ R, r.Holds (fun i => (q i : ℝ)) := by
  intro r hr
  have he : r.eval (fun i => (q i : ℝ)) = ((r.eval (K := ℚ) q : ℚ) : ℝ) := by
    simp only [Row.eval, rat_cast_sum, Rat.cast_mul, Rat.cast_id]
  rw [Row.Holds, he]
  exact (rat_rel_cast r.strict (r.eval (K := ℚ) q) r.bound).mpr (hq r hr)

/-- Full soundness and completeness over the original real affine contract. -/
theorem solveRational_complete (n : ℕ) (R : Finset (Row n)) :
    (∃ q, solveRational n R = some q) ↔ Feasible ℝ R := by
  rw [← decideFeasible_correct (K := ℝ), ← solveRational_isSome]
  cases h : solveRational n R <;> simp

theorem solveRational_none_iff (n : ℕ) (R : Finset (Row n)) :
    solveRational n R = none ↔ ¬ Feasible ℝ R := by
  rw [← solveRational_complete]
  cases h : solveRational n R <;> simp

theorem solveRational_checked {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ)
    (h : solveRational n R = some q) : checkRationalWitness R q = true :=
  (checkRationalWitness_correct R q).mpr (solveRational_sound R q h)

/-- The ordered wire implementation retains duplicates: zero rows first,
then the Cartesian product with positive rows outermost and negative rows
innermost. This is extensionally the existing finite-set projection. -/
def projectList {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => r.last = 0).map Row.drop ++
  (R.filter fun r => 0 < r.last).flatMap (fun p =>
    (R.filter fun r => r.last < 0).map (fun m => p.combine m))

theorem projectList_toFinset {n : ℕ} (R : List (Row (n+1))) :
    (projectList R).toFinset = project R.toFinset := by
  ext q
  simp only [projectList, project, List.mem_toFinset, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_filter, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
    Prod.exists]
  aesop

def solveList : (n : ℕ) → List (Row n) → Option (Fin n → ℚ)
  | 0, R =>
    if ∀ r ∈ R, Rel r.strict (0 : ℚ) r.bound then some Fin.elim0 else none
  | n+1, R =>
    (solveList n (projectList R)).map (fun x => Fin.snoc x (liftWitness R.toFinset x))

/-- Exact refinement of ordered/duplicate wire rows to the proved solver;
the selected vector is equal, rather than merely another feasible vector. -/
theorem solveList_eq_solveRational (n : ℕ) (R : List (Row n)) :
    solveList n R = solveRational n R.toFinset := by
  induction n with
  | zero => simp only [solveList, solveRational, List.mem_toFinset]
  | succ n ih =>
    simp only [solveList, solveRational, ih, projectList_toFinset]

theorem solveList_sound {n : ℕ} (R : List (Row n)) (q : Fin n → ℚ)
    (h : solveList n R = some q) : ∀ r ∈ R, r.Holds q := by
  rw [solveList_eq_solveRational] at h
  simpa only [List.mem_toFinset] using solveRational_sound R.toFinset q h

theorem solveList_complete (n : ℕ) (R : List (Row n)) :
    (∃ q, solveList n R = some q) ↔ Feasible ℝ R.toFinset := by
  rw [solveList_eq_solveRational, solveRational_complete]

theorem solveList_none_iff (n : ℕ) (R : List (Row n)) :
    solveList n R = none ↔ ¬ Feasible ℝ R.toFinset := by
  rw [solveList_eq_solveRational, solveRational_none_iff]

#print axioms boundsWitness_spec
#print axioms liftWitness_correct
#print axioms checkRationalWitness_correct
#print axioms solveRational_isSome
#print axioms solveRational_sound
#print axioms rationalWitness_real
#print axioms solveRational_complete
#print axioms solveRational_none_iff
#print axioms solveRational_checked
#print axioms projectList_toFinset
#print axioms solveList_eq_solveRational
#print axioms solveList_sound
#print axioms solveList_complete
#print axioms solveList_none_iff

end UnifiedLean.G6.RationalAffineWitness

/-! Source candidate for the existing native AFFINE certificates.
Reuses the original Row and rational-witness theorem; no solver is implemented.
The finite rational matrix is supplied. Native parsing, source-chart admission
and all-size source exclusion are separate obligations. Not checked yet. -/

namespace Astra.NativeAffineCertificates

open scoped BigOperators
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness

variable {n m : ℕ}

/-- Ordered original rows may repeat; witness checking uses the same finite set. -/
def rowsSet (R : Fin m → Row n) : Finset (Row n) :=
  Finset.univ.image R

/-- Reuse the existing positive checker and rational-to-real theorem. -/
theorem checked_witness_real (R : Fin m → Row n) (q : Fin n → ℚ)
    (h : checkRationalWitness (rowsSet R) q = true) :
    ∀ a, (R a).Holds (fun j => (q j : ℝ)) := by
  have hr := rationalWitness_real (rowsSet R) q
    ((checkRationalWitness_correct (rowsSet R) q).mp h)
  intro a
  exact hr (R a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

/-- Exact finite predicate used by the existing Rust check_exclusion:
a zero multiplier on a strict row cannot supply a strict contradiction. -/
def checkFarkas (R : Fin m → Row n) (w : Fin m → ℚ) : Bool :=
  decide ((∀ a, 0 ≤ w a) ∧
    (∀ j, (∑ a, w a * (R a).coeff j) = 0) ∧
    ((∑ a, w a * (R a).bound) < 0 ∨
      ((∑ a, w a * (R a).bound) = 0 ∧
        ∃ a, 0 < w a ∧ (R a).strict = true)))

theorem weighted_eval_zero (R : Fin m → Row n) (w : Fin m → ℚ)
    (hc : ∀ j, (∑ a, w a * (R a).coeff j) = 0)
    (x : Fin n → ℝ) :
    (∑ a, (w a : ℝ) * (R a).eval x) = 0 := by
  have hcR (j : Fin n) :
      (∑ a, (w a : ℝ) * ((R a).coeff j : ℝ)) = 0 := by
    exact_mod_cast hc j
  calc
    (∑ a, (w a : ℝ) * (R a).eval x) =
        ∑ a, ∑ j, ((w a : ℝ) * ((R a).coeff j : ℝ)) * x j := by
      simp only [Row.eval, Finset.mul_sum, mul_assoc]
    _ = ∑ j, ∑ a, ((w a : ℝ) * ((R a).coeff j : ℝ)) * x j := Finset.sum_comm
    _ = ∑ j, (∑ a, (w a : ℝ) * ((R a).coeff j : ℝ)) * x j := by
      simp only [Finset.sum_mul]
    _ = 0 := by simp only [hcR, zero_mul, Finset.sum_const_zero]

/-- Soundness concerns this exact finite matrix over the reals. It needs no
claim about the native elimination trajectory or the origin of the rows. -/
theorem farkas_infeasible (R : Fin m → Row n) (w : Fin m → ℚ)
    (hw : ∀ a, 0 ≤ w a)
    (hc : ∀ j, (∑ a, w a * (R a).coeff j) = 0)
    (hb : (∑ a, w a * (R a).bound) < 0 ∨
      ((∑ a, w a * (R a).bound) = 0 ∧
        ∃ a, 0 < w a ∧ (R a).strict = true)) :
    ¬ ∃ x : Fin n → ℝ, ∀ a, (R a).Holds x := by
  rintro ⟨x, hx⟩
  have hwR (a : Fin m) : 0 ≤ (w a : ℝ) := by exact_mod_cast hw a
  have hle (a : Fin m) :
      (w a : ℝ) * (R a).eval x ≤ (w a : ℝ) * ((R a).bound : ℝ) :=
    mul_le_mul_of_nonneg_left (rel_le (hx a)) (hwR a)
  have hz := weighted_eval_zero R w hc x
  rcases hb with hneg | ⟨heq, a, hwa, hsa⟩
  · have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin m))) => hle a)
    have hbR : (∑ a, (w a : ℝ) * ((R a).bound : ℝ)) < 0 := by
      exact_mod_cast hneg
    linarith
  · have ha : (R a).eval x < ((R a).bound : ℝ) := by
      simpa [Row.Holds, UnifiedLean.G6.StrictAffineElimination.Rel, hsa] using hx a
    have hwaR : 0 < (w a : ℝ) := by exact_mod_cast hwa
    have hlt := mul_lt_mul_of_pos_left ha hwaR
    have hsum : (∑ a, (w a : ℝ) * (R a).eval x) <
        ∑ a, (w a : ℝ) * ((R a).bound : ℝ) :=
      Finset.sum_lt_sum (fun a _ => hle a) ⟨a, Finset.mem_univ a, hlt⟩
    have hbR : (∑ a, (w a : ℝ) * ((R a).bound : ℝ)) = 0 := by
      exact_mod_cast heq
    linarith

theorem checked_farkas_infeasible (R : Fin m → Row n) (w : Fin m → ℚ)
    (h : checkFarkas R w = true) :
    ¬ ∃ x : Fin n → ℝ, ∀ a, (R a).Holds x := by
  simp only [checkFarkas, decide_eq_true_eq] at h
  exact farkas_infeasible R w h.1 h.2.1 h.2.2

end Astra.NativeAffineCertificates

/-! Authored literal controls, not an actual native execution record. -/
namespace Astra.NativeAffineCertificates.Examples

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness

def intervalRows (a : Fin 2) : Row 1 where
  coeff _ := if a.val = 0 then -1 else 1
  bound := if a.val = 0 then 0 else 1
  strict := true

def intervalPoint : Fin 1 → ℚ := fun _ => 1/2

theorem interval_checked :
    checkRationalWitness (rowsSet intervalRows) intervalPoint = true := by
  apply (checkRationalWitness_correct _ _).mpr
  intro row hrow
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hrow
  fin_cases a <;> norm_num [intervalRows, intervalPoint, Row.Holds, Row.eval,
    UnifiedLean.G6.StrictAffineElimination.Rel, Fin.sum_univ_succ]

theorem interval_real :
    ∀ a, (intervalRows a).Holds (fun j => (intervalPoint j : ℝ)) :=
  checked_witness_real intervalRows intervalPoint interval_checked

/-- x>0 and x<=0 on the SAME original coordinate. -/
def contradictoryRows (a : Fin 2) : Row 1 where
  coeff _ := if a.val = 0 then -1 else 1
  bound := 0
  strict := decide (a.val = 0)

def unitWeights : Fin 2 → ℚ := fun _ => 1

theorem contradiction_checked : checkFarkas contradictoryRows unitWeights = true := by
  norm_num [checkFarkas, unitWeights, contradictoryRows, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem contradiction_real :
    ¬ ∃ x : Fin 1 → ℝ, ∀ a, (contradictoryRows a).Holds x :=
  checked_farkas_infeasible contradictoryRows unitWeights contradiction_checked

/-- The only strict original row is 0<1 and receives multiplier ZERO.
The weak pair permits x=0; this must not be certified as an exclusion. -/
def zeroStrictRows (a : Fin 3) : Row 1 where
  coeff _ := if a.val = 0 then 0 else if a.val = 1 then -1 else 1
  bound := if a.val = 0 then 1 else 0
  strict := decide (a.val = 0)

def zeroStrictWeights (a : Fin 3) : ℚ := if a.val = 0 then 0 else 1

theorem zero_strict_not_exclusion : checkFarkas zeroStrictRows zeroStrictWeights = false := by
  norm_num [checkFarkas, zeroStrictRows, zeroStrictWeights, Fin.sum_univ_succ,
    Fin.forall_fin_succ, Fin.exists_fin_succ]

theorem zero_strict_witness :
    checkRationalWitness (rowsSet zeroStrictRows) (fun _ => 0) = true := by
  apply (checkRationalWitness_correct _ _).mpr
  intro row hrow
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hrow
  fin_cases a <;> norm_num [zeroStrictRows, Row.Holds, Row.eval,
    UnifiedLean.G6.StrictAffineElimination.Rel, Fin.sum_univ_succ]

end Astra.NativeAffineCertificates.Examples
