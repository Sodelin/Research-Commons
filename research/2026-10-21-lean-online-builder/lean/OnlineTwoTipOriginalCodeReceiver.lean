import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Inv
import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
import Init.Data.Rat
import Std


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


/-! Exact arithmetic and canonical wire parsing. Rational operations are the
standard Lean `Rat` implementation, whose denominator is positive and whose
numerator and denominator are coprime. Input integers are bounded at 256 bits;
derived arithmetic is unrestricted exact arithmetic. -/
namespace GParity.Rational

def wire (q : Rat) : String := s!"{q.num}/{q.den}"

def parseNat (s : String) : Option Nat := do
  let n ← s.toNat?
  if toString n == s then some n else none

def parseInt (s : String) : Option Int := do
  let n ← s.toInt?
  if toString n == s then some n else none

def parse (s : String) : Option Rat := do
  match s.splitOn "/" with
  | [a, b] =>
      let num ← parseInt a
      let den ← parseNat b
      if den == 0 || num.natAbs ≥ 2^256 || den ≥ 2^256 then none
      else
        let q := mkRat num den
        if wire q == s then some q else none
  | _ => none

def dot (a x : List Rat) : Rat :=
  (a.zipWith (· * ·) x).foldl (· + ·) 0

def line (label : String) (xs : List Rat) : String :=
  label ++ toString xs.length ++
    (if xs.isEmpty then "" else " " ++ String.intercalate " " (xs.map wire)) ++ "\n"

end GParity.Rational


/-! Deterministic exact strict Fourier--Motzkin execution. Projection preserves
zero rows in input order, then combines positive outer/negative inner rows. No
row rescaling or deduplication occurs. Original-row multipliers follow every
projection step. The formal source-typed arithmetic theorem is supplied by
`StrictAffineElimination`; refinement of this wire representation is a separate
checked module, rather than an assumption of this executable. -/
namespace GParity.Affine
open GParity.Rational

structure Row where
  coeff : List Rat
  bound : Rat
  strict : Bool
  weights : List Rat
  deriving Repr, BEq

def Row.eval (r : Row) (x : List Rat) : Rat := dot r.coeff x

def Row.holds (r : Row) (x : List Rat) : Bool :=
  if r.strict then decide (r.eval x < r.bound) else decide (r.eval x ≤ r.bound)

def Row.last (r : Row) : Rat := r.coeff.getLast?.getD 0

def Row.drop (n : Nat) (r : Row) : Row := { r with coeff := r.coeff.take n }

def Row.combine (n : Nat) (p m : Row) : Row :=
  let cp := -m.last
  let cm := p.last
  { coeff := (p.coeff.take n).zipWith (fun a b => cp*a + cm*b) (m.coeff.take n)
    bound := cp*p.bound + cm*m.bound
    strict := m.strict || p.strict
    weights := p.weights.zipWith (fun a b => cp*a + cm*b) m.weights }

def zeros (rows : List Row) : List Row := rows.filter (fun r => r.last == 0)
def positives (rows : List Row) : List Row := rows.filter (fun r => decide (0 < r.last))
def negatives (rows : List Row) : List Row := rows.filter (fun r => decide (r.last < 0))

def projectedSize (rows : List Row) : Nat :=
  (zeros rows).length + (positives rows).length * (negatives rows).length

def projectList (n : Nat) (rows : List Row) : List Row :=
  (zeros rows).map (Row.drop n) ++
  (positives rows).flatMap (fun p => (negatives rows).map (Row.combine n p))

structure Endpoint where
  value : Rat
  strict : Bool
  deriving Repr

def endpoint (n : Nat) (r : Row) (x : List Rat) : Endpoint :=
  ⟨(r.bound - dot (r.coeff.take n) x) / r.last, r.strict⟩

def lowerExtremum (xs : List Endpoint) : Option Endpoint := xs.foldl
  (fun acc x => match acc with
    | none => some x
    | some y =>
        if y.value < x.value then some x
        else if x.value == y.value then some ⟨y.value, y.strict || x.strict⟩
        else some y) none

def upperExtremum (xs : List Endpoint) : Option Endpoint := xs.foldl
  (fun acc x => match acc with
    | none => some x
    | some y =>
        if x.value < y.value then some x
        else if x.value == y.value then some ⟨y.value, y.strict || x.strict⟩
        else some y) none

def chooseLast (n : Nat) (rows : List Row) (x : List Rat) : Rat :=
  let lower := lowerExtremum ((negatives rows).map (fun r => endpoint n r x))
  let upper := upperExtremum ((positives rows).map (fun r => endpoint n r x))
  match lower, upper with
  | none, none => 0
  | some a, none => a.value + 1
  | none, some b => b.value - 1
  | some a, some b => if a.value < b.value then (a.value + b.value) / 2 else a.value

inductive Outcome where
  | sat : List Rat → Outcome
  | unsat : Row → Outcome
  | unknown : Nat → Nat → Nat → Outcome
  deriving Repr

def solve : Nat → List Row → Nat → Outcome
  | 0, rows, _ =>
      match rows.find? (fun r => !(r.holds [])) with
      | some r => .unsat r
      | none => .sat []
  | n+1, rows, cap =>
      let required := projectedSize rows
      if cap < required then .unknown (n+1) required cap
      else
        match solve n (projectList n rows) cap with
        | .sat x => .sat (x ++ [chooseLast n rows x])
        | .unsat r => .unsat r
        | .unknown n required cap => .unknown n required cap

def checkWitness (n : Nat) (rows : List Row) (x : List Rat) : Bool :=
  x.length == n && rows.all (fun r => r.coeff.length == n) && rows.all (fun r => r.holds x)

/-- Independent arithmetic checking of the emitted contradiction against the
original rows; no projection trace is required by the consumer. -/
def checkContradiction (n : Nat) (rows : List Row) (weights : List Rat) : Bool :=
  let weighted := rows.zip weights
  let bounds : Rat := weighted.foldl (fun a rw => a + rw.2 * rw.1.bound) 0
  weights.length == rows.length && rows.all (fun r => r.coeff.length == n) &&
    weights.all (fun w => decide (0 ≤ w)) &&
    (List.range n).all (fun j =>
      weighted.foldl (fun a rw => a + rw.2 * (rw.1.coeff[j]?.getD 0)) 0 == 0) &&
    (decide (bounds < 0) ||
      (bounds == 0 && weighted.any (fun rw => rw.1.strict && decide (0 < rw.2))))

end GParity.Affine


/-! Literal original-ID natural cells, compiled to one joint rational bank.
The finite graph predicate follows `RootedBinary`; its typed-source refinement
and the intended active-exposure interpretation remain explicit obligations.
The ordered row convention preserves duplicates and maps to the inherited
finite-set compiler by semantic equality, not by a finset iteration order. -/
namespace GParity.Chart
open GParity.Rational GParity.Affine

structure Edge where
  source : Nat
  target : Nat
  deriving Repr
structure Hybrid where
  vertex : Nat
  incoming0 : Nat
  incoming1 : Nat
  deriving Repr
structure Source where
  vertices : Nat
  root : Nat
  edges : List Edge
  leaves : List Nat
  hybrids : List Hybrid
  deriving Repr
inductive AgeAtom where
  | node : Nat → AgeAtom
  | fixed : Rat → AgeAtom
  deriving Repr
inductive Comparison where
  | strict | weak | equal
  deriving Repr, BEq
structure AgeConstraint where
  kind : Comparison
  left : AgeAtom
  right : AgeAtom
  deriving Repr
structure Bound where
  value : Rat
  strict : Bool
  deriving Repr
structure Interval where
  lower : Option Bound
  upper : Option Bound
  deriving Repr
structure Exposure where
  population : Option Nat
  younger : AgeAtom
  older : AgeAtom
  interval : Interval
  deriving Repr
structure Input where
  source : Source
  chronology : List AgeConstraint
  exposures : List Exposure
  coins : List Interval
  cap : Nat
  deriving Repr

def Source.dimension (s : Source) : Nat := s.vertices + s.edges.length + 1 + s.hybrids.length
def Source.inDegree (s : Source) (v : Nat) : Nat := (s.edges.filter (fun e => e.target == v)).length
def Source.outDegree (s : Source) (v : Nat) : Nat := (s.edges.filter (fun e => e.source == v)).length
def Source.isHybrid (s : Source) (v : Nat) : Bool := s.inDegree v == 2 && s.outDegree v == 1

/-- Finite transitive closure; blocked vertices exclude both path endpoints. -/
def Source.reachable (s : Source) (start : Nat) (blocked : Option Nat) : List Nat :=
  if blocked == some start then [] else
  (List.range s.vertices).foldl (fun visited _ =>
    s.edges.foldl (fun visited e =>
      if visited.contains e.source && blocked != some e.target &&
          blocked != some e.source && !visited.contains e.target
      then visited ++ [e.target] else visited) visited) [start]

def Source.valid (s : Source) : Bool :=
  s.vertices > 0 && s.root < s.vertices && s.leaves.length ≥ 2 &&
  s.edges.all (fun e => e.source < s.vertices && e.target < s.vertices) &&
  s.leaves.all (fun v => v < s.vertices) &&
  s.leaves.eraseDups.length == s.leaves.length &&
  s.inDegree s.root == 0 && s.outDegree s.root == 2 &&
  s.leaves.all (fun v => s.inDegree v == 1 && s.outDegree v == 0) &&
  (s.hybrids.map (·.vertex)).eraseDups.length == s.hybrids.length &&
  s.hybrids.all (fun h => h.vertex < s.vertices && s.isHybrid h.vertex &&
    h.incoming0 < s.edges.length && h.incoming1 < s.edges.length &&
    h.incoming0 != h.incoming1 &&
    (s.edges[h.incoming0]?.map (·.target)) == some h.vertex &&
    (s.edges[h.incoming1]?.map (·.target)) == some h.vertex) &&
  (List.range s.vertices).all (fun v =>
    if v == s.root || s.leaves.contains v then true else
      (s.inDegree v == 1 && s.outDegree v == 2) ||
      (s.isHybrid v && (s.hybrids.map (·.vertex)).contains v)) &&
  s.edges.all (fun e => !(s.reachable e.target none).contains e.source) &&
  (List.range s.vertices).all (fun v => (s.reachable s.root none).contains v) &&
  (List.range s.vertices).all (fun v => v == s.root ||
    s.leaves.any (fun leaf => (s.reachable s.root (some v)).contains leaf))

structure Form where
  coeff : List Rat
  constant : Rat
  deriving Repr
def Form.const (n : Nat) (q : Rat) : Form := ⟨List.replicate n 0, q⟩
def Form.variable (n i : Nat) : Form := ⟨(List.range n).map (fun j => if i == j then 1 else 0), 0⟩
def Form.sub (f g : Form) : Form := ⟨f.coeff.zipWith (· - ·) g.coeff, f.constant - g.constant⟩
def Form.scale (q : Rat) (f : Form) : Form := ⟨f.coeff.map (fun a => q*a), q*f.constant⟩
def ageForm (s : Source) : AgeAtom → Form
  | .node i => Form.variable s.dimension i
  | .fixed q => Form.const s.dimension q

def affineRow (strict : Bool) (f g : Form) : Row :=
  ⟨f.coeff.zipWith (· - ·) g.coeff, g.constant-f.constant, strict, []⟩
def comparisonRows (kind : Comparison) (f g : Form) : List Row :=
  let row := affineRow (kind == .strict) f g
  if kind == .equal then [row, affineRow false g f] else [row]
def scaledRows (interval : Interval) (duration inverse : Form) : List Row :=
  (match interval.lower with
   | none => [] | some b => [affineRow b.strict (inverse.scale b.value) duration]) ++
  (match interval.upper with
   | none => [] | some b => [affineRow b.strict duration (inverse.scale b.value)])

def emitRows (input : Input) : List Row :=
  let s := input.source
  let n := s.dimension
  let zero := Form.const n 0
  let one := Form.const n 1
  let coin := fun h => Form.variable n (s.vertices+s.edges.length+1+h)
  let rows :=
    s.edges.flatMap (fun e => comparisonRows .strict (Form.variable n e.target) (Form.variable n e.source)) ++
    s.leaves.flatMap (fun v => comparisonRows .equal (Form.variable n v) zero) ++
    (List.range (s.edges.length+1)).flatMap (fun e => comparisonRows .strict zero (Form.variable n (s.vertices+e))) ++
    (List.range s.hybrids.length).flatMap (fun h => comparisonRows .strict zero (coin h)) ++
    (List.range s.hybrids.length).flatMap (fun h => comparisonRows .strict (coin h) one) ++
    input.chronology.flatMap (fun c => comparisonRows c.kind (ageForm s c.left) (ageForm s c.right)) ++
    input.exposures.flatMap (fun e => scaledRows e.interval
      ((ageForm s e.older).sub (ageForm s e.younger))
      (Form.variable n (s.vertices + e.population.getD s.edges.length))) ++
    input.coins.zipIdx.flatMap (fun (c,h) => scaledRows c (coin h) one)
  rows.zipIdx.map (fun (r,i) => { r with weights := (List.range rows.length).map (fun j => if i == j then 1 else 0) })

def bankNames (s : Source) : List String :=
  (List.range s.vertices).map (fun i => s!"AGE:{i}") ++
  (List.range s.edges.length).map (fun i => s!"RATE:{i}") ++ ["RATE:A"] ++
  (List.range s.hybrids.length).map (fun i => s!"COIN:{i}")

def parseAge (v : Nat) (token : String) : Option AgeAtom := do
  match token.splitOn ":" with
  | ["V", i] =>
      let i ← parseNat i
      if i < v then some (.node i) else none
  | ["Q", q] => some (.fixed (← parse q))
  | _ => none
def parseBound (token : String) : Option (Option Bound) := do
  if token == "NONE" then some none else
  match token.splitOn ":" with
  | ["LE", q] => some (some ⟨← parse q, false⟩)
  | ["LT", q] => some (some ⟨← parse q, true⟩)
  | _ => none
def parsePopulation (e : Nat) (token : String) : Option (Option Nat) := do
  if token == "A" then some none else
  match token.splitOn ":" with
  | ["E", i] =>
      let i ← parseNat i
      if i < e then some (some i) else none
  | _ => none

def parseChart (v e l h c x cap : Nat) (lines : List String) : Option Input := do
  if v < 3 || v > 32 || e < 2 || e > 32 || l < 2 || l > v ||
      h > v || c > 32 || x > 32 || cap > 4096 || v+e+1+h > 32 ||
      lines.length != 2+e+l+2*h+c+x then none
  else
    let root ← match (← lines.head?).splitOn " " with
      | ["ROOT", r] => parseNat r | _ => none
    let edges ← (lines.drop 1 |>.take e).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["EDGE", id, a, b] =>
          if (← parseNat id) != i then none else
          some (⟨← parseNat a, ← parseNat b⟩ : Edge)
      | _ => none)
    let leaves ← (lines.drop (1+e) |>.take l).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["LEAF", id, a] => if (← parseNat id) != i then none else parseNat a
      | _ => none)
    let hybrids ← (lines.drop (1+e+l) |>.take h).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["HYBRID", id, a, p, q] =>
          if (← parseNat id) != i then none else
          some (⟨← parseNat a, ← parseNat p, ← parseNat q⟩ : Hybrid)
      | _ => none)
    let chronology ← (lines.drop (1+e+l+h) |>.take c).mapM (fun s => do
      match s.splitOn " " with
      | ["AGE", kind, a, b] =>
          let kind ← if kind == "LT" then some Comparison.strict else
            if kind == "LE" then some Comparison.weak else if kind == "EQ" then some Comparison.equal else none
          some (⟨kind, ← parseAge v a, ← parseAge v b⟩ : AgeConstraint)
      | _ => none)
    let exposures ← (lines.drop (1+e+l+h+c) |>.take x).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["EXPOSURE", id, p, a, b, lo, hi] =>
          if (← parseNat id) != i then none else
          some (⟨← parsePopulation e p, ← parseAge v a, ← parseAge v b,
            ⟨← parseBound lo, ← parseBound hi⟩⟩ : Exposure)
      | _ => none)
    let coins ← (lines.drop (1+e+l+h+c+x) |>.take h).zipIdx.mapM (fun (s,i) => do
      match s.splitOn " " with
      | ["COIN", id, lo, hi] =>
          if (← parseNat id) != i then none else
          some (⟨← parseBound lo, ← parseBound hi⟩ : Interval)
      | _ => none)
    let input : Input := ⟨⟨v,root,edges,leaves,hybrids⟩,chronology,exposures,coins,cap⟩
    if !input.source.valid || (emitRows input).length > 128 then none else some input

def matrix (input : Input) (rows : List Row) : String :=
  s!"BANK {input.source.dimension} " ++ String.intercalate " " (bankNames input.source) ++ "\n" ++
  s!"MATRIX {input.source.dimension} {rows.length} {input.cap}\n" ++
  String.join (rows.map (fun r => (if r.strict then "LT " else "LE ") ++ wire r.bound ++
    " " ++ String.intercalate " " (r.coeff.map wire) ++ "\n")) ++
  "END_MATRIX\nGATE SOURCE_ADMISSION_NOT_ESTABLISHED\n"

end GParity.Chart

namespace UnifiedLean.G6.NaturalCellInverseRates
structure RationalBound where
  value : ℚ
  strict : Bool

structure RationalInterval where
  lower : Option RationalBound
  upper : Option RationalBound

def RationalInterval.contains (c : RationalInterval) (x : ℝ) : Prop :=
  (∀ b ∈ c.lower, if b.strict then (b.value : ℝ) < x else (b.value : ℝ) ≤ x) ∧
  (∀ b ∈ c.upper, if b.strict then x < (b.value : ℝ) else x ≤ (b.value : ℝ))

/-- Every row is affine in duration d and the ONE physical inverse rate u.
An absent upper endpoint (saturation) remains absent. -/
def RationalInterval.scaled (c : RationalInterval) (d u : ℝ) : Prop :=
  (∀ b ∈ c.lower, if b.strict then (b.value : ℝ) * u < d else (b.value : ℝ) * u ≤ d) ∧
  (∀ b ∈ c.upper, if b.strict then d < (b.value : ℝ) * u else d ≤ (b.value : ℝ) * u)

inductive AgeComparison
  | strict | weak | equal

def AgeComparison.holds (cmp : AgeComparison) (x y : ℝ) : Prop :=
  match cmp with
  | .strict => x < y
  | .weak => x ≤ y
  | .equal => x = y


end UnifiedLean.G6.NaturalCellInverseRates

namespace UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open scoped BigOperators

structure Affine (n : ℕ) where
  coeff : Fin n → ℚ
  constant : ℚ

def Affine.eval {n : ℕ} (f : Affine n) (x : Fin n → ℝ) : ℝ :=
  (f.constant : ℝ) + ∑ i, (f.coeff i : ℝ)*x i

def Affine.const {n : ℕ} (q : ℚ) : Affine n := ⟨fun _ => 0,q⟩
def Affine.variable {n : ℕ} (i : Fin n) : Affine n :=
  ⟨fun j => if j=i then 1 else 0,0⟩
def Affine.sub {n : ℕ} (f g : Affine n) : Affine n :=
  ⟨fun i => f.coeff i-g.coeff i,f.constant-g.constant⟩
def Affine.scale {n : ℕ} (q : ℚ) (f : Affine n) : Affine n :=
  ⟨fun i => q*f.coeff i,q*f.constant⟩

@[simp] theorem Affine.eval_const {n : ℕ} (q : ℚ) (x : Fin n → ℝ) :
    (Affine.const q).eval x = q := by simp [Affine.eval, Affine.const]
@[simp] theorem Affine.eval_variable {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    (Affine.variable i).eval x = x i := by
  simp only [Affine.eval, Affine.variable, Rat.cast_zero, zero_add]
  calc
    (∑ j, (↑(if j=i then (1 : ℚ) else 0) : ℝ)*x j) =
        ∑ j, if j=i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> simp_all
    _ = x i := by simp
@[simp] theorem Affine.eval_sub {n : ℕ} (f g : Affine n) (x : Fin n → ℝ) :
    (f.sub g).eval x = f.eval x-g.eval x := by
  simp only [Affine.eval, Affine.sub, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
  ring
@[simp] theorem Affine.eval_scale {n : ℕ} (q : ℚ) (f : Affine n) (x : Fin n → ℝ) :
    (f.scale q).eval x = (q : ℝ)*f.eval x := by
  simp only [Affine.eval, Affine.scale, Rat.cast_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

def affineRow {n : ℕ} (s : Bool) (f g : Affine n) : Row n :=
  ⟨fun i => f.coeff i-g.coeff i,g.constant-f.constant,s⟩

@[simp] theorem affineRow_holds {n : ℕ} (s : Bool) (f g : Affine n) (x : Fin n → ℝ) :
    (affineRow s f g).Holds x ↔ StrictAffineElimination.Rel s (f.eval x) (g.eval x) := by
  simp only [Row.Holds, Row.eval, affineRow, Rat.cast_sub, sub_mul,
    Finset.sum_sub_distrib, Affine.eval]
  cases s <;> simp only [StrictAffineElimination.Rel, Bool.false_eq_true, if_false, if_true]
  all_goals constructor <;> intro h <;> linarith

def comparisonRows {n : ℕ} (cmp : AgeComparison) (f g : Affine n) : Finset (Row n) :=
  match cmp with
  | .strict => {affineRow true f g}
  | .weak => {affineRow false f g}
  | .equal => {affineRow false f g,affineRow false g f}

@[simp] theorem comparisonRows_holds {n : ℕ} (cmp : AgeComparison)
    (f g : Affine n) (x : Fin n → ℝ) :
    (∀ r ∈ comparisonRows cmp f g, r.Holds x) ↔ cmp.holds (f.eval x) (g.eval x) := by
  cases cmp <;> simp [comparisonRows, AgeComparison.holds, StrictAffineElimination.Rel]
  exact le_antisymm_iff.symm

def scaledRows {n : ℕ} (c : RationalInterval) (d u : Affine n) : Finset (Row n) :=
  (match c.lower with | none => ∅ | some b => {affineRow b.strict (u.scale b.value) d}) ∪
  (match c.upper with | none => ∅ | some b => {affineRow b.strict d (u.scale b.value)})

@[simp] theorem scaledRows_holds {n : ℕ} (c : RationalInterval) (d u : Affine n)
    (x : Fin n → ℝ) :
    (∀ r ∈ scaledRows c d u, r.Holds x) ↔ c.scaled (d.eval x) (u.eval x) := by
  rcases c with ⟨lo,hi⟩
  cases lo <;> cases hi <;> simp [scaledRows, RationalInterval.scaled, StrictAffineElimination.Rel]


end UnifiedLean.G6.NaturalCellAffineCompiler

namespace UnifiedLean.G6.NaturalCellOrderedCompiler
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
def comparisonList {n : ℕ} (cmp : AgeComparison) (f g : Affine n) : List (Row n) :=
  match cmp with
  | .strict => [affineRow true f g]
  | .weak => [affineRow false f g]
  | .equal => [affineRow false f g, affineRow false g f]

theorem comparisonList_toFinset {n : ℕ} (cmp : AgeComparison) (f g : Affine n) :
    (comparisonList cmp f g).toFinset = comparisonRows cmp f g := by
  cases cmp <;> simp [comparisonList, comparisonRows]

def scaledList {n : ℕ} (c : RationalInterval) (d u : Affine n) : List (Row n) :=
  (match c.lower with | none => [] | some b => [affineRow b.strict (u.scale b.value) d]) ++
  (match c.upper with | none => [] | some b => [affineRow b.strict d (u.scale b.value)])

theorem scaledList_toFinset {n : ℕ} (c : RationalInterval) (d u : Affine n) :
    (scaledList c d u).toFinset = scaledRows c d u := by
  rcases c with ⟨lo, hi⟩
  cases lo <;> cases hi <;> simp [scaledList, scaledRows]

def encodeRow {n : ℕ} (r : Row n) : GParity.Affine.Row :=
  ⟨List.ofFn r.coeff, r.bound, r.strict, []⟩

def encodeRows {n : ℕ} (rows : List (Row n)) : List GParity.Affine.Row :=
  rows.map encodeRow


end UnifiedLean.G6.NaturalCellOrderedCompiler


/-!
Value-level affine-form correspondence for the EXISTING CHART emitter.
This relates its coefficients/bounds/strictness to the source-typed row
constructors. It does not prove Rust execution, parser admission or the
complete original-source/ordered-emission relation.
-/
namespace Astra.NativeCellFormReflection

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler

variable {n : ℕ}

def encodeForm (f : Affine n) : GParity.Chart.Form :=
  ⟨List.ofFn f.coeff, f.constant⟩

theorem encodeForm_const (q : ℚ) :
    encodeForm (Affine.const (n := n) q) = GParity.Chart.Form.const n q := by
  apply congrArg₂ GParity.Chart.Form.mk
  · simp [encodeForm, Affine.const, GParity.Chart.Form.const]
  · rfl

theorem encodeForm_variable (i : Fin n) :
    encodeForm (Affine.variable i) = GParity.Chart.Form.variable n i.val := by
  apply congrArg₂ GParity.Chart.Form.mk
  · change List.ofFn (fun k : Fin n => if k = i then (1 : ℚ) else 0) =
      (List.range n).map (fun k => if i.val == k then (1 : ℚ) else 0)
    apply List.ext_getElem
    · simp
    · intro j hj hk
      rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      by_cases h : j = i.val
      · simp [Fin.ext_iff, h]
      · have hi : i.val ≠ j := Ne.symm h
        simp [Fin.ext_iff, h, hi]
  · rfl

theorem encodeForm_sub (f g : Affine n) :
    encodeForm (f.sub g) = (encodeForm f).sub (encodeForm g) := by
  apply congrArg₂ GParity.Chart.Form.mk
  · apply List.ext_getElem
    · simp [encodeForm, Affine.sub, GParity.Chart.Form.sub]
    · intro j hj hk
      simp_all [encodeForm, Affine.sub, GParity.Chart.Form.sub]
  · rfl

theorem encodeForm_scale (q : ℚ) (f : Affine n) :
    encodeForm (f.scale q) = (encodeForm f).scale q := by
  apply congrArg₂ GParity.Chart.Form.mk
  · apply List.ext_getElem
    · simp [encodeForm, Affine.scale, GParity.Chart.Form.scale]
    · intro j hj hk
      simp_all [encodeForm, Affine.scale, GParity.Chart.Form.scale]
  · rfl

theorem affineRow_correspondence (s : Bool) (f g : Affine n) :
    GParity.Chart.affineRow s (encodeForm f) (encodeForm g) =
      encodeRow (affineRow s f g) := by
  apply congrArg (fun coeff : List Rat =>
    (⟨coeff, g.constant - f.constant, s, []⟩ : GParity.Affine.Row))
  exact (congrArg GParity.Chart.Form.coeff (encodeForm_sub f g)).symm

def encodeComparison : AgeComparison → GParity.Chart.Comparison
  | .strict => .strict
  | .weak => .weak
  | .equal => .equal

def encodeBound (b : RationalBound) : GParity.Chart.Bound :=
  ⟨b.value, b.strict⟩

def encodeInterval (c : RationalInterval) : GParity.Chart.Interval :=
  ⟨c.lower.map encodeBound, c.upper.map encodeBound⟩

theorem comparison_correspondence (cmp : AgeComparison) (f g : Affine n) :
    GParity.Chart.comparisonRows (encodeComparison cmp) (encodeForm f) (encodeForm g) =
      encodeRows (comparisonList cmp f g) := by
  cases cmp with
  | strict =>
    change [GParity.Chart.affineRow true (encodeForm f) (encodeForm g)] =
      [encodeRow (affineRow true f g)]
    rw [affineRow_correspondence]
  | weak =>
    change [GParity.Chart.affineRow false (encodeForm f) (encodeForm g)] =
      [encodeRow (affineRow false f g)]
    rw [affineRow_correspondence]
  | equal =>
    change [GParity.Chart.affineRow false (encodeForm f) (encodeForm g),
      GParity.Chart.affineRow false (encodeForm g) (encodeForm f)] =
      [encodeRow (affineRow false f g), encodeRow (affineRow false g f)]
    rw [affineRow_correspondence, affineRow_correspondence]

theorem scaled_correspondence (c : RationalInterval) (d u : Affine n) :
    GParity.Chart.scaledRows (encodeInterval c) (encodeForm d) (encodeForm u) =
      encodeRows (scaledList c d u) := by
  rcases c with ⟨lo, hi⟩
  cases lo <;> cases hi <;>
    simp [encodeInterval, encodeBound, GParity.Chart.scaledRows,
      scaledList, encodeRows, ← encodeForm_scale, affineRow_correspondence]

end Astra.NativeCellFormReflection


/-!
Raw edge-indexed graph foundations for the source network class.

Edges have their own type: distinct edges with the same endpoints are NOT
identified.  In particular the source's parallel two-cycles are not lost.
No canonical-blob representation, quartet factorization, circular metric,
or desired conclusion is a field of these structures.

Root suppression, planar embeddings, galledness/level certification, canonical
coverage, and actual quartet composition are separate proof obligations.
-/

namespace Nanuq.Source

universe u v w

structure EdgeGraph (V : Type u) (E : Type v) where
  source : E → V
  target : E → V

namespace EdgeGraph

variable {V : Type u} {E : Type v} (G : EdgeGraph V E)

/-- Undirected incidence still refers to the individual edge identity. -/
def Inc (e : E) (a b : V) : Prop :=
  (G.source e = a ∧ G.target e = b) ∨
  (G.source e = b ∧ G.target e = a)

theorem inc_symm {e : E} {a b : V} (h : G.Inc e a b) : G.Inc e b a :=
  h.symm

theorem inc_source_target (e : E) : G.Inc e (G.source e) (G.target e) :=
  Or.inl ⟨rfl, rfl⟩

def UStep (keep : E → Prop) (a b : V) : Prop :=
  ∃ e, keep e ∧ G.Inc e a b

def UReach (keep : E → Prop) (a b : V) : Prop :=
  Relation.ReflTransGen (G.UStep keep) a b

theorem ustep_symm {keep : E → Prop} {a b : V} (h : G.UStep keep a b) :
    G.UStep keep b a := by
  obtain ⟨e, he, hab⟩ := h
  exact ⟨e, he, G.inc_symm hab⟩

theorem ustep_mono {keep more : E → Prop} (hm : ∀ e, keep e → more e)
    {a b : V} (h : G.UStep keep a b) : G.UStep more a b := by
  obtain ⟨e, he, hab⟩ := h
  exact ⟨e, hm e he, hab⟩

theorem ureach_refl (keep : E → Prop) (a : V) : G.UReach keep a a :=
  .refl

theorem ureach_single {keep : E → Prop} {a b : V} (h : G.UStep keep a b) :
    G.UReach keep a b :=
  Relation.ReflTransGen.single h

theorem ureach_trans {keep : E → Prop} {a b c : V}
    (hab : G.UReach keep a b) (hbc : G.UReach keep b c) : G.UReach keep a c :=
  hab.trans hbc

theorem ureach_symm {keep : E → Prop} {a b : V}
    (h : G.UReach keep a b) : G.UReach keep b a := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact (G.ureach_single (G.ustep_symm hstep)).trans ih

theorem ureach_mono {keep more : E → Prop} (hm : ∀ e, keep e → more e)
    {a b : V} (h : G.UReach keep a b) : G.UReach more a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (G.ustep_mono hm hstep)

/-- Deletion removes one edge ID, not all edges with the same endpoints. -/
def ReachWithout (e : E) (a b : V) : Prop :=
  G.UReach (fun f => f ≠ e) a b

/-- An edge is a bridge precisely when its endpoints disconnect on its deletion. -/
def IsBridge (e : E) : Prop :=
  ¬ G.ReachWithout e (G.source e) (G.target e)

theorem not_bridge_of_detour {e : E}
    (h : G.ReachWithout e (G.source e) (G.target e)) : ¬ G.IsBridge e := by
  intro hb
  exact hb h

theorem not_bridge_of_parallel {e f : E} (hne : f ≠ e)
    (hs : G.source f = G.source e) (ht : G.target f = G.target e) :
    ¬ G.IsBridge e := by
  apply G.not_bridge_of_detour
  exact G.ureach_single ⟨f, hne, Or.inl ⟨hs, ht⟩⟩

theorem not_bridge_of_loop {e : E} (h : G.source e = G.target e) :
    ¬ G.IsBridge e := by
  apply G.not_bridge_of_detour
  rw [← h]
  exact .refl

theorem bridge_endpoints_ne {e : E} (h : G.IsBridge e) :
    G.source e ≠ G.target e := by
  intro heq
  exact G.not_bridge_of_loop heq h

/-- The actual blob equivalence: connectivity after deleting every bridge. -/
def SameBlob (a b : V) : Prop :=
  G.UReach (fun e => ¬ G.IsBridge e) a b

theorem sameBlob_refl (a : V) : G.SameBlob a a := .refl

theorem sameBlob_symm {a b : V} (h : G.SameBlob a b) : G.SameBlob b a :=
  G.ureach_symm h

theorem sameBlob_trans {a b c : V} (hab : G.SameBlob a b)
    (hbc : G.SameBlob b c) : G.SameBlob a c :=
  hab.trans hbc

def blobSetoid : Setoid V where
  r := G.SameBlob
  iseqv := ⟨G.sameBlob_refl, G.sameBlob_symm, G.sameBlob_trans⟩

def Blob := Quotient G.blobSetoid

def blobOf (a : V) : G.Blob := Quotient.mk G.blobSetoid a

theorem nonbridge_sameBlob {e : E} (h : ¬ G.IsBridge e) :
    G.SameBlob (G.source e) (G.target e) :=
  G.ureach_single ⟨e, h, G.inc_source_target e⟩

theorem bridge_not_sameBlob {e : E} (h : G.IsBridge e) :
    ¬ G.SameBlob (G.source e) (G.target e) := by
  intro hab
  apply h
  apply G.ureach_mono (keep := fun f => ¬ G.IsBridge f) _ hab
  intro f hf hfe
  subst f
  exact hf h

theorem bridge_blob_ne {e : E} (h : G.IsBridge e) :
    G.blobOf (G.source e) ≠ G.blobOf (G.target e) := by
  intro heq
  exact G.bridge_not_sameBlob h (Quotient.exact heq)

def DStep (a b : V) : Prop :=
  ∃ e, G.source e = a ∧ G.target e = b

def DReach (a b : V) : Prop := Relation.ReflTransGen G.DStep a b

def Acyclic : Prop := ∀ a, ¬ Relation.TransGen G.DStep a a

theorem dstep_ureach {a b : V} (h : G.DStep a b) :
    G.UReach (fun _ => True) a b := by
  obtain ⟨e, hs, ht⟩ := h
  exact G.ureach_single ⟨e, trivial, Or.inl ⟨hs, ht⟩⟩

theorem dreach_ureach {a b : V} (h : G.DReach a b) :
    G.UReach (fun _ => True) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (G.dstep_ureach hstep)

theorem acyclic_no_loop (h : G.Acyclic) (e : E) :
    G.source e ≠ G.target e := by
  intro heq
  apply h (G.source e)
  exact Relation.TransGen.single ⟨e, rfl, heq.symm⟩

theorem dreach_antisymm (h : G.Acyclic) {a b : V}
    (hab : G.DReach a b) (hba : G.DReach b a) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with heq | ⟨c, hac, hcb⟩
  · exact heq
  · exact False.elim (h a (Relation.TransGen.head' hac (hcb.trans hba)))

/-- A directed walk avoiding a vertex, including its two endpoints. -/
def AvoidReach (blocked a b : V) : Prop :=
  a ≠ blocked ∧ b ≠ blocked ∧
  Relation.ReflTransGen (fun x y => G.DStep x y ∧ x ≠ blocked ∧ y ≠ blocked) a b

def Dominates (root blocked a : V) : Prop := ¬ G.AvoidReach blocked root a

theorem root_dominates (root a : V) : G.Dominates root root a := by
  intro h
  exact h.1 rfl

theorem self_dominates (root a : V) : G.Dominates root a a := by
  intro h
  exact h.2.1 rfl

section FiniteDegree
variable [Fintype E] [DecidableEq V]

def inDegree (a : V) : Nat :=
  (Finset.univ.filter (fun e => G.target e = a)).card

def outDegree (a : V) : Nat :=
  (Finset.univ.filter (fun e => G.source e = a)).card

def IsHybrid (a : V) : Prop := G.inDegree a = 2 ∧ G.outDegree a = 1

end FiniteDegree
end EdgeGraph

/-- Raw finite rooted binary phylogenetic data with the source LSA condition.
`rooted` is ordinary reachability from the root, not a decomposition premise.
This structure deliberately does NOT claim galledness, level, or planarity.
-/
structure RootedBinary (V : Type u) (E : Type v) (X : Type w)
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] where
  graph : EdgeGraph V E
  root : V
  leaf : X ↪ V
  at_least_two_taxa : 2 ≤ Fintype.card X
  root_degrees : graph.inDegree root = 0 ∧ graph.outDegree root = 2
  leaf_degrees : ∀ x, graph.inDegree (leaf x) = 1 ∧ graph.outDegree (leaf x) = 0
  internal_degrees : ∀ a, a ≠ root → (∀ x, leaf x ≠ a) →
    (graph.inDegree a = 1 ∧ graph.outDegree a = 2) ∨ graph.IsHybrid a
  acyclic : graph.Acyclic
  rooted : ∀ a, graph.DReach root a
  least_stable : ∀ a, (∀ x, graph.Dominates root a (leaf x)) → a = root

namespace RootedBinary
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem leaf_ne_root (x : X) : N.leaf x ≠ N.root := by
  intro heq
  have h := (N.leaf_degrees x).2
  rw [heq, N.root_degrees.2] at h
  cases h

theorem underlying_connected (a b : V) :
    N.graph.UReach (fun _ => True) a b :=
  (N.graph.ureach_symm (N.graph.dreach_ureach (N.rooted a))).trans
    (N.graph.dreach_ureach (N.rooted b))

theorem unique_common_dominator {a : V}
    (h : ∀ x, N.graph.Dominates N.root a (N.leaf x)) : a = N.root :=
  N.least_stable a h

end RootedBinary
end Nanuq.Source

#print axioms Nanuq.Source.EdgeGraph.not_bridge_of_parallel
#print axioms Nanuq.Source.EdgeGraph.bridge_not_sameBlob
#print axioms Nanuq.Source.EdgeGraph.bridge_blob_ne
#print axioms Nanuq.Source.EdgeGraph.dreach_antisymm
#print axioms Nanuq.Source.RootedBinary.underlying_connected

namespace UnifiedLean.Source.NativeParentRouting
open Nanuq.Source
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
abbrev Hybrid (N : RootedBinary V E X) := {v : V // N.graph.IsHybrid v}
end UnifiedLean.Source.NativeParentRouting

namespace UnifiedLean.G6.NaturalCellInverseRates
inductive AgeAtom (V : Type*)
  | node (v : V)
  | fixed (q : ℚ)

def AgeAtom.eval (a : V → ℝ) : AgeAtom V → ℝ
  | .node v => a v
  | .fixed q => q

structure Exposure (V E : Type*) where
  population : Option E
  younger : AgeAtom V
  older : AgeAtom V
  cell : RationalInterval

def Exposure.duration (e : Exposure V E) (a : V → ℝ) : ℝ :=
  e.older.eval a - e.younger.eval a

structure AgeConstraint (V : Type*) where
  left : AgeAtom V
  right : AgeAtom V
  comparison : AgeComparison

def AgeConstraint.holds (c : AgeConstraint V) (a : V → ℝ) : Prop :=
  c.comparison.holds (c.left.eval a) (c.right.eval a)


end UnifiedLean.G6.NaturalCellInverseRates

namespace UnifiedLean.G6.NaturalCellAffineCompiler
open Nanuq.Source
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.Source.NativeParentRouting
variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]

abbrev BankVar (N : RootedBinary V E X) := V ⊕ (Option E ⊕ Hybrid N)
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)

instance hybridPredicateDecidable : DecidablePred (N.graph.IsHybrid) := by
  intro v
  unfold Nanuq.Source.EdgeGraph.IsHybrid
  infer_instance

def agesOf (x : Fin n → ℝ) (v : V) : ℝ := x (layout (Sum.inl v))
def inverseRatesOf (x : Fin n → ℝ) (e : Option E) : ℝ := x (layout (Sum.inr (Sum.inl e)))
def coinsOf (x : Fin n → ℝ) (h : Hybrid N) : ℝ := x (layout (Sum.inr (Sum.inr h)))

def bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) (i : Fin n) : ℝ :=
  match layout.symm i with
  | .inl v => a v
  | .inr (.inl e) => u e
  | .inr (.inr h) => g h

@[simp] theorem agesOf_bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) :
    agesOf N layout (bankVector N layout a u g) = a := by
  funext v
  simp [agesOf, bankVector]
@[simp] theorem inverseRatesOf_bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) :
    inverseRatesOf N layout (bankVector N layout a u g) = u := by
  funext e
  simp [inverseRatesOf, bankVector]
@[simp] theorem coinsOf_bankVector (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) :
    coinsOf N layout (bankVector N layout a u g) = g := by
  funext h
  simp [coinsOf, bankVector]

def ageForm (atom : AgeAtom V) : Affine n :=
  match atom with
  | .node v => .variable (layout (.inl v))
  | .fixed q => .const q

def inverseForm (e : Option E) : Affine n := .variable (layout (.inr (.inl e)))
def coinForm (h : Hybrid N) : Affine n := .variable (layout (.inr (.inr h)))
def durationForm (e : Exposure V E) : Affine n :=
  (ageForm N layout e.older).sub (ageForm N layout e.younger)

def chronologyRows (c : AgeConstraint V) : Finset (Row n) :=
  comparisonRows c.comparison (ageForm N layout c.left) (ageForm N layout c.right)

def compileCell (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Finset (Row n) :=
  (Finset.univ.biUnion fun e : E =>
    comparisonRows .strict (ageForm N layout (.node (N.graph.target e)))
      (ageForm N layout (.node (N.graph.source e)))) ∪
  (Finset.univ.biUnion fun v : X =>
    comparisonRows .equal (ageForm N layout (.node (N.leaf v))) (.const 0)) ∪
  (Finset.univ.biUnion fun e : Option E =>
    comparisonRows .strict (.const 0) (inverseForm N layout e)) ∪
  (Finset.univ.biUnion fun h : Hybrid N =>
    comparisonRows .strict (.const 0) (coinForm N layout h)) ∪
  (Finset.univ.biUnion fun h : Hybrid N =>
    comparisonRows .strict (coinForm N layout h) (.const 1)) ∪
  (Finset.univ.biUnion fun j : C => chronologyRows N layout (chronology j)) ∪
  (Finset.univ.biUnion fun i : I =>
    scaledRows (rows i).cell (durationForm N layout (rows i))
      (inverseForm N layout (rows i).population)) ∪
  (Finset.univ.biUnion fun h : Hybrid N =>
    scaledRows (coins h) (coinForm N layout h) (.const 1))


end UnifiedLean.G6.NaturalCellAffineCompiler

namespace UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.StrictAffineElimination
def decodeVector (n : ℕ) (x : List Rat) : Fin n → ℚ :=
  fun i => x[i.val]?.getD 0

def decodeRow (n : ℕ) (r : GParity.Affine.Row) : Row n :=
  ⟨decodeVector n r.coeff, r.bound, r.strict⟩

def decodeRows (n : ℕ) (rs : List GParity.Affine.Row) : List (Row n) :=
  rs.map (decodeRow n)

def RowsWellFormed (n : ℕ) (rs : List GParity.Affine.Row) : Prop :=
  ∀ r ∈ rs, r.coeff.length = n


end UnifiedLean.G6.WireAffineRefinement

namespace UnifiedLean.G6.NaturalCellOrderedCompiler
open Nanuq.Source
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.Source.NativeParentRouting
theorem flatMap_toFinset_univ {A B : Type*} [Fintype A] [DecidableEq B]
    (xs : List A) (hxs : ∀ a, a ∈ xs) (f : A → List B) :
    (xs.flatMap f).toFinset = Finset.univ.biUnion (fun a => (f a).toFinset) := by
  ext b
  simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, _, hb⟩
    exact ⟨a, hb⟩
  · rintro ⟨a, hb⟩
    exact ⟨a, hxs a, hb⟩

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)

def compileCellList (edges : List E) (leaves : List X) (populations : List (Option E))
    (hybrids : List (Hybrid N)) (chronologyIds : List C) (exposureIds : List I)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : List (Row n) :=
  edges.flatMap (fun e => comparisonList .strict
    (ageForm N layout (.node (N.graph.target e)))
    (ageForm N layout (.node (N.graph.source e)))) ++
  leaves.flatMap (fun x => comparisonList .equal
    (ageForm N layout (.node (N.leaf x))) (.const 0)) ++
  populations.flatMap (fun e => comparisonList .strict (.const 0) (inverseForm N layout e)) ++
  hybrids.flatMap (fun h => comparisonList .strict (.const 0) (coinForm N layout h)) ++
  hybrids.flatMap (fun h => comparisonList .strict (coinForm N layout h) (.const 1)) ++
  chronologyIds.flatMap (fun j => comparisonList (chronology j).comparison
    (ageForm N layout (chronology j).left) (ageForm N layout (chronology j).right)) ++
  exposureIds.flatMap (fun i => scaledList (rows i).cell (durationForm N layout (rows i))
    (inverseForm N layout (rows i).population)) ++
  hybrids.flatMap (fun h => scaledList (coins h) (coinForm N layout h) (.const 1))

/-- This fixes the emitted matrix mathematically, without assigning the
inherited finite set a fictitious canonical list order. -/
theorem compileCellList_toFinset (edges : List E) (leaves : List X)
    (populations : List (Option E)) (hybrids : List (Hybrid N))
    (chronologyIds : List C) (exposureIds : List I)
    (hedges : ∀ e, e ∈ edges) (hleaves : ∀ x, x ∈ leaves)
    (hpopulations : ∀ e, e ∈ populations) (hhybrids : ∀ h, h ∈ hybrids)
    (hchronology : ∀ j, j ∈ chronologyIds) (hexposures : ∀ i, i ∈ exposureIds)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) :
    (compileCellList N layout edges leaves populations hybrids chronologyIds exposureIds
      chronology rows coins).toFinset = compileCell N layout chronology rows coins := by
  simp only [compileCellList, List.toFinset_append,
    flatMap_toFinset_univ edges hedges, flatMap_toFinset_univ leaves hleaves,
    flatMap_toFinset_univ populations hpopulations,
    flatMap_toFinset_univ hybrids hhybrids,
    flatMap_toFinset_univ chronologyIds hchronology,
    flatMap_toFinset_univ exposureIds hexposures,
    comparisonList_toFinset, scaledList_toFinset, compileCell, chronologyRows]

theorem decodeVector_ofFn {n : ℕ} (x : Fin n → ℚ) :
    decodeVector n (List.ofFn x) = x := by
  funext i
  simp [decodeVector, List.getElem?_ofFn, i.isLt]

theorem decode_encodeRow {n : ℕ} (r : Row n) :
    decodeRow n (encodeRow r) = r := by
  cases r
  simp only [decodeRow, encodeRow, decodeVector_ofFn]

theorem decode_encodeRows {n : ℕ} (rows : List (Row n)) :
    decodeRows n (encodeRows rows) = rows := by
  simp only [decodeRows, encodeRows, List.map_map, Function.comp_def, decode_encodeRow,
    List.map_id_fun']
  rfl

theorem encodedRows_wellFormed {n : ℕ} (rows : List (Row n)) :
    RowsWellFormed n (encodeRows rows) := by
  intro r hr
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hr
  exact List.length_ofFn


end UnifiedLean.G6.NaturalCellOrderedCompiler


/-!
Aggregate the existing CHART emitter into the existing source-typed compiler.
All input relations below concern individual fields, occurrence lists and
coordinate positions. No emitted-matrix equality is an input premise.
The captured request/parser/source admission and physical readout remain
separate obligations. Internal unit bookkeeping weights are erased explicitly.
-/
namespace Astra.NativeCellAggregateReflection

open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.NaturalCellInverseRates
open UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler
open UnifiedLean.G6.WireAffineRefinement
open Astra.NativeCellFormReflection

def eraseWeights (rows : List GParity.Affine.Row) : List GParity.Affine.Row :=
  rows.map (fun r => {r with weights := []})

theorem eraseWeights_append (a b : List GParity.Affine.Row) :
    eraseWeights (a ++ b) = eraseWeights a ++ eraseWeights b := by
  simp [eraseWeights]

theorem eraseWeights_flatMap {A : Type*} (xs : List A)
    (f : A → List GParity.Affine.Row) :
    eraseWeights (xs.flatMap f) = xs.flatMap (fun x => eraseWeights (f x)) := by
  simp [eraseWeights, List.map_flatMap]

theorem eraseWeights_comparison (cmp : GParity.Chart.Comparison)
    (f g : GParity.Chart.Form) :
    eraseWeights (GParity.Chart.comparisonRows cmp f g) =
      GParity.Chart.comparisonRows cmp f g := by
  cases cmp <;> rfl

theorem eraseWeights_scaled (c : GParity.Chart.Interval)
    (d u : GParity.Chart.Form) :
    eraseWeights (GParity.Chart.scaledRows c d u) =
      GParity.Chart.scaledRows c d u := by
  rcases c with ⟨lo,hi⟩
  cases lo <;> cases hi <;> rfl

theorem eraseWeights_bookkeeping (rows : List GParity.Affine.Row) :
    eraseWeights (rows.zipIdx.map (fun (r,i) =>
      {r with weights := (List.range rows.length).map (fun j => if i == j then 1 else 0)})) =
      eraseWeights rows := by
  apply List.ext_getElem
  · simp [eraseWeights]
  · intro i hi hj
    simp [eraseWeights]

theorem decodeRows_eraseWeights (n : ℕ) (rows : List GParity.Affine.Row) :
    decodeRows n (eraseWeights rows) = decodeRows n rows := by
  simp [decodeRows, eraseWeights, List.map_map, decodeRow]

theorem wellFormed_eraseWeights_iff (n : ℕ) (rows : List GParity.Affine.Row) :
    RowsWellFormed n (eraseWeights rows) ↔ RowsWellFormed n rows := by
  simp [RowsWellFormed, eraseWeights]

def reflectAge {V : Type*} (vertex : V → ℕ) : AgeAtom V → GParity.Chart.AgeAtom
  | .node v => .node (vertex v)
  | .fixed q => .fixed q

def reflectChronology {V : Type*} (vertex : V → ℕ) (c : AgeConstraint V) :
    GParity.Chart.AgeConstraint :=
  ⟨encodeComparison c.comparison, reflectAge vertex c.left, reflectAge vertex c.right⟩

def reflectExposure {V E : Type*} (vertex : V → ℕ) (edge : E → ℕ)
    (r : Exposure V E) : GParity.Chart.Exposure :=
  ⟨r.population.map edge, reflectAge vertex r.younger,
    reflectAge vertex r.older, encodeInterval r.cell⟩

variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)
variable (input : GParity.Chart.Input)
variable (edges : List E) (leaves : List X) (populations : List (Option E))
variable (hybrids : List (Hybrid N)) (chronologyIds : List C) (exposureIds : List I)
variable (chronology : C → AgeConstraint V) (exposures : I → Exposure V E)
variable (coins : Hybrid N → RationalInterval)

structure FieldReflection where
  vertex : V → ℕ
  edge : E → ℕ
  hybrid : Hybrid N → ℕ
  dimension : input.source.dimension = n
  age_position : ∀ v, (layout (.inl v)).val = vertex v
  inverse_position : ∀ e, (layout (.inr (.inl e))).val =
    input.source.vertices + (e.map edge).getD input.source.edges.length
  coin_position : ∀ h, (layout (.inr (.inr h))).val =
    input.source.vertices + input.source.edges.length + 1 + hybrid h
  edge_fields : input.source.edges =
    edges.map (fun e => ⟨vertex (N.graph.source e), vertex (N.graph.target e)⟩)
  leaf_fields : input.source.leaves = leaves.map (fun x => vertex (N.leaf x))
  population_order : List.range (input.source.edges.length + 1) =
    populations.map (fun e => (e.map edge).getD input.source.edges.length)
  hybrid_order : List.range input.source.hybrids.length = hybrids.map hybrid
  chronology_fields : input.chronology =
    chronologyIds.map (fun j => reflectChronology vertex (chronology j))
  exposure_fields : input.exposures =
    exposureIds.map (fun i => reflectExposure vertex edge (exposures i))
  coin_fields : input.coins.zipIdx =
    hybrids.map (fun h => (encodeInterval (coins h), hybrid h))

variable {N layout input edges leaves populations hybrids chronologyIds exposureIds chronology exposures coins}
variable (h : FieldReflection N layout input edges leaves populations hybrids
  chronologyIds exposureIds chronology exposures coins)

theorem age_correspondence (a : AgeAtom V) :
    GParity.Chart.ageForm input.source (reflectAge h.vertex a) =
      encodeForm (ageForm N layout a) := by
  cases a with
  | node v => simp only [reflectAge, GParity.Chart.ageForm, ageForm,
      h.dimension, encodeForm_variable, h.age_position]
  | fixed q => simp only [reflectAge, GParity.Chart.ageForm, ageForm,
      h.dimension, encodeForm_const]

theorem inverse_correspondence (e : Option E) :
    GParity.Chart.Form.variable input.source.dimension
      (input.source.vertices + (e.map h.edge).getD input.source.edges.length) =
      encodeForm (inverseForm N layout e) := by
  simp only [inverseForm, encodeForm_variable, h.dimension, h.inverse_position]

theorem coin_correspondence (a : Hybrid N) :
    GParity.Chart.Form.variable input.source.dimension
      (input.source.vertices + input.source.edges.length + 1 + h.hybrid a) =
      encodeForm (coinForm N layout a) := by
  simp only [coinForm, encodeForm_variable, h.dimension, h.coin_position]

include h

theorem erase_emitRows_eq_encoded :
    eraseWeights (GParity.Chart.emitRows input) =
      encodeRows (compileCellList N layout edges leaves populations hybrids
        chronologyIds exposureIds chronology exposures coins) := by
  have he : input.source.edges.flatMap (fun e => GParity.Chart.comparisonRows .strict
      (GParity.Chart.Form.variable input.source.dimension e.target)
      (GParity.Chart.Form.variable input.source.dimension e.source)) =
      edges.flatMap (fun e => encodeRows (comparisonList .strict
        (ageForm N layout (.node (N.graph.target e)))
        (ageForm N layout (.node (N.graph.source e))))) := by
    rw [h.edge_fields]
    simp only [List.flatMap_map]
    congr 1
    funext e
    rw [← comparison_correspondence]
    simp only [encodeComparison, ageForm, encodeForm_variable, h.dimension, h.age_position]
  have hl : input.source.leaves.flatMap (fun v => GParity.Chart.comparisonRows .equal
      (GParity.Chart.Form.variable input.source.dimension v)
      (GParity.Chart.Form.const input.source.dimension 0)) =
      leaves.flatMap (fun x => encodeRows (comparisonList .equal
        (ageForm N layout (.node (N.leaf x))) (.const 0))) := by
    rw [h.leaf_fields]
    simp only [List.flatMap_map]
    congr 1
    funext x
    rw [← comparison_correspondence]
    simp only [encodeComparison, ageForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.age_position]
  have hp : (List.range (input.source.edges.length + 1)).flatMap (fun e =>
      GParity.Chart.comparisonRows .strict (GParity.Chart.Form.const input.source.dimension 0)
        (GParity.Chart.Form.variable input.source.dimension (input.source.vertices + e))) =
      populations.flatMap (fun e => encodeRows (comparisonList .strict
        (.const 0) (inverseForm N layout e))) := by
    rw [h.population_order]
    simp only [List.flatMap_map]
    congr 1
    funext e
    rw [← comparison_correspondence]
    simp only [encodeComparison, inverseForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.inverse_position]
  have h0 : (List.range input.source.hybrids.length).flatMap (fun a =>
      GParity.Chart.comparisonRows .strict (GParity.Chart.Form.const input.source.dimension 0)
        (GParity.Chart.Form.variable input.source.dimension
          (input.source.vertices + input.source.edges.length + 1 + a))) =
      hybrids.flatMap (fun a => encodeRows (comparisonList .strict (.const 0) (coinForm N layout a))) := by
    rw [h.hybrid_order]
    simp only [List.flatMap_map]
    congr 1
    funext a
    rw [← comparison_correspondence]
    simp only [encodeComparison, coinForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.coin_position]
  have h1 : (List.range input.source.hybrids.length).flatMap (fun a =>
      GParity.Chart.comparisonRows .strict
        (GParity.Chart.Form.variable input.source.dimension
          (input.source.vertices + input.source.edges.length + 1 + a))
        (GParity.Chart.Form.const input.source.dimension 1)) =
      hybrids.flatMap (fun a => encodeRows (comparisonList .strict (coinForm N layout a) (.const 1))) := by
    rw [h.hybrid_order]
    simp only [List.flatMap_map]
    congr 1
    funext a
    rw [← comparison_correspondence]
    simp only [encodeComparison, coinForm, encodeForm_variable, encodeForm_const,
      h.dimension, h.coin_position]
  have hc : input.chronology.flatMap (fun c => GParity.Chart.comparisonRows c.kind
      (GParity.Chart.ageForm input.source c.left) (GParity.Chart.ageForm input.source c.right)) =
      chronologyIds.flatMap (fun j => encodeRows (comparisonList (chronology j).comparison
        (ageForm N layout (chronology j).left) (ageForm N layout (chronology j).right))) := by
    rw [h.chronology_fields]
    simp only [List.flatMap_map]
    congr 1
    funext j
    rw [← comparison_correspondence]
    simp only [reflectChronology, age_correspondence h]
  have hx : input.exposures.flatMap (fun e => GParity.Chart.scaledRows e.interval
      ((GParity.Chart.ageForm input.source e.older).sub (GParity.Chart.ageForm input.source e.younger))
      (GParity.Chart.Form.variable input.source.dimension
        (input.source.vertices + e.population.getD input.source.edges.length))) =
      exposureIds.flatMap (fun i => encodeRows (scaledList (exposures i).cell
        (durationForm N layout (exposures i)) (inverseForm N layout (exposures i).population))) := by
    rw [h.exposure_fields]
    simp only [List.flatMap_map]
    congr 1
    funext i
    rw [← scaled_correspondence]
    simp only [reflectExposure, age_correspondence h, inverse_correspondence h,
      durationForm, encodeForm_sub]
  have hb : input.coins.zipIdx.flatMap (fun (c,a) => GParity.Chart.scaledRows c
      (GParity.Chart.Form.variable input.source.dimension
        (input.source.vertices + input.source.edges.length + 1 + a))
      (GParity.Chart.Form.const input.source.dimension 1)) =
      hybrids.flatMap (fun a => encodeRows (scaledList (coins a)
        (coinForm N layout a) (.const 1))) := by
    rw [h.coin_fields]
    simp only [List.flatMap_map]
    congr 1
    funext a
    rw [← scaled_correspondence]
    rw [coin_correspondence h, encodeForm_const, h.dimension]
  unfold GParity.Chart.emitRows
  rw [eraseWeights_bookkeeping]
  simp only [eraseWeights_append, eraseWeights_flatMap,
    eraseWeights_comparison, eraseWeights_scaled]
  rw [he, hl, hp, h0, h1, hc, hx, hb]
  simp only [compileCellList, encodeRows, List.map_append, List.map_flatMap]

theorem decoded_emitRows_eq_compileCellList :
    decodeRows n (GParity.Chart.emitRows input) =
      compileCellList N layout edges leaves populations hybrids
        chronologyIds exposureIds chronology exposures coins := by
  rw [← decodeRows_eraseWeights n, erase_emitRows_eq_encoded h, decode_encodeRows]

theorem emitted_coefficient_lengths :
    RowsWellFormed n (GParity.Chart.emitRows input) := by
  apply (wellFormed_eraseWeights_iff n _).mp
  rw [erase_emitRows_eq_encoded h]
  exact encodedRows_wellFormed _

theorem decoded_emitRows_toFinset
    (hedges : ∀ e, e ∈ edges) (hleaves : ∀ x, x ∈ leaves)
    (hpopulations : ∀ e, e ∈ populations) (hhybrids : ∀ a, a ∈ hybrids)
    (hchronology : ∀ j, j ∈ chronologyIds) (hexposures : ∀ i, i ∈ exposureIds) :
    (decodeRows n (GParity.Chart.emitRows input)).toFinset =
      compileCell N layout chronology exposures coins := by
  rw [decoded_emitRows_eq_compileCellList h]
  exact compileCellList_toFinset N layout edges leaves populations hybrids
    chronologyIds exposureIds hedges hleaves hpopulations hhybrids
    hchronology hexposures chronology exposures coins

end Astra.NativeCellAggregateReflection

namespace GProgram.G2
open Nanuq.Source
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
structure OriginalHybridParents (N : RootedBinary V E X) where
  hybrid : V
  isHybrid : N.graph.IsHybrid hybrid
  parent0 : E
  parent1 : E
  target0 : N.graph.target parent0 = hybrid
  target1 : N.graph.target parent1 = hybrid
  different : parent0 ≠ parent1

def OriginalHybridParents.parent {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (bit : Bool) : E :=
  if bit then H.parent1 else H.parent0


end GProgram.G2

namespace UnifiedLean.Source.NativeParentRouting
open Nanuq.Source
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
structure OriginalParentRegistry (N : RootedBinary V E X) where
  parents : Hybrid N → GProgram.G2.OriginalHybridParents N
  original_site : ∀ v, (parents v).hybrid = v.1


end UnifiedLean.Source.NativeParentRouting

namespace GProgram.G7.OriginalFiniteEncoding
variable {X ID : Type*} [Fintype X] [Fintype ID]
def vertexCount (n r : ℕ) : ℕ := 2*n + 2*r - 1
def edgeCount (n r : ℕ) : ℕ := 2*n + 3*r - 2

abbrev Code (X ID : Type*) [Fintype X] [Fintype ID] :=
  let nv := vertexCount (Fintype.card X) (Fintype.card ID)
  let ne := edgeCount (Fintype.card X) (Fintype.card ID)
  (Fin ne → Fin nv) × (Fin ne → Fin nv) × Fin nv ×
    (X → Fin nv) × (ID → Fin nv) × (ID → Bool → Fin ne)


end GProgram.G7.OriginalFiniteEncoding

namespace GProgram.G7.OriginalAdmission
open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding UnifiedLean.Source.NativeParentRouting
variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
abbrev NV := Fin (vertexCount (Fintype.card X) (Fintype.card ID))
abbrev NE := Fin (edgeCount (Fintype.card X) (Fintype.card ID))
def codeGraph (c : Code X ID) : EdgeGraph (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)) :=
  ⟨c.1,c.2.1⟩
def codeRoot (c : Code X ID) : NV (X:=X) (ID:=ID) := c.2.2.1
def codeLeaf (c : Code X ID) : X → NV (X:=X) (ID:=ID) := c.2.2.2.1

def BinaryValid (c : Code X ID) : Prop :=
  Function.Injective (codeLeaf c) ∧ 2 ≤ Fintype.card X ∧
  ((codeGraph c).inDegree (codeRoot c) = 0 ∧ (codeGraph c).outDegree (codeRoot c) = 2) ∧
  (∀ x, (codeGraph c).inDegree (codeLeaf c x) = 1 ∧ (codeGraph c).outDegree (codeLeaf c x) = 0) ∧
  (∀ a, a ≠ codeRoot c → (∀ x, codeLeaf c x ≠ a) →
    ((codeGraph c).inDegree a = 1 ∧ (codeGraph c).outDegree a = 2) ∨ (codeGraph c).IsHybrid a) ∧
  (codeGraph c).Acyclic ∧
  (∀ a, (codeGraph c).DReach (codeRoot c) a) ∧
  (∀ a, (∀ x, (codeGraph c).Dominates (codeRoot c) a (codeLeaf c x)) → a = codeRoot c)

def sourceOfValid (c : Code X ID) (h : BinaryValid c) :
    RootedBinary (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)) X where
  graph := codeGraph c
  root := codeRoot c
  leaf := ⟨codeLeaf c,h.1⟩
  at_least_two_taxa := h.2.1
  root_degrees := h.2.2.1
  leaf_degrees := h.2.2.2.1
  internal_degrees := h.2.2.2.2.1
  acyclic := h.2.2.2.2.2.1
  rooted := h.2.2.2.2.2.2.1
  least_stable := h.2.2.2.2.2.2.2

def codeSite (c : Code X ID) : ID → NV (X:=X) (ID:=ID) := c.2.2.2.2.1
def codeParent (c : Code X ID) : ID → Bool → NE (X:=X) (ID:=ID) := c.2.2.2.2.2

def RegistryValid (c : Code X ID) : Prop :=
  Function.Injective (codeSite c) ∧
  (∀ i, (codeGraph c).IsHybrid (codeSite c i)) ∧
  (∀ a, (codeGraph c).IsHybrid a → ∃ i, codeSite c i = a) ∧
  (∀ i b, (codeGraph c).target (codeParent c i b) = codeSite c i) ∧
  (∀ i, codeParent c i false ≠ codeParent c i true)
def decodedHybridMap (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    ID → Hybrid (sourceOfValid c hb) := fun i => ⟨codeSite c i,hr.2.1 i⟩

theorem decodedHybridMap_bijective (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    Function.Bijective (decodedHybridMap c hb hr) := by
  constructor
  · intro i j he
    exact hr.1 (congrArg Subtype.val he)
  · intro h
    obtain ⟨i,hi⟩ := hr.2.2.1 h.val h.property
    exact ⟨i,Subtype.ext hi⟩

def decodedIDs (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    ID ≃ Hybrid (sourceOfValid c hb) where
  toFun := decodedHybridMap c hb hr
  invFun := Fintype.bijInv (decodedHybridMap_bijective c hb hr)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

def decodedRegistry (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    OriginalParentRegistry (sourceOfValid c hb) where
  parents h := {
    hybrid := h.val
    isHybrid := h.property
    parent0 := codeParent c ((decodedIDs c hb hr).symm h) false
    parent1 := codeParent c ((decodedIDs c hb hr).symm h) true
    target0 := by
      have he := hr.2.2.2.1 ((decodedIDs c hb hr).symm h) false
      have hs := congrArg Subtype.val ((decodedIDs c hb hr).apply_symm_apply h)
      exact he.trans hs
    target1 := by
      have he := hr.2.2.2.1 ((decodedIDs c hb hr).symm h) true
      have hs := congrArg Subtype.val ((decodedIDs c hb hr).apply_symm_apply h)
      exact he.trans hs
    different := hr.2.2.2.2 _ }
  original_site _ := rfl

theorem decoded_parent_exact (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (i : ID) (b : Bool) :
    ((decodedRegistry c hb hr).parents ((decodedIDs c hb hr) i)).parent b = codeParent c i b := by
  cases b <;> simp [decodedRegistry,GProgram.G2.OriginalHybridParents.parent]


end GProgram.G7.OriginalAdmission


/-!
Explicit original bank ordering for the existing native row compiler.

The caller supplies occurrence-preserving vertex/edge/hybrid equivalences.
This constructs the shared index layout; it does not acquire or admit a source,
parse a request, interpret a coin or certify an observation law.
-/
namespace Astra.NativeOrderedBankLayout

variable {V E H : Type*} {nv ne nh : ℕ}

/-- All original edges, followed by ONE ancestral population. -/
def populationEquiv (edges : E ≃ Fin ne) : Option E ≃ Fin (ne + 1) :=
  (Equiv.optionCongr edges).trans finSuccEquivLast.symm

/-- Native AGE, edge inverse rates, ancestral inverse rate, then hybrid IDs. -/
def bankEquiv (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) : V ⊕ (Option E ⊕ H) ≃ Fin (nv + ne + 1 + nh) :=
  ((Equiv.sumCongr vertices
      ((Equiv.sumCongr (populationEquiv edges) hybrids).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by simp [Nat.add_assoc]))

@[simp] theorem population_some (edges : E ≃ Fin ne) (e : E) :
    populationEquiv edges (some e) = (edges e).castSucc := by
  simp [populationEquiv]

@[simp] theorem population_none (edges : E ≃ Fin ne) :
    populationEquiv edges none = Fin.last ne := by
  simp [populationEquiv]

@[simp] theorem age_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (v : V) :
    (bankEquiv vertices edges hybrids (.inl v)).val = (vertices v).val := by
  simp [bankEquiv]

@[simp] theorem edge_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (e : E) :
    (bankEquiv vertices edges hybrids (.inr (.inl (some e)))).val =
      nv + (edges e).val := by
  simp [bankEquiv, populationEquiv]

@[simp] theorem ancestral_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) :
    (bankEquiv vertices edges hybrids (.inr (.inl none))).val = nv + ne := by
  simp [bankEquiv, populationEquiv]

@[simp] theorem hybrid_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (h : H) :
    (bankEquiv vertices edges hybrids (.inr (.inr h))).val =
      nv + ne + 1 + (hybrids h).val := by
  simp [bankEquiv, Nat.add_assoc]

/-- No edge or hybrid coordinate can alias the one ancestral slot. -/
theorem ancestral_fiber (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (q : V ⊕ (Option E ⊕ H)) :
    (bankEquiv vertices edges hybrids q).val = nv + ne ↔ q = .inr (.inl none) := by
  constructor
  · intro h
    apply (bankEquiv vertices edges hybrids).injective
    apply Fin.ext
    simpa only [ancestral_index] using h
  · rintro rfl
    exact ancestral_index vertices edges hybrids

/-- Universal coordinate contract, including empty carriers when supplied. -/
theorem ordered_bank_positions (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) :
    (∀ v, (bankEquiv vertices edges hybrids (.inl v)).val = (vertices v).val) ∧
    (∀ e, (bankEquiv vertices edges hybrids (.inr (.inl (some e)))).val =
      nv + (edges e).val) ∧
    (bankEquiv vertices edges hybrids (.inr (.inl none))).val = nv + ne ∧
    (∀ h, (bankEquiv vertices edges hybrids (.inr (.inr h))).val =
      nv + ne + 1 + (hybrids h).val) ∧
    (∀ q, (bankEquiv vertices edges hybrids q).val = nv + ne ↔
      q = .inr (.inl none)) := by
  exact ⟨age_index vertices edges hybrids, edge_index vertices edges hybrids,
    ancestral_index vertices edges hybrids, hybrid_index vertices edges hybrids,
    ancestral_fiber vertices edges hybrids⟩

end Astra.NativeOrderedBankLayout


/-!
Source-only use-site of the checked generic index layout.

This file has not been elaborated in the complete native import context.
It reuses the original finite-code decoder and registry, preserving its
explicit BinaryValid/RegistryValid premises and original parent bits.
-/
namespace Astra.OriginalCodeBankLayout

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting

variable {X ID : Type*} [Fintype X] [Fintype ID]
variable [DecidableEq X] [DecidableEq ID] {nh : ℕ}

/-- The supplied ID order must be the native ORIGINAL hybrid occurrence order. -/
noncomputable def layout (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (idOrder : ID ≃ Fin nh) :
    (NV (X := X) (ID := ID) ⊕
      (Option (NE (X := X) (ID := ID)) ⊕ Hybrid (sourceOfValid c hb))) ≃
      Fin (vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) + 1 + nh) :=
  Astra.NativeOrderedBankLayout.bankEquiv
    (Equiv.refl (NV (X := X) (ID := ID)))
    (Equiv.refl (NE (X := X) (ID := ID)))
    ((decodedIDs c hb hr).symm.trans idOrder)

theorem age_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (v : NV (X := X) (ID := ID)) :
    (layout c hb hr idOrder (.inl v)).val = v.val := by
  simp [layout]

theorem edge_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (e : NE (X := X) (ID := ID)) :
    (layout c hb hr idOrder (.inr (.inl (some e)))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) + e.val := by
  simp [layout]

theorem ancestral_position (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (idOrder : ID ≃ Fin nh) :
    (layout c hb hr idOrder (.inr (.inl none))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) := by
  simp [layout]

theorem hybrid_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (i : ID) :
    (layout c hb hr idOrder (.inr (.inr (decodedIDs c hb hr i)))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) + 1 + (idOrder i).val := by
  simp [layout]

/-- Reuse the exact existing original-parent occurrence theorem. -/
theorem parent_occurrence (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (i : ID) (b : Bool) :
    ((decodedRegistry c hb hr).parents (decodedIDs c hb hr i)).parent b =
      codeParent c i b :=
  decoded_parent_exact c hb hr i b

end Astra.OriginalCodeBankLayout


/-!
Use the EXISTING finite Code/decoder/registry directly for the existing CHART
value records. This supplies no byte-parser/native validator refinement or
new graph/admission factory. BinaryValid/RegistryValid remain real premises.
All original edges and parent occurrences retain their literal Fin positions.
-/
namespace Astra.OriginalCodeChartReflection

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.NaturalCellOrderedCompiler UnifiedLean.G6.WireAffineRefinement
open Astra.NativeCellFormReflection Astra.NativeCellAggregateReflection

theorem mapped_ofFn_eq_range {A : Type*} {k : ℕ}
    (f : Fin k → A) (g : A → ℕ) (h : ∀ i, g (f i) = i.val) :
    (List.ofFn f).map g = List.range k := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_ofFn, List.getElem_range, h]

theorem zipIdx_ofFn_pairs {A : Type*} {k : ℕ} (f : Fin k → A) :
    (List.ofFn f).zipIdx = List.ofFn (fun i => (f i, i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
variable {nt nh nc ni : ℕ}

def edgeOrder (c : Code X ID) : List (NE (X:=X) (ID:=ID)) := List.ofFn id

def leafOrder (taxonOrder : X ≃ Fin nt) : List X := List.ofFn taxonOrder.symm

def populationOrder (c : Code X ID) : List (Option (NE (X:=X) (ID:=ID))) :=
  (edgeOrder c).map some ++ [none]

noncomputable def hybridOrder (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) : List (Hybrid (sourceOfValid c hb)) :=
  List.ofFn (fun i => decodedIDs c hb hr (idOrder.symm i))

def sourceOfCode (c : Code X ID) (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh) :
    GParity.Chart.Source where
  vertices := vertexCount (Fintype.card X) (Fintype.card ID)
  root := (codeRoot c).val
  edges := List.ofFn (fun e : NE (X:=X) (ID:=ID) =>
    ⟨((codeGraph c).source e).val, ((codeGraph c).target e).val⟩)
  leaves := List.ofFn (fun i => (codeLeaf c (taxonOrder.symm i)).val)
  hybrids := List.ofFn (fun i => ⟨(codeSite c (idOrder.symm i)).val,
    (codeParent c (idOrder.symm i) false).val,
    (codeParent c (idOrder.symm i) true).val⟩)

noncomputable def inputOfCode (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh)
    (chronology : Fin nc → AgeConstraint (NV (X:=X) (ID:=ID)))
    (exposures : Fin ni → Exposure (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)))
    (coins : Hybrid (sourceOfValid c hb) → RationalInterval) (cap : ℕ) :
    GParity.Chart.Input where
  source := sourceOfCode c taxonOrder idOrder
  chronology := List.ofFn (fun i => reflectChronology Fin.val (chronology i))
  exposures := List.ofFn (fun i => reflectExposure Fin.val Fin.val (exposures i))
  coins := List.ofFn (fun i => encodeInterval (coins (decodedIDs c hb hr (idOrder.symm i))))
  cap := cap

theorem edge_values (c : Code X ID) :
    (edgeOrder c).map Fin.val = List.range (edgeCount (Fintype.card X) (Fintype.card ID)) :=
  mapped_ofFn_eq_range id Fin.val (by intro i; rfl)

variable (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
variable (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh)
variable (chronology : Fin nc → AgeConstraint (NV (X:=X) (ID:=ID)))
variable (exposures : Fin ni → Exposure (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)))
variable (coins : Hybrid (sourceOfValid c hb) → RationalInterval) (cap : ℕ)

/-- Every relation is constructed from the literal Code and exact occurrence
orders, rather than supplied as a claimed emitted-matrix equality. -/
noncomputable def fieldReflection :
    FieldReflection (sourceOfValid c hb) (Astra.OriginalCodeBankLayout.layout c hb hr idOrder)
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)
      (edgeOrder c) (leafOrder taxonOrder) (populationOrder c)
      (hybridOrder c hb hr idOrder) (List.ofFn id) (List.ofFn id)
      chronology exposures coins where
  vertex := Fin.val
  edge := Fin.val
  hybrid := fun h => (idOrder ((decodedIDs c hb hr).symm h)).val
  dimension := by simp [inputOfCode, sourceOfCode, GParity.Chart.Source.dimension]
  age_position v := Astra.OriginalCodeBankLayout.age_position c hb hr idOrder v
  inverse_position e := by
    cases e with
    | none => simp [inputOfCode, sourceOfCode, Astra.OriginalCodeBankLayout.ancestral_position]
    | some e => simp [inputOfCode, sourceOfCode, Astra.OriginalCodeBankLayout.edge_position]
  coin_position h := by
    have p := Astra.OriginalCodeBankLayout.hybrid_position c hb hr idOrder
      ((decodedIDs c hb hr).symm h)
    simpa [inputOfCode, sourceOfCode] using p
  edge_fields := by
    apply List.ext_getElem
    · simp [inputOfCode, sourceOfCode, edgeOrder]
    · intro i hi hj
      simp [inputOfCode, sourceOfCode, edgeOrder, sourceOfValid, codeGraph]
  leaf_fields := by
    apply List.ext_getElem
    · simp [inputOfCode, sourceOfCode, leafOrder]
    · intro i hi hj
      simp [inputOfCode, sourceOfCode, leafOrder, sourceOfValid]
  population_order := by
    simpa [inputOfCode, sourceOfCode, populationOrder, List.map_map,
      Function.comp_def, edge_values]
      using (List.range_succ (n := edgeCount (Fintype.card X) (Fintype.card ID)))
  hybrid_order := by
    simp only [inputOfCode, sourceOfCode, List.length_ofFn]
    symm
    exact mapped_ofFn_eq_range _ _ (by intro i; simp)
  chronology_fields := by simp [inputOfCode, List.map_ofFn]
  exposure_fields := by simp [inputOfCode, List.map_ofFn]
  coin_fields := by
    simp [inputOfCode, hybridOrder, zipIdx_ofFn_pairs, List.map_ofFn, Function.comp_def]

theorem edgeOrder_complete : ∀ e, e ∈ edgeOrder c := by
  intro e
  exact List.mem_ofFn.mpr ⟨e,rfl⟩

theorem leafOrder_complete : ∀ x, x ∈ leafOrder taxonOrder := by
  intro x
  exact List.mem_ofFn.mpr ⟨taxonOrder x, by simp⟩

theorem populationOrder_complete : ∀ e, e ∈ populationOrder c := by
  intro e
  cases e with
  | none => simp [populationOrder]
  | some e =>
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨e, edgeOrder_complete c e, rfl⟩

theorem hybridOrder_complete : ∀ h, h ∈ hybridOrder c hb hr idOrder := by
  intro h
  exact List.mem_ofFn.mpr ⟨idOrder ((decodedIDs c hb hr).symm h), by simp⟩

theorem decoded_emitRows_of_code :
    decodeRows _ (GParity.Chart.emitRows
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)) =
      compileCellList (sourceOfValid c hb) (Astra.OriginalCodeBankLayout.layout c hb hr idOrder)
        (edgeOrder c) (leafOrder taxonOrder) (populationOrder c) (hybridOrder c hb hr idOrder)
        (List.ofFn id) (List.ofFn id) chronology exposures coins :=
  decoded_emitRows_eq_compileCellList (fieldReflection c hb hr taxonOrder idOrder
    chronology exposures coins cap)

theorem coefficient_lengths_of_code :
    RowsWellFormed (vertexCount (Fintype.card X) (Fintype.card ID) +
      edgeCount (Fintype.card X) (Fintype.card ID) + 1 + nh) (GParity.Chart.emitRows
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)) :=
  emitted_coefficient_lengths (fieldReflection c hb hr taxonOrder idOrder
    chronology exposures coins cap)

theorem decoded_emitRows_toFinset_of_code :
    (decodeRows _ (GParity.Chart.emitRows
      (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap))).toFinset =
      compileCell (sourceOfValid c hb) (Astra.OriginalCodeBankLayout.layout c hb hr idOrder)
        chronology exposures coins := by
  apply decoded_emitRows_toFinset (fieldReflection c hb hr taxonOrder idOrder
    chronology exposures coins cap)
  · exact edgeOrder_complete c
  · exact leafOrder_complete taxonOrder
  · exact populationOrder_complete c
  · exact hybridOrder_complete c hb hr idOrder
  · intro i; exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · intro i; exact List.mem_ofFn.mpr ⟨i,rfl⟩

end Astra.OriginalCodeChartReflection

namespace GProgram.G5
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
structure Calendar (G : EdgeGraph V E) where
  age : V → ℝ
  edge_older : ∀ e, age (G.target e) < age (G.source e)


end GProgram.G5

namespace UnifiedLean.Source.NativePairClockLaw
variable {E : Type*}
structure PositivePairRates (E : Type*) where
  edge : E → ℝ
  edge_pos : ∀ e, 0 < edge e
  ancestral : ℝ
  ancestral_pos : 0 < ancestral

noncomputable def pairRate (r : PositivePairRates E) : Option E → ℝ
  | none => r.ancestral
  | some e => r.edge e

lemma pairRate_pos (r : PositivePairRates E) (e : Option E) : 0 < pairRate r e := by
  cases e with
  | none => exact r.ancestral_pos
  | some e => exact r.edge_pos e


end UnifiedLean.Source.NativePairClockLaw

namespace UnifiedLean.Source.NativeIndependentPairMixture
open Nanuq.Source UnifiedLean.Source.NativeParentRouting
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
structure HybridProbabilities (N : RootedBinary V E X) where
  gamma : Hybrid N → ℝ
  positive : ∀ h, 0 < gamma h
  below_one : ∀ h, gamma h < 1


end UnifiedLean.Source.NativeIndependentPairMixture

namespace UnifiedLean.G6.NaturalCellInverseRates
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
theorem interval_div_iff (c : RationalInterval) (d u : ℝ) (hu : 0 < u) :
    c.contains (d / u) ↔ c.scaled d u := by
  unfold RationalInterval.contains RationalInterval.scaled
  constructor
  · rintro ⟨hl, hh⟩
    constructor
    · intro b hb
      have h := hl b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (le_div_iff₀ hu).mp h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (lt_div_iff₀ hu).mp h
    · intro b hb
      have h := hh b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (div_le_iff₀ hu).mp h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (div_lt_iff₀ hu).mp h
  · rintro ⟨hl, hh⟩
    constructor
    · intro b hb
      have h := hl b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (le_div_iff₀ hu).mpr h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (lt_div_iff₀ hu).mpr h
    · intro b hb
      have h := hh b hb
      cases hstrict : b.strict with
      | false =>
          simp only [hstrict, Bool.false_eq_true, if_false] at h ⊢
          exact (div_le_iff₀ hu).mpr h
      | true =>
          simp only [hstrict, if_true] at h ⊢
          exact (div_lt_iff₀ hu).mpr h

theorem interval_rate_iff (c : RationalInterval) (rho d : ℝ) (hr : 0 < rho) :
    c.contains (rho * d) ↔ c.scaled d rho⁻¹ := by
  have he : rho * d = d / rho⁻¹ := by simp only [div_inv_eq_mul, mul_comm]
  rw [he]
  exact interval_div_iff c d rho⁻¹ (inv_pos.mpr hr)

variable {V E X I : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Source graph and original IDs are unchanged. none is the SAME ancestral
population used by every finite post-root exposure. -/
noncomputable def inverseBank (r : PositivePairRates E) : Option E → ℝ :=
  fun e => (pairRate r e)⁻¹

theorem inverse_bank_pos (r : PositivePairRates E) (e : Option E) :
    0 < inverseBank r e := inv_pos.mpr (pairRate_pos r e)

noncomputable def ratesOfInverse (u : Option E → ℝ) (hu : ∀ e, 0 < u e) :
    PositivePairRates E where
  edge e := (u (some e))⁻¹
  edge_pos e := inv_pos.mpr (hu (some e))
  ancestral := (u none)⁻¹
  ancestral_pos := inv_pos.mpr (hu none)

theorem constructed_pair_rate (u : Option E → ℝ) (hu : ∀ e, 0 < u e)
    (e : Option E) : pairRate (ratesOfInverse u hu) e = (u e)⁻¹ := by
  cases e <;> rfl

theorem reconstructed_inverse_bank (u : Option E → ℝ) (hu : ∀ e, 0 < u e) :
    inverseBank (ratesOfInverse u hu) = u := by
  funext e
  simp only [inverseBank, constructed_pair_rate, inv_inv]

theorem all_hazard_cells_iff (rows : I → Exposure V E) (a : V → ℝ)
    (r : PositivePairRates E) :
    (∀ i, (rows i).cell.contains (pairRate r (rows i).population * (rows i).duration a)) ↔
      (∀ i, (rows i).cell.scaled ((rows i).duration a)
        (inverseBank r (rows i).population)) := by
  constructor
  · intro h i
    exact (interval_rate_iff (rows i).cell _ _ (pairRate_pos r _)).mp (h i)
  · intro h i
    exact (interval_rate_iff (rows i).cell _ _ (pairRate_pos r _)).mpr (h i)

/-- Construct an ACTUAL original Calendar directly from its linear edge-age
constraints. No physically altered graph or suppressed demographic node. -/
def calendarOfAges (N : RootedBinary V E X) (a : V → ℝ)
    (ha : ∀ e, a (N.graph.target e) < a (N.graph.source e)) : Calendar N.graph :=
  ⟨a, ha⟩

/-- The original shared inheritance carrier is built from its strict linear
bounds; COMMON/INDEPENDENT observation kernels remain separately defined. -/
def inheritanceOfValues (N : RootedBinary V E X) (g : Hybrid N → ℝ)
    (hg0 : ∀ h, 0 < g h) (hg1 : ∀ h, g h < 1) : HybridProbabilities N :=
  ⟨g, hg0, hg1⟩

/-- Back-substitution into the genuine original positive rate bank satisfies
all original cells simultaneously. This supplies no desired observation law. -/
theorem reconstructed_bank_satisfies (rows : I → Exposure V E) (a : V → ℝ)
    (u : Option E → ℝ) (hu : ∀ e, 0 < u e)
    (hc : ∀ i, (rows i).cell.scaled ((rows i).duration a) (u (rows i).population)) :
    ∀ i, (rows i).cell.contains
      (pairRate (ratesOfInverse u hu) (rows i).population * (rows i).duration a) := by
  apply (all_hazard_cells_iff rows a (ratesOfInverse u hu)).mpr
  rw [reconstructed_inverse_bank]
  exact hc

def originalCellFeasible (N : RootedBinary V E X)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Prop :=
  ∃ (c : Calendar N.graph) (r : PositivePairRates E) (g : HybridProbabilities N),
    (∀ x, c.age (N.leaf x) = 0) ∧
    (∀ j, (chronology j).holds c.age) ∧
    (∀ h, (coins h).contains (g.gamma h)) ∧
    (∀ i, (rows i).cell.contains
      (pairRate r (rows i).population * (rows i).duration c.age))

/-- An explicit rational-affine system: all coefficients in age comparisons,
exposure bounds and gamma cells are rational constants. u has one coordinate
per original edge and ONE ancestral coordinate. -/
def inverseCellFeasible (N : RootedBinary V E X)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) : Prop :=
  ∃ (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ),
    (∀ e, a (N.graph.target e) < a (N.graph.source e)) ∧
    (∀ x, a (N.leaf x) = 0) ∧
    (∀ e, 0 < u e) ∧
    (∀ h, 0 < g h) ∧ (∀ h, g h < 1) ∧
    (∀ j, (chronology j).holds a) ∧
    (∀ h, (coins h).contains (g h)) ∧
    (∀ i, (rows i).cell.scaled ((rows i).duration a) (u (rows i).population))

/-- Exact simultaneous source-to-cell equivalence. No approximation,
feasibility oracle, source-image equality or source witness is assumed. -/
theorem original_cell_iff_inverse (N : RootedBinary V E X)
    (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) :
    originalCellFeasible N chronology rows coins ↔
      inverseCellFeasible N chronology rows coins := by
  constructor
  · rintro ⟨c, r, g, htip, horder, hcoins, hrows⟩
    exact ⟨c.age, inverseBank r, g.gamma, c.edge_older, htip,
      inverse_bank_pos r, g.positive, g.below_one, horder, hcoins,
      (all_hazard_cells_iff rows c.age r).mp hrows⟩
  · rintro ⟨a, u, g, hedge, htip, hu, hg0, hg1, horder, hcoins, hrows⟩
    exact ⟨calendarOfAges N a hedge, ratesOfInverse u hu,
      inheritanceOfValues N g hg0 hg1, htip, horder, hcoins,
      reconstructed_bank_satisfies rows a u hu hrows⟩


end UnifiedLean.G6.NaturalCellInverseRates

namespace UnifiedLean.G6.NaturalCellAffineCompiler
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.NaturalCellInverseRates
variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)
@[simp] theorem ageForm_eval (atom : AgeAtom V) (x : Fin n → ℝ) :
    (ageForm N layout atom).eval x = atom.eval (agesOf N layout x) := by
  cases atom <;> simp [ageForm, AgeAtom.eval, agesOf]
@[simp] theorem inverseForm_eval (e : Option E) (x : Fin n → ℝ) :
    (inverseForm N layout e).eval x = inverseRatesOf N layout x e := by
  simp [inverseForm, inverseRatesOf]
@[simp] theorem coinForm_eval (h : Hybrid N) (x : Fin n → ℝ) :
    (coinForm N layout h).eval x = coinsOf N layout x h := by
  simp [coinForm, coinsOf]
@[simp] theorem durationForm_eval (e : Exposure V E) (x : Fin n → ℝ) :
    (durationForm N layout e).eval x = e.duration (agesOf N layout x) := by
  simp [durationForm, Exposure.duration]

@[simp] theorem chronologyRows_holds (c : AgeConstraint V) (x : Fin n → ℝ) :
    (∀ r ∈ chronologyRows N layout c, r.Holds x) ↔ c.holds (agesOf N layout x) := by
  simp [chronologyRows, AgeConstraint.holds]

lemma scaled_one_iff (c : RationalInterval) (g : ℝ) : c.scaled g 1 ↔ c.contains g := by
  simp [RationalInterval.scaled, RationalInterval.contains]

def BankConditions (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval)
    (a : V → ℝ) (u : Option E → ℝ) (g : Hybrid N → ℝ) : Prop :=
    (∀ e, a (N.graph.target e) < a (N.graph.source e)) ∧
    (∀ x, a (N.leaf x) = 0) ∧
    (∀ e, 0 < u e) ∧
    (∀ h, 0 < g h) ∧ (∀ h, g h < 1) ∧
    (∀ j, (chronology j).holds a) ∧
    (∀ h, (coins h).contains (g h)) ∧
    (∀ i, (rows i).cell.scaled ((rows i).duration a) (u (rows i).population))

@[simp] theorem forall_univ_biUnion {A B : Type*} [Fintype A]
    [DecidableEq B] (f : A → Finset B) (P : B → Prop) :
    (∀ r ∈ Finset.univ.biUnion f, P r) ↔ ∀ i, ∀ r ∈ f i, P r := by
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index]
  exact forall_comm

/-- Every compiled row is equivalent to its source constraint, jointly on one
bank. This is a theorem about the actual emitted finite matrix, not a provider
field asserting source-completeness. -/
theorem compileCell_correct (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (x : Fin n → ℝ) :
    (∀ r ∈ compileCell N layout chronology rows coins, r.Holds x) ↔
    BankConditions N chronology rows coins (agesOf N layout x)
      (inverseRatesOf N layout x) (coinsOf N layout x) := by
  simp only [compileCell, Finset.forall_mem_union, forall_univ_biUnion,
    comparisonRows_holds, chronologyRows_holds, scaledRows_holds,
    Affine.eval_const, ageForm_eval, inverseForm_eval, coinForm_eval,
    durationForm_eval, AgeAtom.eval, AgeComparison.holds,
    Rat.cast_zero, Rat.cast_one, scaled_one_iff, BankConditions]
  tauto

/-- Existence of an original inverse bank is exactly finite matrix feasibility.
The proof explicitly encodes and decodes the one shared bank through layout. -/
theorem inverse_cell_iff_compiled (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) :
    inverseCellFeasible N chronology rows coins ↔
      Feasible ℝ (compileCell N layout chronology rows coins) := by
  constructor
  · rintro ⟨a,u,g,h⟩
    refine ⟨bankVector N layout a u g, (compileCell_correct N layout chronology rows coins _).mpr ?_⟩
    simpa only [agesOf_bankVector, inverseRatesOf_bankVector, coinsOf_bankVector,
      BankConditions] using h
  · rintro ⟨x,hx⟩
    refine ⟨agesOf N layout x, inverseRatesOf N layout x, coinsOf N layout x, ?_⟩
    exact (compileCell_correct N layout chronology rows coins x).mp hx


end UnifiedLean.G6.NaturalCellAffineCompiler


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

namespace UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.RationalAffineWitness
open scoped BigOperators
theorem ofFn_decodeVector (n : ℕ) (x : List Rat) (hx : x.length = n) :
    List.ofFn (decodeVector n x) = x := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hix : i < x.length := by omega
    simp [List.getElem?_ofFn, hi, decodeVector, List.getElem?_eq_getElem hix]
  · have hix : x.length ≤ i := by omega
    simp [List.getElem?_ofFn, hi, List.getElem?_eq_none hix]

theorem zipWith_ofFn {n : ℕ} (a x : Fin n → Rat) :
    (List.ofFn a).zipWith (· * ·) (List.ofFn x) = List.ofFn (fun i => a i * x i) := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n <;>
    simp [List.getElem?_zipWith, List.getElem?_ofFn, hi]

theorem dot_ofFn {n : ℕ} (a x : Fin n → Rat) :
    GParity.Rational.dot (List.ofFn a) (List.ofFn x) = ∑ i, a i * x i := by
  rw [GParity.Rational.dot, zipWith_ofFn, ← List.sum_eq_foldl, List.sum_ofFn]

theorem decodeRow_eval (n : ℕ) (r : GParity.Affine.Row) (x : List Rat)
    (hr : r.coeff.length = n) (hx : x.length = n) :
    (decodeRow n r).eval (decodeVector n x) = r.eval x := by
  change (∑ i, (decodeVector n r.coeff i : ℚ) * decodeVector n x i) =
    GParity.Rational.dot r.coeff x
  calc
    _ = GParity.Rational.dot (List.ofFn (decodeVector n r.coeff))
        (List.ofFn (decodeVector n x)) := by
      simpa only [Rat.cast_id] using (dot_ofFn (decodeVector n r.coeff) (decodeVector n x)).symm
    _ = _ := by rw [ofFn_decodeVector n r.coeff hr, ofFn_decodeVector n x hx]

theorem decodeRow_holds (n : ℕ) (r : GParity.Affine.Row) (x : List Rat)
    (hr : r.coeff.length = n) (hx : x.length = n) :
    r.holds x = true ↔ (decodeRow n r).Holds (decodeVector n x) := by
  have he := decodeRow_eval n r x hr hx
  change r.holds x = true ↔ StrictAffineElimination.Rel r.strict
    ((decodeRow n r).eval (decodeVector n x)) r.bound
  rw [he]
  cases hs : r.strict <;>
    simp [GParity.Affine.Row.holds, StrictAffineElimination.Rel, hs]

/-- The runtime's positive-output checker has precisely the typed affine
meaning, including the exact returned dimension. -/
theorem checkWitness_correct (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (x : List Rat) :
    GParity.Affine.checkWitness n rows x = true ↔
      x.length = n ∧ ∀ r ∈ (decodeRows n rows).toFinset, r.Holds (decodeVector n x) := by
  have hshape : rows.all (fun r => r.coeff.length == n) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    exact hrows
  simp only [GParity.Affine.checkWitness, hshape, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq, List.all_eq_true]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    exact (decodeRow_holds n r x (hrows r hr) hx).mp (hs r hr)
  · rintro ⟨hx, hs⟩
    refine ⟨hx, ?_⟩
    intro r hr
    apply (decodeRow_holds n r x (hrows r hr) hx).mpr
    exact hs (decodeRow n r) (List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩))

/-- A checked wire certificate is a real witness for the inherited rows. -/
theorem checkedWireWitness_real (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (x : List Rat)
    (hx : GParity.Affine.checkWitness n rows x = true) :
    ∀ r ∈ (decodeRows n rows).toFinset,
      r.Holds (fun i => (decodeVector n x i : ℝ)) :=
  rationalWitness_real _ _ ((checkWitness_correct n rows hrows x).mp hx).2

theorem checkedWireWitness_feasible (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (x : List Rat)
    (hx : GParity.Affine.checkWitness n rows x = true) :
    Feasible ℝ (decodeRows n rows).toFinset :=
  ⟨fun i => (decodeVector n x i : ℝ), checkedWireWitness_real n rows hrows x hx⟩


end UnifiedLean.G6.WireAffineRefinement


/-!
# Exact original-row certificates for strict affine infeasibility

Contributor: Codex / lean_reuse, 10 October 2026.
This independently checks a nonnegative combination of the original rows.
Projection traces need not be trusted by a certificate consumer. A zero normal
with negative bound, or zero bound with a positively weighted strict premise,
excludes every real vector. The theorem concerns the supplied finite matrix;
source admission and complete source/chart coverage remain separate.
-/
namespace UnifiedLean.G6.AffineContradictionCertificate

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.RationalAffineWitness
open scoped BigOperators

def weightedBound {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : ℚ :=
  ∑ i, weights i * (rows i).bound

def weightedCoeff {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) (j : Fin n) : ℚ :=
  ∑ i, weights i * (rows i).coeff j

def StrictUsed {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : Prop :=
  ∃ i, 0 < weights i ∧ (rows i).strict = true

def Valid {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : Prop :=
  (∀ i, 0 ≤ weights i) ∧ (∀ j, weightedCoeff rows weights j = 0) ∧
    (weightedBound rows weights < 0 ∨
      (weightedBound rows weights = 0 ∧ StrictUsed rows weights))

instance validDecidable {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) :
    Decidable (Valid rows weights) := by
  unfold Valid StrictUsed
  infer_instance

def check {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) : Bool :=
  decide (Valid rows weights)

theorem check_correct {m n : ℕ} (rows : Fin m → Row n) (weights : Fin m → ℚ) :
    check rows weights = true ↔ Valid rows weights := by
  simp only [check, decide_eq_true_eq]

theorem weighted_eval_eq {m n : ℕ} (rows : Fin m → Row n)
    (weights : Fin m → ℚ) (x : Fin n → ℝ) :
    (∑ i, (weights i : ℝ) * (rows i).eval x) =
      ∑ j, (weightedCoeff rows weights j : ℝ) * x j := by
  simp only [Row.eval, Finset.mul_sum, weightedCoeff, rat_cast_sum,
    Rat.cast_mul, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Soundness for arbitrary real vectors, with strict rows handled without
a closure relaxation. This excludes weak infeasibility as well as strict
boundary conflicts such as `x < 0` together with `0 ≤ x`. -/
theorem valid_excludes_real {m n : ℕ} (rows : Fin m → Row n)
    (weights : Fin m → ℚ) (hv : Valid rows weights) :
    ¬ ∃ x : Fin n → ℝ, ∀ i, (rows i).Holds x := by
  rintro ⟨x, hx⟩
  obtain ⟨hw, hc, hb⟩ := hv
  have he : (∑ i, (weights i : ℝ) * (rows i).eval x) = 0 := by
    rw [weighted_eval_eq]
    simp only [hc, Rat.cast_zero, zero_mul, Finset.sum_const_zero]
  have hle : ∀ i, (weights i : ℝ) * (rows i).eval x ≤
      (weights i : ℝ) * ((rows i).bound : ℝ) := by
    intro i
    apply mul_le_mul_of_nonneg_left (rel_le (hx i))
    exact_mod_cast hw i
  have hbcast : (∑ i, (weights i : ℝ) * ((rows i).bound : ℝ)) =
      (weightedBound rows weights : ℝ) := by
    simp only [weightedBound, rat_cast_sum, Rat.cast_mul]
  rcases hb with hneg | ⟨hzero, i, hi, hstrict⟩
  · have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hle i)
    rw [he, hbcast] at hsum
    have hn : (weightedBound rows weights : ℝ) < 0 := by exact_mod_cast hneg
    linarith
  · have hrow : (rows i).eval x < ((rows i).bound : ℝ) := by
      simpa only [Row.Holds, StrictAffineElimination.Rel, hstrict, if_true] using hx i
    have hmul : (weights i : ℝ) * (rows i).eval x <
        (weights i : ℝ) * ((rows i).bound : ℝ) :=
      mul_lt_mul_of_pos_left hrow (by exact_mod_cast hi)
    have hsum := Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ _, hmul⟩
    rw [he, hbcast, hzero, Rat.cast_zero] at hsum
    exact (lt_irrefl (0 : ℝ)) hsum

theorem checked_excludes_real {m n : ℕ} (rows : Fin m → Row n)
    (weights : Fin m → ℚ) (h : check rows weights = true) :
    ¬ ∃ x : Fin n → ℝ, ∀ i, (rows i).Holds x :=
  valid_excludes_real rows weights ((check_correct rows weights).mp h)

#print axioms check_correct
#print axioms weighted_eval_eq
#print axioms valid_excludes_real
#print axioms checked_excludes_real

end UnifiedLean.G6.AffineContradictionCertificate


/-!
# Native contradiction checking refines the proved original-row certificate

Contributor: Codex / lean_reuse_recovery, 10 October 2026.
One multiplier per original row and exact coefficient lengths are explicit.
The proof checks the native list/fold/Boolean program, not a replacement
certificate predicate. No projection-cap completeness or source admission is
assumed: an accepted certificate excludes the supplied matrix only.
-/
namespace UnifiedLean.G6.WireContradictionRefinement

open UnifiedLean.G6.StrictAffineElimination
open UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.AffineContradictionCertificate
open scoped BigOperators

def indexedRows (n : ℕ) (rows : List GParity.Affine.Row) : Fin rows.length → Row n :=
  fun i => decodeRow n (rows.get i)

def indexedWeights (rows : List GParity.Affine.Row) (weights : List Rat) :
    Fin rows.length → ℚ := decodeVector rows.length weights

theorem zip_ofFn {α β : Type*} {m : ℕ} (a : Fin m → α) (b : Fin m → β) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i, b i)) := by
  rw [List.zip_eq_zipWith]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < m <;>
    simp [List.getElem?_zipWith, List.getElem?_ofFn, hi]

theorem zipRows_eq_ofFn (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) :
    rows.zip weights = List.ofFn (fun i : Fin rows.length =>
      (rows.get i, indexedWeights rows weights i)) := by
  calc
    rows.zip weights = (List.ofFn rows.get).zip
        (List.ofFn (decodeVector rows.length weights)) := by
      rw [List.ofFn_get, ofFn_decodeVector rows.length weights hw]
    _ = _ := zip_ofFn _ _

theorem foldl_ofFn_sum {α : Type*} {m : ℕ} (a : Fin m → α) (f : α → Rat) :
    (List.ofFn a).foldl (fun z x => z + f x) 0 = ∑ i, f (a i) := by
  calc
    _ = ((List.ofFn a).map f).foldl (· + ·) 0 := by rw [List.foldl_map]
    _ = (List.ofFn (fun i => f (a i))).sum := by
      rw [← List.sum_eq_foldl, List.map_ofFn]
      rfl
    _ = _ := by rw [List.sum_ofFn]

theorem weightedFold_eq (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) (f : GParity.Affine.Row → Rat) :
    (rows.zip weights).foldl (fun z rw => z + rw.2 * f rw.1) 0 =
      ∑ i, indexedWeights rows weights i * f (rows.get i) := by
  rw [zipRows_eq_ofFn rows weights hw]
  exact foldl_ofFn_sum _ _

theorem nativeBound_eq (n : ℕ) (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) :
    (rows.zip weights).foldl (fun z rw => z + rw.2 * rw.1.bound) 0 =
      weightedBound (indexedRows n rows) (indexedWeights rows weights) := by
  exact weightedFold_eq rows weights hw GParity.Affine.Row.bound

theorem nativeCoeff_eq (n : ℕ) (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) (j : Fin n) :
    (rows.zip weights).foldl (fun z rw => z + rw.2 * (rw.1.coeff[j.val]?.getD 0)) 0 =
      weightedCoeff (indexedRows n rows) (indexedWeights rows weights) j := by
  exact weightedFold_eq rows weights hw (fun r => r.coeff[j.val]?.getD 0)

theorem nativeNonnegative_iff (rows : List GParity.Affine.Row) (weights : List Rat)
    (hw : weights.length = rows.length) :
    weights.all (fun w => decide (0 ≤ w)) = true ↔
      ∀ i, 0 ≤ indexedWeights rows weights i := by
  have ha :
      (List.ofFn (decodeVector rows.length weights)).all (fun w => decide (0 ≤ w)) =
        weights.all (fun w => decide (0 ≤ w)) := by
    rw [ofFn_decodeVector rows.length weights hw]
  rw [← ha]
  simp only [List.all_eq_true, decide_eq_true_eq, List.forall_mem_ofFn_iff]
  rfl

theorem nativeStrictUsed_iff (n : ℕ) (rows : List GParity.Affine.Row)
    (weights : List Rat) (hw : weights.length = rows.length) :
    (rows.zip weights).any (fun rw => rw.1.strict && decide (0 < rw.2)) = true ↔
      StrictUsed (indexedRows n rows) (indexedWeights rows weights) := by
  rw [zipRows_eq_ofFn rows weights hw]
  simp only [List.any_eq_true, List.mem_ofFn, Bool.and_eq_true, decide_eq_true_eq,
    StrictUsed, indexedRows, decodeRow]
  constructor
  · rintro ⟨p, ⟨i, rfl⟩, hs, hi⟩
    exact ⟨i, hi, hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨(rows.get i, indexedWeights rows weights i), ⟨i, rfl⟩, hs, hi⟩

/-- With exact input dimensions, the actual native Boolean checker is exactly
the proved rational original-row certificate predicate. -/
theorem checkContradiction_correct (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (weights : List Rat)
    (hw : weights.length = rows.length) :
    GParity.Affine.checkContradiction n rows weights = true ↔
      Valid (indexedRows n rows) (indexedWeights rows weights) := by
  have hshape : rows.all (fun r => r.coeff.length == n) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    exact hrows
  have hzero :
      (List.range n).all (fun j =>
        (rows.zip weights).foldl (fun z rw => z + rw.2 * (rw.1.coeff[j]?.getD 0)) 0 == 0) = true ↔
        ∀ j, weightedCoeff (indexedRows n rows) (indexedWeights rows weights) j = 0 := by
    simp only [List.all_eq_true, beq_iff_eq, List.mem_range]
    constructor
    · intro h j
      rw [← nativeCoeff_eq n rows weights hw j]
      exact h j.val j.isLt
    · intro h j hj
      exact (nativeCoeff_eq n rows weights hw ⟨j, hj⟩).trans (h ⟨j, hj⟩)
  simp only [GParity.Affine.checkContradiction, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, hw, hshape, true_and, and_true, decide_eq_true_eq,
    nativeNonnegative_iff rows weights hw, hzero, nativeBound_eq n rows weights hw,
    nativeStrictUsed_iff n rows weights hw, Valid, and_assoc]

theorem indexedRows_holds_iff (n : ℕ) (rows : List GParity.Affine.Row)
    (x : Fin n → ℝ) :
    (∀ i, (indexedRows n rows i).Holds x) ↔
      ∀ r ∈ (decodeRows n rows).toFinset, r.Holds x := by
  constructor
  · intro h q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hr
    simpa only [indexedRows, hi] using h i
  · intro h i
    apply h
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨rows.get i, List.get_mem _ _, rfl⟩

/-- A successful native negative certificate excludes every real vector of
the supplied matrix. The runtime may still return UNKNOWN at a cap. -/
theorem checkedWireContradiction_excludes_real (n : ℕ) (rows : List GParity.Affine.Row)
    (hrows : RowsWellFormed n rows) (weights : List Rat)
    (hw : weights.length = rows.length)
    (h : GParity.Affine.checkContradiction n rows weights = true) :
    ¬ Feasible ℝ (decodeRows n rows).toFinset := by
  intro hf
  obtain ⟨x, hx⟩ := hf
  apply valid_excludes_real (indexedRows n rows) (indexedWeights rows weights)
    ((checkContradiction_correct n rows hrows weights hw).mp h)
  exact ⟨x, (indexedRows_holds_iff n rows x).mpr hx⟩

#print axioms zipRows_eq_ofFn
#print axioms weightedFold_eq
#print axioms checkContradiction_correct
#print axioms checkedWireContradiction_excludes_real

end UnifiedLean.G6.WireContradictionRefinement

namespace UnifiedLean.G6.RationalNaturalCellWitness
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.RationalAffineWitness
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
variable {V E X I C : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]
variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]
variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)
def checkOriginalCellWitness (chronology : C → AgeConstraint V) (rows : I → Exposure V E)
    (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ) : Bool :=
  checkRationalWitness (compileCell N layout chronology rows coins) q

/-- A successful exact rational certificate produces the actual jointly shared
bank, with every original-calendar constraint interpreted on that same vector. -/
theorem checkOriginalCellWitness_sound (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    BankConditions N chronology rows coins
      (agesOf N layout (fun i => (q i : ℝ)))
      (inverseRatesOf N layout (fun i => (q i : ℝ)))
      (coinsOf N layout (fun i => (q i : ℝ))) := by
  apply (compileCell_correct N layout chronology rows coins _).mp
  apply rationalWitness_real
  exact (checkRationalWitness_correct _ q).mp hq

structure OriginalCellBank (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) where
  calendar : Calendar N.graph
  rates : PositivePairRates E
  inheritance : HybridProbabilities N
  leaf_zero : ∀ x, calendar.age (N.leaf x) = 0
  chronology_holds : ∀ j, (chronology j).holds calendar.age
  coins_holds : ∀ h, (coins h).contains (inheritance.gamma h)
  exposures_hold : ∀ i, (rows i).cell.contains
    (pairRate rates (rows i).population * (rows i).duration calendar.age)

/-- No existence choice occurs in this realization: calendar ages and coins
are the returned coordinates; rates are their positive inverse reciprocals.
The real carrier realization is noncomputable, while the rational solver and
its finite certificate remain executable. -/
noncomputable def checkedOriginalCellBank (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    OriginalCellBank N chronology rows coins := by
  let h := checkOriginalCellWitness_sound N layout chronology rows coins q hq
  let hedge := h.1
  let htip := h.2.1
  let hu := h.2.2.1
  let hg0 := h.2.2.2.1
  let hg1 := h.2.2.2.2.1
  let hchron := h.2.2.2.2.2.1
  let hcoins := h.2.2.2.2.2.2.1
  let hrows := h.2.2.2.2.2.2.2
  refine ⟨calendarOfAges N (agesOf N layout (fun i => (q i : ℝ))) hedge,
    ratesOfInverse (inverseRatesOf N layout (fun i => (q i : ℝ))) hu,
    inheritanceOfValues N (coinsOf N layout (fun i => (q i : ℝ))) hg0 hg1,
    htip, hchron, hcoins, ?_⟩
  exact reconstructed_bank_satisfies rows _ _ hu hrows

theorem checkedOriginalCellBank_ages (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    (checkedOriginalCellBank N layout chronology rows coins q hq).calendar.age =
      agesOf N layout (fun i => (q i : ℝ)) := rfl

theorem checkedOriginalCellBank_rates (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true)
    (e : Option E) :
    pairRate (checkedOriginalCellBank N layout chronology rows coins q hq).rates e =
      (inverseRatesOf N layout (fun i => (q i : ℝ)) e)⁻¹ := by
  exact constructed_pair_rate (inverseRatesOf N layout (fun i => (q i : ℝ)))
    (checkOriginalCellWitness_sound N layout chronology rows coins q hq).2.2.1 e

theorem checkedOriginalCellBank_coins (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    (checkedOriginalCellBank N layout chronology rows coins q hq).inheritance.gamma =
      coinsOf N layout (fun i => (q i : ℝ)) := rfl

theorem checkedOriginalCellBank_feasible (chronology : C → AgeConstraint V)
    (rows : I → Exposure V E) (coins : Hybrid N → RationalInterval) (q : Fin n → ℚ)
    (hq : checkOriginalCellWitness N layout chronology rows coins q = true) :
    originalCellFeasible N chronology rows coins := by
  let b := checkedOriginalCellBank N layout chronology rows coins q hq
  exact ⟨b.calendar, b.rates, b.inheritance, b.leaf_zero,
    b.chronology_holds, b.coins_holds, b.exposures_hold⟩


end UnifiedLean.G6.RationalNaturalCellWitness


/-!
Compose the literal original Code/CHART field construction with the EXISTING
wire certificate and physical-bank receivers. No parser, native validator,
source observation, bounded-search completeness or all-source NO is asserted.
The external contradiction vector still has one entry per ORIGINAL wire row.
-/
namespace Astra.OriginalCodeChartReceiver

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.RationalAffineWitness
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.RationalNaturalCellWitness UnifiedLean.G6.WireAffineRefinement
open UnifiedLean.G6.WireContradictionRefinement
open Astra.OriginalCodeChartReflection

variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
variable {nt nh nc ni : ℕ}
variable (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
variable (taxonOrder : X ≃ Fin nt) (idOrder : ID ≃ Fin nh)
variable (chronology : Fin nc → AgeConstraint (NV (X:=X) (ID:=ID)))
variable (exposures : Fin ni → Exposure (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)))
variable (coins : Hybrid (sourceOfValid c hb) → RationalInterval) (cap : ℕ)

local notation "D" => vertexCount (Fintype.card X) (Fintype.card ID) +
  edgeCount (Fintype.card X) (Fintype.card ID) + 1 + nh
local notation "N" => sourceOfValid c hb
local notation "L" => Astra.OriginalCodeBankLayout.layout c hb hr idOrder
local notation "R" => GParity.Chart.emitRows
  (inputOfCode c hb hr taxonOrder idOrder chronology exposures coins cap)

theorem checked_original_witness (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) :
    checkOriginalCellWitness N L chronology exposures coins (decodeVector D x) = true := by
  apply (checkRationalWitness_correct _ _).mpr
  have h := ((checkWitness_correct D R
    (coefficient_lengths_of_code c hb hr taxonOrder idOrder chronology exposures coins cap)
    x).mp hx).2
  simpa only [decoded_emitRows_toFinset_of_code c hb hr taxonOrder idOrder
    chronology exposures coins cap] using h

/-- Ages and inheritance are the same returned coordinates; rates are their
positive reciprocals, using the existing original physical carriers. -/
noncomputable def checked_original_bank (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) :
    OriginalCellBank N chronology exposures coins :=
  checkedOriginalCellBank N L chronology exposures coins (decodeVector D x)
    (checked_original_witness c hb hr taxonOrder idOrder chronology exposures coins cap x hx)

theorem checked_original_bank_rates (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) (e : Option (NE (X:=X) (ID:=ID))) :
    pairRate (checked_original_bank c hb hr taxonOrder idOrder chronology exposures coins cap
      x hx).rates e = (inverseRatesOf N L (fun i => (decodeVector D x i : ℝ)) e)⁻¹ := by
  exact checkedOriginalCellBank_rates N L chronology exposures coins (decodeVector D x)
    (checked_original_witness c hb hr taxonOrder idOrder chronology exposures coins cap x hx) e

theorem checked_original_bank_feasible (x : List Rat)
    (hx : GParity.Affine.checkWitness D R x = true) :
    originalCellFeasible N chronology exposures coins :=
  checkedOriginalCellBank_feasible N L chronology exposures coins (decodeVector D x)
    (checked_original_witness c hb hr taxonOrder idOrder chronology exposures coins cap x hx)

/-- This excludes only the supplied original source CELL, with the complete
ordered external vector. It excludes no unenumerated source or chart. -/
theorem checked_original_exclusion (weights : List Rat)
    (hlen : weights.length = (R).length)
    (hx : GParity.Affine.checkContradiction D R weights = true) :
    ¬ originalCellFeasible N chronology exposures coins := by
  have hn := checkedWireContradiction_excludes_real D R
    (coefficient_lengths_of_code c hb hr taxonOrder idOrder chronology exposures coins cap)
    weights hlen hx
  intro ho
  apply hn
  rw [decoded_emitRows_toFinset_of_code c hb hr taxonOrder idOrder chronology exposures coins cap]
  exact (inverse_cell_iff_compiled N L chronology exposures coins).mp
    ((original_cell_iff_inverse N chronology exposures coins).mp ho)

end Astra.OriginalCodeChartReceiver

namespace GProgram.G7.OriginalAdmission
open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding
variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
def CutChild (c : Code X ID) : Prop :=
  ∀ f, (codeGraph c).IsHybrid ((codeGraph c).source f) → (codeGraph c).IsBridge f

end GProgram.G7.OriginalAdmission

namespace UnifiedLean.G6.TwoTipChartFixture
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
def graph : EdgeGraph (Fin 3) (Fin 2) :=
  ⟨fun _ => 0, fun e => e.succ⟩

def leaf : Fin 2 ↪ Fin 3 :=
  ⟨Fin.succ, by intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)⟩

theorem step_rank {a b : Fin 3} (h : graph.DStep a b) : a.val < b.val := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [graph]

theorem path_rank {a b : Fin 3} (h : Relation.TransGen graph.DStep a b) :
    a.val < b.val := by
  induction h with
  | single h => exact step_rank h
  | tail _ h ih => exact lt_trans ih (step_rank h)

theorem graph_acyclic : graph.Acyclic := by
  intro a ha
  exact (lt_irrefl _) (path_rank ha)

theorem graph_rooted : ∀ a, graph.DReach 0 a := by
  intro a
  fin_cases a
  · exact .refl
  · exact .single ⟨0, rfl, rfl⟩
  · exact .single ⟨1, rfl, rfl⟩

theorem graph_least_stable :
    ∀ a, (∀ x, graph.Dominates 0 a (leaf x)) → a = 0 := by
  intro a h
  fin_cases a
  · rfl
  · exact False.elim (h 1 ⟨by decide, by decide,
      .single ⟨⟨1, rfl, rfl⟩, by decide, by decide⟩⟩)
  · exact False.elim (h 0 ⟨by decide, by decide,
      .single ⟨⟨0, rfl, rfl⟩, by decide, by decide⟩⟩)

def source : RootedBinary (Fin 3) (Fin 2) (Fin 2) where
  graph := graph
  root := 0
  leaf := leaf
  at_least_two_taxa := by decide
  root_degrees := by decide
  leaf_degrees := by decide
  internal_degrees := by
    intro a hroot hleaf
    fin_cases a
    · exact False.elim (hroot rfl)
    · exact False.elim (hleaf 0 rfl)
    · exact False.elim (hleaf 1 rfl)
  acyclic := graph_acyclic
  rooted := graph_rooted
  least_stable := graph_least_stable

theorem noHybrid (h : Hybrid source) : False := by
  have hn : ∀ v : Fin 3, ¬ graph.IsHybrid v := by
    intro v
    unfold EdgeGraph.IsHybrid
    fin_cases v <;> decide
  exact hn h.val h.property


def nativeSource : GParity.Chart.Source :=
  ⟨3, 0, [⟨0, 1⟩, ⟨0, 2⟩], [1, 2], []⟩

def nativeInput : GParity.Chart.Input :=
  ⟨nativeSource, [], [], [], 4096⟩

theorem nativeSource_valid : nativeSource.valid = true := by decide


end UnifiedLean.G6.TwoTipChartFixture


/-!
One literal use-site of the existing Code decoder and physical receiver.
The projection prepends only the retained two-tip graph/source declarations
and literal wire source/input, omitting all five original evaluation commands.
No native process or byte-parser/source-origin relation is asserted.
-/
namespace Astra.TwoTipOriginalCodeReceiver

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler
open UnifiedLean.G6.RationalNaturalCellWitness UnifiedLean.G6.WireAffineRefinement
open Astra.OriginalCodeChartReflection Astra.OriginalCodeChartReceiver

abbrev retainedSource := UnifiedLean.G6.TwoTipChartFixture.source

/-- Expected fixture positions, without relying on `encode` numbering. -/
def code : Code (Fin 2) (Fin 0) :=
  (fun _ => ⟨0, by simp [vertexCount]⟩, fun e => e.succ,
    ⟨0, by simp [vertexCount]⟩, Fin.succ, Fin.elim0, Fin.elim0)

theorem binary_valid : BinaryValid code := by
  exact ⟨retainedSource.leaf.injective, retainedSource.at_least_two_taxa,
    retainedSource.root_degrees, retainedSource.leaf_degrees,
    retainedSource.internal_degrees, retainedSource.acyclic,
    retainedSource.rooted, retainedSource.least_stable⟩

theorem registry_valid : RegistryValid code := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro a ha
    exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid ⟨a, ha⟩)
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem cut_child : CutChild code := by
  intro e he
  exact False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid ⟨_, he⟩)

theorem decoded_source_eq : sourceOfValid code binary_valid = retainedSource := by
  rfl

def taxonOrder : Fin 2 ≃ Fin 2 := Equiv.refl _
def idOrder : Fin 0 ≃ Fin 0 := Equiv.refl _
def chronology : Fin 0 → AgeConstraint (Fin 3) := Fin.elim0
def exposures : Fin 0 → Exposure (Fin 3) (Fin 2) := Fin.elim0
def coins : Hybrid (sourceOfValid code binary_valid) → RationalInterval :=
  fun h => False.elim (UnifiedLean.G6.TwoTipChartFixture.noHybrid h)

theorem source_fields_exact :
    sourceOfCode code taxonOrder idOrder = UnifiedLean.G6.TwoTipChartFixture.nativeSource := by
  rfl

theorem input_fields_exact :
    inputOfCode code binary_valid registry_valid taxonOrder idOrder
      chronology exposures coins 4096 = UnifiedLean.G6.TwoTipChartFixture.nativeInput := by
  rfl

theorem original_rows_exact :
    (decodeRows 6 (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput)).toFinset =
      compileCell (sourceOfValid code binary_valid)
        (Astra.OriginalCodeBankLayout.layout code binary_valid registry_valid idOrder)
        chronology exposures coins := by
  rw [← input_fields_exact]
  exact decoded_emitRows_toFinset_of_code code binary_valid registry_valid taxonOrder idOrder
    chronology exposures coins 4096

theorem supplied_witness_checked (x : List Rat)
    (hx : GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput) x = true) :
    GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows (inputOfCode code binary_valid registry_valid taxonOrder idOrder
        chronology exposures coins 4096)) x = true := by
  rw [input_fields_exact]
  exact hx

noncomputable def bank (x : List Rat)
    (hx : GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput) x = true) :
    OriginalCellBank (sourceOfValid code binary_valid)
    chronology exposures coins :=
  checked_original_bank code binary_valid registry_valid taxonOrder idOrder
    chronology exposures coins 4096 x (supplied_witness_checked x hx)

theorem original_cell_feasible (x : List Rat)
    (hx : GParity.Affine.checkWitness 6
      (GParity.Chart.emitRows UnifiedLean.G6.TwoTipChartFixture.nativeInput) x = true) :
    originalCellFeasible (sourceOfValid code binary_valid) chronology exposures coins :=
  checked_original_bank_feasible code binary_valid registry_valid taxonOrder idOrder
    chronology exposures coins 4096 x (supplied_witness_checked x hx)

end Astra.TwoTipOriginalCodeReceiver
