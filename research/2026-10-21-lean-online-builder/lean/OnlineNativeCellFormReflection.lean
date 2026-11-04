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
