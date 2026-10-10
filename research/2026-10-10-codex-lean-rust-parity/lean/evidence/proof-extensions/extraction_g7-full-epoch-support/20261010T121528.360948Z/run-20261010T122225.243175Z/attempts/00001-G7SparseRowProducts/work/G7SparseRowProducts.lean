import G7PopulationSelectedSupport

/-!
# Finite literal-row products and exact selected polynomial pushforwards

Contributor: Codex / lean_reuse_successor, 2026-10-10.
This algebraic bridge groups complete literal destination fibres. It requires
an explicit equality between the literal constructor's projected key and the
inherited selected-key join; no arbitrary destination representative is chosen.
The executable functions enumerate only the supplied lists. Fresh kernel
checking and complete audit remain required.
-/
namespace GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.PopulationSelectedSupport
open scoped BigOperators

abbrev Rows (I A : Type*) := List (A × Sparse I)

def readRows {I A K : Type*} [DecidableEq K] (key : A → K)
    (rows : Rows I A) (target : K) : Sparse I :=
  rows.flatMap fun row => if key row.1 = target then row.2 else []

def multiplyRows {I A B C : Type*} (join : A → B → C)
    (left : Rows I A) (right : Rows I B) : Rows I C :=
  left.flatMap fun a => right.map fun b => (join a.1 b.1, product a.2 b.2)

lemma readRows_append {I A K : Type*} [DecidableEq K] (key : A → K)
    (left right : Rows I A) (target : K) :
    readRows key (left ++ right) target =
      readRows key left target ++ readRows key right target := by
  simp only [readRows,List.flatMap_append]

lemma readRows_map {I A B K : Type*} [DecidableEq K] (key : B → K)
    (rows : List A) (f : A → B × Sparse I) (target : K) :
    readRows key (rows.map f) target =
      rows.flatMap (fun a => if key (f a).1 = target then (f a).2 else []) := by
  simp only [readRows,List.flatMap_map]

lemma polynomial_cons {I : Type*} (z : List (I × Nat) × ℚ) (p : Sparse I) :
    polynomial (z :: p) = MvPolynomial.C z.2 *
      (z.1.map fun a => MvPolynomial.X a.1 ^ a.2).prod + polynomial p := rfl

lemma polynomial_product_row {I : Type*} (z : List (I × Nat) × ℚ) (b : Sparse I) :
    polynomial (b.map fun y => (z.1 ++ y.1,z.2*y.2)) =
      MvPolynomial.C z.2 * (z.1.map fun a => MvPolynomial.X a.1 ^ a.2).prod *
        polynomial b := by
  induction b with
  | nil => simp [polynomial]
  | cons y b ih =>
      simp only [List.map_cons,polynomial_cons,List.map_append,List.prod_append,
        MvPolynomial.C_mul]
      rw [ih]
      ring

lemma polynomial_product {I : Type*} (a b : Sparse I) :
    polynomial (product a b) = polynomial a * polynomial b := by
  induction a with
  | nil => simp [product,polynomial]
  | cons z a ih =>
      change polynomial ((b.map fun y => (z.1 ++ y.1,z.2*y.2)) ++ product a b) = _
      rw [polynomial_append,polynomial_product_row,ih,polynomial_cons,add_mul]

lemma polynomial_readRows {I A K : Type*} [DecidableEq K] (key : A → K)
    (rows : Rows I A) (target : K) :
    polynomial (readRows key rows target) =
      (rows.map fun row => if key row.1 = target then polynomial row.2 else 0).sum := by
  rw [readRows,polynomial_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro row _
  by_cases h : key row.1 = target
  · rw [if_pos h,if_pos h]
  · rw [if_neg h,if_neg h]
    rfl

lemma list_mul_sum {A M : Type*} [Semiring M] (l : List A) (q : M) (f : A → M) :
    (l.map fun a => q * f a).sum = q * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

/-- Repeated literal keys contribute their sum, including zero rows. -/
lemma sum_partition {A K M : Type*} [Fintype K] [DecidableEq K] [Semiring M]
    (l : List A) (key : A → K) (weight : A → M) (g : K → M) :
    (l.map fun a => weight a * g (key a)).sum =
      ∑ k : K, (l.map fun a => if key a = k then weight a else 0).sum * g k := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib]
      rw [ih]
      congr 1
      simp [ite_mul,eq_comm]

lemma sum_partition_two {A B KA KB M : Type*}
    [Fintype KA] [DecidableEq KA] [Fintype KB] [DecidableEq KB] [Semiring M]
    (left : List A) (right : List B) (keyA : A → KA) (keyB : B → KB)
    (weightA : A → M) (weightB : B → M) (h : KA → KB → M) :
    (left.map fun a => weightA a *
      (right.map fun b => weightB b * h (keyA a) (keyB b)).sum).sum =
      ∑ ka : KA, ∑ kb : KB,
        (left.map fun a => if keyA a = ka then weightA a else 0).sum *
          (right.map fun b => if keyB b = kb then weightB b else 0).sum * h ka kb := by
  rw [sum_partition left keyA weightA]
  apply Finset.sum_congr rfl
  intro ka _
  rw [sum_partition right keyB weightB]
  simp only [Finset.mul_sum,mul_assoc]

lemma polynomial_read_multiplyRows {I A B C K : Type*} [DecidableEq K]
    (join : A → B → C) (key : C → K) (left : Rows I A) (right : Rows I B)
    (target : K) :
    polynomial (readRows key (multiplyRows join left right) target) =
      (left.map fun a => (right.map fun b =>
        if key (join a.1 b.1) = target then polynomial a.2 * polynomial b.2 else 0).sum).sum := by
  induction left with
  | nil => rfl
  | cons a left ih =>
      change polynomial (readRows key
        ((right.map fun b => (join a.1 b.1,product a.2 b.2)) ++
          multiplyRows join left right) target) = _
      rw [readRows_append,polynomial_append,ih]
      simp only [List.map_cons,List.sum_cons]
      congr 1
      rw [readRows_map,polynomial_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro b _
      by_cases h : key (join a.1 b.1) = target
      · rw [if_pos h,if_pos h,polynomial_product]
      · rw [if_neg h,if_neg h]
        rfl

/-- Exact finite-row pushforward identity for any literal join that refines the
inherited key join. This is the algebraic step needed by the whole source epoch.
Both sums include every literal row in each selected-key fibre. -/
theorem polynomial_read_multiplyRows_partition {I A B C KA KB K : Type*}
    [DecidableEq K] [Fintype KA] [DecidableEq KA] [Fintype KB] [DecidableEq KB]
    (join : A → B → C) (keyA : A → KA) (keyB : B → KB) (key : C → K)
    (joinKey : KA × KB → K)
    (hjoin : ∀ a b, key (join a b) = joinKey (keyA a,keyB b))
    (left : Rows I A) (right : Rows I B) (target : K) :
    polynomial (readRows key (multiplyRows join left right) target) =
      ∑ ab : KA × KB, if joinKey ab = target then
        polynomial (readRows keyA left ab.1) * polynomial (readRows keyB right ab.2) else 0 := by
  let delta : KA → KB → MvPolynomial I ℚ := fun ka kb =>
    if joinKey (ka,kb) = target then 1 else 0
  rw [polynomial_read_multiplyRows]
  calc
    (left.map fun a => (right.map fun b =>
      if key (join a.1 b.1) = target then polynomial a.2 * polynomial b.2 else 0).sum).sum =
        (left.map fun a => polynomial a.2 *
          (right.map fun b => polynomial b.2 * delta (keyA a.1) (keyB b.1)).sum).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro a _
      rw [← list_mul_sum]
      apply congrArg List.sum
      apply List.map_congr_left
      intro b _
      rw [hjoin]
      by_cases h : joinKey (keyA a.1,keyB b.1) = target <;> simp [delta,h]
    _ = ∑ ka : KA, ∑ kb : KB,
        (left.map fun a => if keyA a.1 = ka then polynomial a.2 else 0).sum *
          (right.map fun b => if keyB b.1 = kb then polynomial b.2 else 0).sum * delta ka kb :=
      sum_partition_two left right (fun a => keyA a.1) (fun b => keyB b.1)
        (fun a => polynomial a.2) (fun b => polynomial b.2) delta
    _ = ∑ ab : KA × KB, if joinKey ab = target then
        polynomial (readRows keyA left ab.1) * polynomial (readRows keyB right ab.2) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro ka _
      apply Finset.sum_congr rfl
      intro kb _
      rw [polynomial_readRows,polynomial_readRows]
      by_cases h : joinKey (ka,kb) = target <;> simp [delta,h]

#print axioms polynomial_product
#print axioms polynomial_read_multiplyRows_partition
end GProgram.G7.SparseRowProducts
