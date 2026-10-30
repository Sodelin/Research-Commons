import ResearchCommons.MSCI.JC69ExponentialPolynomial
import Mathlib.Algebra.Polynomial.BigOperators

/-! Concrete multivariate exponential-polynomial finite-grid determination.
Classical mathematics, formalized by dot (OpenAI), 30 October 2026.
UNCOMPILED. Coordinate-degree box r corresponds to r=2F+1 in the hand proof.
No scientific-source expansion is an assumption or conclusion here.
-/
noncomputable section
namespace ResearchCommons.MSCI.JC69CountVectorGrid
open scoped BigOperators
open ResearchCommons.MSCI.JC69ExponentialPolynomial

/-- A finite coefficient array represents every polynomial with each
coordinate degree < r, including every total-degree < r polynomial. -/
structure Term (A r : ℕ) where
  beta : Fin A → ℝ
  coeff : (Fin A → Fin r) → ℝ

def monomial (A r : ℕ) (v : Fin A → ℕ) (e : Fin A → Fin r) : ℝ :=
  ∏ j, (v j:ℝ)^(e j).val

def termValue {A r : ℕ} (t : Term A r) (v : Fin A → ℕ) : ℝ :=
  (∑ e, t.coeff e * monomial A r v e) * ∏ j, t.beta j ^ v j

def value {A r : ℕ} : List (Term A r) → (Fin A → ℕ) → ℝ
  | [], _ => 0
  | t::ts, v => termValue t v + value ts v

/-- Actual univariate section: all other count coordinates become constants. -/
def sectionPolynomial {A r : ℕ} (t : Term A r) (i : Fin A) (v : Fin A → ℕ) : Polynomial ℝ :=
  ∑ e : Fin A → Fin r, Polynomial.monomial (e i).val
    (t.coeff e * (∏ j ∈ Finset.univ.erase i, (v j:ℝ)^(e j).val) *
      (∏ j ∈ Finset.univ.erase i, t.beta j ^ v j))

lemma section_degree {A r : ℕ} (hr : 0 < r) (t : Term A r)
    (i : Fin A) (v : Fin A → ℕ) : (sectionPolynomial t i v).natDegree < r := by
  have h : (sectionPolynomial t i v).natDegree ≤ r-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro e _
    exact (Polynomial.natDegree_monomial_le _).trans (by have := (e i).isLt; omega)
  omega

lemma monomial_update {A r : ℕ} (v : Fin A → ℕ) (i : Fin A) (n : ℕ)
    (e : Fin A → Fin r) :
    monomial A r (Function.update v i n) e =
      (n:ℝ)^(e i).val * ∏ j ∈ Finset.univ.erase i, (v j:ℝ)^(e j).val := by
  classical
  unfold monomial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma exponential_update {A : ℕ} (b : Fin A → ℝ) (v : Fin A → ℕ)
    (i : Fin A) (n : ℕ) :
    (∏ j, b j ^ (Function.update v i n) j) =
      b i ^ n * ∏ j ∈ Finset.univ.erase i, b j ^ v j := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma term_section {A r : ℕ} (t : Term A r) (i : Fin A) (v : Fin A → ℕ) (n : ℕ) :
    termValue t (Function.update v i n) =
      t.beta i ^ n * (sectionPolynomial t i v).eval (n:ℝ) := by
  classical
  simp only [termValue,monomial_update,exponential_update,sectionPolynomial,
    Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

def sections {A r : ℕ} (ts : List (Term A r)) (i : Fin A) (v : Fin A → ℕ) :
    List (ℝ × Polynomial ℝ) := ts.map (fun t => (t.beta i,sectionPolynomial t i v))

lemma value_section {A r : ℕ} (ts : List (Term A r)) (i : Fin A) (v : Fin A → ℕ) :
    (fun n => value ts (Function.update v i n)) = expPolySum (sections ts i v) := by
  funext n
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simpa only [value,sections,List.map_cons,expPolySum,term_section] using
      congrArg (fun x => t.beta i ^ n * (sectionPolynomial t i v).eval (n:ℝ) + x) ih

/-- The same coordinate factor list applies for ALL values of the other
coordinates: no source/count-dependent fitted recurrence is introduced. -/
def coordinateFactors {A r : ℕ} (ts : List (Term A r)) (i : Fin A) : List ℝ :=
  ts.flatMap (fun t => List.replicate r (t.beta i))

lemma sections_factors {A r : ℕ} (ts : List (Term A r)) (i : Fin A) (v : Fin A → ℕ) :
    factors r (sections ts i v) = coordinateFactors ts i := by
  simp [factors,sections,coordinateFactors,List.flatMap_map]

lemma coordinate_factors_length {A r : ℕ} (ts : List (Term A r)) (i : Fin A) :
    (coordinateFactors ts i).length = ts.length*r := by
  rw [← sections_factors ts i (fun _ => 0),factors_length]
  simp [sections]

theorem actual_count_vector_annihilator {A r : ℕ} (hr : 0 < r)
    (ts : List (Term A r)) (i : Fin A) (v : Fin A → ℕ) :
    annihilate (coordinateFactors ts i) (fun n => value ts (Function.update v i n)) = 0 := by
  rw [value_section,← sections_factors ts i v]
  apply expPolySum_annihilated
  intro t ht
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
  exact section_degree hr u i v

/-- Concrete full count-vector grid theorem at EXACT order termCount*r.
Taking at most 2M terms and r=2F+1 yields the hand proof's K bound, without
excluding repeated bases or imposing a generic source parameter restriction. -/
theorem value_zero_of_count_cube {A r : ℕ} (hr : 0 < r) (ts : List (Term A r))
    (hz : ∀ v, (∀ i, v i < ts.length*r) → value ts v = 0) : value ts = 0 := by
  apply count_vector_zero_of_annihilated_cube A (ts.length*r) (value ts) (coordinateFactors ts)
  · intro i
    exact le_of_eq (coordinate_factors_length ts i)
  · intro v i
    exact actual_count_vector_annihilator hr ts i v
  · exact hz

/-- The manuscript's exact loose bound, including fewer than 2M terms.
No positivity or distinctness of bases is used by this algebraic step. -/
theorem value_zero_of_manuscript_cube (A F M : ℕ)
    (ts : List (Term A (2*F+1))) (hm : ts.length ≤ 2*M)
    (hz : ∀ v, (∀ i, v i < 2*M*(2*F+1)) → value ts v = 0) : value ts = 0 := by
  apply count_vector_zero_of_annihilated_cube A (2*M*(2*F+1))
    (value ts) (coordinateFactors ts)
  · intro i
    rw [coordinate_factors_length]
    exact Nat.mul_le_mul_right (2*F+1) hm
  · intro v i
    exact actual_count_vector_annihilator (by omega) ts i v
  · exact hz

#print axioms term_section
#print axioms actual_count_vector_annihilator
#print axioms value_zero_of_count_cube
#print axioms value_zero_of_manuscript_cube
end ResearchCommons.MSCI.JC69CountVectorGrid
