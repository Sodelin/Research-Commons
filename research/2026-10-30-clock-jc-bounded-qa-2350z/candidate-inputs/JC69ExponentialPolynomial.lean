import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Tactic

/-! Concrete exponential-polynomial annihilators for the finite-window proof.
Contributor: dot (OpenAI), 30 October 2026. UNCOMPILED CANDIDATE.
This is classical finite-difference mathematics, not a novelty claim.
No actual source Fourier expansion is postulated or proved in this module.
-/
noncomputable section
namespace ResearchCommons.MSCI.JC69ExponentialPolynomial
open scoped BigOperators
open Function

def weightedDiff (b : ℝ) (f : ℕ → ℝ) : ℕ → ℝ :=
  fun n => f (n+1) - b*f n

lemma weightedDiff_add (b : ℝ) (f g : ℕ → ℝ) :
    weightedDiff b (f+g) = weightedDiff b f + weightedDiff b g := by
  funext n
  simp only [weightedDiff,Pi.add_apply]
  ring

@[simp] lemma weightedDiff_zero (b : ℝ) : weightedDiff b 0 = 0 := by
  funext n
  simp [weightedDiff]

lemma weightedDiff_commute (a b : ℝ) (f : ℕ → ℝ) :
    weightedDiff a (weightedDiff b f) = weightedDiff b (weightedDiff a f) := by
  funext n
  simp only [weightedDiff]
  ring

/-- No division by the base: repeated or even zero bases are permitted. -/
lemma iterate_geometric_mul (b : ℝ) (g : ℝ → ℝ) (k n : ℕ) :
    (weightedDiff b)^[k] (fun m => b^m*g (m:ℝ)) n =
      b^n*b^k*((fwdDiff (1:ℝ))^[k] g) (n:ℝ) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (weightedDiff b)^[k] (fun m => b^m*g (m:ℝ)) (n+1) -
      b*((weightedDiff b)^[k] (fun m => b^m*g (m:ℝ)) n) = _
    rw [ih,ih,Function.iterate_succ_apply']
    simp only [fwdDiff,Nat.cast_add,Nat.cast_one,pow_succ]
    ring

lemma polynomial_term_annihilated (b : ℝ) (P : Polynomial ℝ) (r : ℕ)
    (hP : P.natDegree < r) :
    (weightedDiff b)^[r] (fun n => b^n*P.eval (n:ℝ)) = 0 := by
  funext n
  rw [iterate_geometric_mul,Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP]
  simp

/-- A literal product of monic first-order shift factors. -/
def annihilate : List ℝ → (ℕ → ℝ) → (ℕ → ℝ)
  | [], f => f
  | b::bs, f => weightedDiff b (annihilate bs f)

@[simp] lemma annihilate_zero (bs : List ℝ) : annihilate bs 0 = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [annihilate,ih]

lemma annihilate_add (bs : List ℝ) (f g : ℕ → ℝ) :
    annihilate bs (f+g) = annihilate bs f + annihilate bs g := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [annihilate,ih,weightedDiff_add]

lemma annihilate_append (as bs : List ℝ) (f : ℕ → ℝ) :
    annihilate (as++bs) f = annihilate as (annihilate bs f) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,annihilate,ih]

lemma annihilate_weightedDiff (bs : List ℝ) (b : ℝ) (f : ℕ → ℝ) :
    annihilate bs (weightedDiff b f) = weightedDiff b (annihilate bs f) := by
  induction bs with
  | nil => rfl
  | cons a bs ih =>
    rw [annihilate,ih,weightedDiff_commute]
    rfl

lemma annihilate_commute (as bs : List ℝ) (f : ℕ → ℝ) :
    annihilate as (annihilate bs f) = annihilate bs (annihilate as f) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [annihilate,ih,annihilate,annihilate_weightedDiff]

lemma annihilate_replicate (b : ℝ) (r : ℕ) (f : ℕ → ℝ) :
    annihilate (List.replicate r b) f = (weightedDiff b)^[r] f := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [List.replicate_succ,annihilate,ih,Function.iterate_succ_apply']

/-- Concrete finite exponential-polynomial sum, not an arbitrary sequence
labelled as a source law. Coefficients can be signed; bases can coincide. -/
def expPolySum : List (ℝ × Polynomial ℝ) → ℕ → ℝ
  | [], _ => 0
  | (b,P)::ts, n => b^n*P.eval (n:ℝ) + expPolySum ts n

def factors (r : ℕ) (ts : List (ℝ × Polynomial ℝ)) : List ℝ :=
  ts.flatMap (fun t => List.replicate r t.1)

lemma factors_length (r : ℕ) (ts : List (ℝ × Polynomial ℝ)) :
    (factors r ts).length = ts.length*r := by
  induction ts with
  | nil => simp [factors]
  | cons t ts ih => simp [factors,List.length_flatMap] at *; omega

/-- The actual product annihilator is derived for every concrete summand.
The resulting order is termCount*r, including repeated bases. -/
theorem expPolySum_annihilated (r : ℕ) (ts : List (ℝ × Polynomial ℝ))
    (hdeg : ∀ t ∈ ts, t.2.natDegree < r) :
    annihilate (factors r ts) (expPolySum ts) = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨b,P⟩
    have hP := hdeg (b,P) (by simp)
    have hts : ∀ t ∈ ts, t.2.natDegree < r := fun t ht => hdeg t (by simp [ht])
    have hp : annihilate (List.replicate r b) (fun n => b^n*P.eval (n:ℝ)) = 0 := by
      rw [annihilate_replicate]
      exact polynomial_term_annihilated b P r hP
    have he : expPolySum ((b,P)::ts) =
        (fun n => b^n*P.eval (n:ℝ)) + expPolySum ts := rfl
    rw [he,annihilate_add]
    change annihilate (List.replicate r b ++ factors r ts) _ +
      annihilate (List.replicate r b ++ factors r ts) _ = 0
    rw [annihilate_append,annihilate_commute, hp,annihilate_zero,
      annihilate_append,ih hts,annihilate_zero,add_zero]

/-- Monicity in usable form: after a zero prefix only the last value remains. -/
lemma annihilate_eq_last (bs : List ℝ) (f : ℕ → ℝ) (n : ℕ)
    (h : ∀ j < bs.length, f (n+j) = 0) :
    annihilate bs f n = f (n+bs.length) := by
  induction bs generalizing n with
  | nil => simp [annihilate]
  | cons b bs ih =>
    have h0 : ∀ j < bs.length, f (n+j) = 0 := by
      intro j hj
      exact h j (by simpa using Nat.lt_succ_of_lt hj)
    have h1 : ∀ j < bs.length, f ((n+1)+j) = 0 := by
      intro j hj
      have hh := h (j+1) (by simpa using Nat.succ_lt_succ hj)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    change annihilate bs f (n+1) - b*annihilate bs f n = _
    rw [ih (n+1) h1,ih n h0,h bs.length (by simp)]
    simp [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Concrete product-annihilator initial-window uniqueness. -/
theorem zero_of_annihilated_prefix (bs : List ℝ) (f : ℕ → ℝ)
    (ha : annihilate bs f = 0) (hz : ∀ n < bs.length, f n = 0) : f = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < bs.length
    · exact hz n hn
    · have hle : bs.length ≤ n := Nat.le_of_not_gt hn
      have hp : ∀ j < bs.length, f ((n-bs.length)+j) = 0 := by
        intro j hj
        exact ih _ (by omega)
      have he := annihilate_eq_last bs f (n-bs.length) hp
      rw [ha] at he
      simpa [Nat.sub_add_cancel hle] using he.symm

/-- Exact finite determination for the displayed concrete expansion; no
hypothesis says that any scientific likelihood already equals this sum. -/
theorem expPolySum_zero_of_grid (r : ℕ) (ts : List (ℝ × Polynomial ℝ))
    (hdeg : ∀ t ∈ ts, t.2.natDegree < r)
    (hz : ∀ n < ts.length*r, expPolySum ts n = 0) : expPolySum ts = 0 := by
  apply zero_of_annihilated_prefix (factors r ts) _ (expPolySum_annihilated r ts hdeg)
  simpa only [factors_length] using hz

#print axioms polynomial_term_annihilated
#print axioms expPolySum_annihilated
#print axioms expPolySum_zero_of_grid


/-- Rectangular-grid propagation in the FULL arbitrary finite count-vector
space. This is a recurrence lemma, not an asserted source representation.
The coefficient/factor lists are fixed per coordinate, independent of v. -/
theorem count_vector_zero_of_annihilated_cube (A K : ℕ)
    (H : (Fin A → ℕ) → ℝ) (bs : Fin A → List ℝ)
    (hlen : ∀ i, (bs i).length ≤ K)
    (ha : ∀ v i, annihilate (bs i) (fun n => H (Function.update v i n)) = 0)
    (hz : ∀ v, (∀ i, v i < K) → H v = 0) : H = 0 := by
  classical
  have step : ∀ k ≤ A, ∀ v : Fin A → ℕ,
      (∀ i, k ≤ i.val → v i < K) → H v = 0 := by
    intro k
    induction k with
    | zero =>
      intro hk v hv
      exact hz v (fun i => hv i (Nat.zero_le _))
    | succ k ih =>
      intro hk v hv
      have hkA : k < A := by omega
      let i : Fin A := ⟨k,hkA⟩
      have hp : ∀ n < (bs i).length, H (Function.update v i n) = 0 := by
        intro n hn
        apply ih (by omega) (Function.update v i n)
        intro j hj
        by_cases hji : j = i
        · subst j
          simpa using (lt_of_lt_of_le hn (hlen i))
        · rw [Function.update_of_ne hji]
          apply hv j
          have hne : j.val ≠ k := by
            intro he
            apply hji
            apply Fin.ext
            exact he
          omega
      have he := congrFun (zero_of_annihilated_prefix (bs i)
        (fun n => H (Function.update v i n)) (ha v i) hp) (v i)
      simpa only [Function.update_eq_self,Pi.zero_apply] using he
  funext v
  apply step A (Nat.le_refl _) v
  intro i hi
  exact False.elim (Nat.not_le_of_gt i.isLt hi)

#print axioms count_vector_zero_of_annihilated_cube
end ResearchCommons.MSCI.JC69ExponentialPolynomial
