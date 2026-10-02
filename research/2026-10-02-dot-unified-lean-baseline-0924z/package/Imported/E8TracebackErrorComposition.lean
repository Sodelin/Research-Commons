import E8FiniteTracebackLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Classical finite stochastic-kernel perturbation bound on a common traceback
state graph. Conditional products encode fresh independent choices. The exact
and approximate local tables must be nonnegative and normalized, and their
local TV must be bounded on all reachable states (here supplied on all states).
Then a depth-d trace and any fixed observable event have error at most d*epsilon.
This is not a proof of engine independence, numerical recurrence fidelity,
RNA support, or a uniform implementation depth bound. It is the named bridge
for composing E8MidpointGridTV with admitted numerical local-kernel bounds.
-/
noncomputable section
namespace E8TracebackErrorComposition
open E8FiniteTracebackLaw
open scoped BigOperators

variable {State : Type*} (b : ℕ) (next : State → Fin b → State)

def pathLaw (kernel : ℕ → State → Fin b → ℝ) : (d : ℕ) → State → Trace b d → ℝ
  | 0, _, _ => 1
  | d + 1, s, t => kernel d s t.1 * pathLaw kernel d (next s t.1) t.2

theorem pathLaw_nonnegative (kernel : ℕ → State → Fin b → ℝ)
    (hk : ∀ d s j, 0 ≤ kernel d s j) (d : ℕ) (s : State) (t : Trace b d) :
    0 ≤ pathLaw b next kernel d s t := by
  induction d generalizing s with
  | zero => exact zero_le_one
  | succ d ih => exact mul_nonneg (hk d s t.1) (ih (next s t.1) t.2)

theorem pathLaw_total (kernel : ℕ → State → Fin b → ℝ)
    (hk : ∀ d s, (∑ j, kernel d s j) = 1) (d : ℕ) (s : State) :
    (∑ t : Trace b d, pathLaw b next kernel d s t) = 1 := by
  induction d generalizing s with
  | zero =>
    change (∑ _ : Unit, (1 : ℝ)) = 1
    simp
  | succ d ih =>
    change (∑ t : Fin b × Trace b d,
      kernel d s t.1 * pathLaw b next kernel d (next s t.1) t.2) = 1
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ih, mul_one]
    exact hk d s

/-- L1 form retains exact constants before dividing by two for total variation. -/
theorem path_L1_bound (p q : ℕ → State → Fin b → ℝ)
    (hp0 : ∀ d s j, 0 ≤ p d s j) (hq0 : ∀ d s j, 0 ≤ q d s j)
    (hp1 : ∀ d s, (∑ j, p d s j) = 1)
    (hq1 : ∀ d s, (∑ j, q d s j) = 1)
    (epsilon : ℝ)
    (hloc : ∀ d s, (∑ j, |p d s j - q d s j|) ≤ 2 * epsilon)
    (d : ℕ) (s : State) :
    (∑ t : Trace b d, |pathLaw b next p d s t - pathLaw b next q d s t|) ≤
      2 * (d : ℝ) * epsilon := by
  induction d generalizing s with
  | zero =>
    simp [pathLaw]
  | succ d ih =>
    change (∑ t : Fin b × Trace b d,
      |p d s t.1 * pathLaw b next p d (next s t.1) t.2 -
        q d s t.1 * pathLaw b next q d (next s t.1) t.2|) ≤ _
    rw [Fintype.sum_prod_type]
    have hfiber : ∀ j : Fin b,
      (∑ t : Trace b d,
        |p d s j * pathLaw b next p d (next s j) t -
          q d s j * pathLaw b next q d (next s j) t|) ≤
        |p d s j - q d s j| + q d s j * (2 * (d : ℝ) * epsilon) := by
      intro j
      calc
        _ ≤ ∑ t : Trace b d,
            (|p d s j - q d s j| * pathLaw b next p d (next s j) t +
              q d s j * |pathLaw b next p d (next s j) t - pathLaw b next q d (next s j) t|) := by
          apply Finset.sum_le_sum
          intro t _
          have hid : p d s j * pathLaw b next p d (next s j) t -
              q d s j * pathLaw b next q d (next s j) t =
              (p d s j - q d s j) * pathLaw b next p d (next s j) t +
              q d s j * (pathLaw b next p d (next s j) t - pathLaw b next q d (next s j) t) := by ring
          rw [hid]
          have h := abs_add_le ((p d s j - q d s j) * pathLaw b next p d (next s j) t)
            (q d s j * (pathLaw b next p d (next s j) t - pathLaw b next q d (next s j) t))
          simpa only [abs_mul, abs_of_nonneg (pathLaw_nonnegative b next p hp0 d (next s j) t),
            abs_of_nonneg (hq0 d s j)] using h
        _ = |p d s j - q d s j| + q d s j *
            (∑ t : Trace b d, |pathLaw b next p d (next s j) t - pathLaw b next q d (next s j) t|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            pathLaw_total b next p hp1, mul_one]
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (ih (next s j)) (hq0 d s j))
    calc
      _ ≤ ∑ j : Fin b, (|p d s j - q d s j| + q d s j * (2 * (d : ℝ) * epsilon)) := by
        exact Finset.sum_le_sum (fun j _ => hfiber j)
      _ = (∑ j, |p d s j - q d s j|) + 2 * (d : ℝ) * epsilon := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hq1, one_mul]
      _ ≤ 2 * epsilon + 2 * (d : ℝ) * epsilon := add_le_add (hloc d s) le_rfl
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

 theorem finite_event_error_le_TV {A : Type*} [Fintype A]
    (p q : A → ℝ) (hp : (∑ a, p a) = 1) (hq : (∑ a, q a) = 1)
    (event : A → Prop) [DecidablePred event] :
    |(∑ a, if event a then p a else 0) - (∑ a, if event a then q a else 0)| ≤
      (∑ a, |p a - q a|) / 2 := by
  let f := fun a => p a - q a
  let x := ∑ a, if event a then f a else 0
  let y := ∑ a, if event a then 0 else f a
  have htotal : x + y = 0 := by
    dsimp [x, y]
    rw [← Finset.sum_add_distrib]
    have heq : (∑ a, ((if event a then f a else 0) + (if event a then 0 else f a))) = ∑ a, f a := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp
    rw [heq]
    simp [f, Finset.sum_sub_distrib, hp, hq]
  have hx := Finset.abs_sum_le_sum_abs (fun a => if event a then f a else 0) Finset.univ
  have hy := Finset.abs_sum_le_sum_abs (fun a => if event a then 0 else f a) Finset.univ
  have habs : (∑ a, |if event a then f a else 0|) +
      (∑ a, |if event a then 0 else f a|) = ∑ a, |f a| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  have hxy : y = -x := by linarith
  change |x| ≤ _ at hx
  change |y| ≤ _ at hy
  rw [hxy, abs_neg] at hy
  have hdiff : (∑ a, if event a then p a else 0) - (∑ a, if event a then q a else 0) = x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [f]
    split_ifs <;> simp
  rw [hdiff]
  change |x| ≤ (∑ a, |f a|) / 2
  linarith

theorem observable_trace_error (p q : ℕ → State → Fin b → ℝ)
    (hp0 : ∀ d s j, 0 ≤ p d s j) (hq0 : ∀ d s j, 0 ≤ q d s j)
    (hp1 : ∀ d s, (∑ j, p d s j) = 1)
    (hq1 : ∀ d s, (∑ j, q d s j) = 1)
    (epsilon : ℝ) (hloc : ∀ d s, (∑ j, |p d s j - q d s j|) ≤ 2 * epsilon)
    (d : ℕ) (s : State) (event : Trace b d → Prop) [DecidablePred event] :
    |(∑ t, if event t then pathLaw b next p d s t else 0) -
      (∑ t, if event t then pathLaw b next q d s t else 0)| ≤ (d : ℝ) * epsilon := by
  have hevent := finite_event_error_le_TV (pathLaw b next p d s) (pathLaw b next q d s)
    (pathLaw_total b next p hp1 d s) (pathLaw_total b next q hq1 d s) event
  have hpaths := path_L1_bound b next p q hp0 hq0 hp1 hq1 epsilon hloc d s
  linarith

end E8TracebackErrorComposition
#print axioms E8TracebackErrorComposition.pathLaw_total
#print axioms E8TracebackErrorComposition.path_L1_bound
#print axioms E8TracebackErrorComposition.finite_event_error_le_TV
#print axioms E8TracebackErrorComposition.observable_trace_error
