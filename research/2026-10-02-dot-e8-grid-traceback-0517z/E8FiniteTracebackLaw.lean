import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Classical finite-depth weighted traceback cancellation, made explicit.
State transitions and production factors define the partition function; branch
probabilities are derived from those partitions. No target law is a field.
A derivation-to-RNA bijection, original energy weights, exhaustive/disjoint
productions, and the executable source bridge are separate obligations. The
finite conditional-product law models independent fresh branch choices; it does
not prove that PRISM or mt19937 supplies them. These are established weighted
sampling facts, not a novelty claim or a tractability claim.
-/
noncomputable section
namespace E8FiniteTracebackLaw
open scoped BigOperators

variable {State : Type*} (b : ℕ)

def Trace : ℕ → Type
  | 0 => Unit
  | d + 1 => Fin b × Trace d

instance traceFintype : (d : ℕ) → Fintype (Trace b d)
  | 0 => inferInstanceAs (Fintype Unit)
  | d + 1 => @instFintypeProd (Fin b) (Trace b d) inferInstance (traceFintype d)

variable (factor : State → Fin b → ℝ) (next : State → Fin b → State)
    (terminal : State → ℝ)

def partition : ℕ → State → ℝ
  | 0, s => terminal s
  | d + 1, s => ∑ j : Fin b, factor s j * partition d (next s j)

def traceWeight : (d : ℕ) → State → Trace b d → ℝ
  | 0, s, _ => terminal s
  | d + 1, s, t => factor s t.1 * traceWeight d (next s t.1) t.2

def branchProbability (d : ℕ) (s : State) (j : Fin b) : ℝ :=
  factor s j * partition b factor next terminal d (next s j) /
    partition b factor next terminal (d + 1) s

def traceProbability : (d : ℕ) → State → Trace b d → ℝ
  | 0, _, _ => 1
  | d + 1, s, t => branchProbability b factor next terminal d s t.1 *
      traceProbability d (next s t.1) t.2

 theorem traceWeight_sum (d : ℕ) (s : State) :
    (∑ t : Trace b d, traceWeight b factor next terminal d s t) =
      partition b factor next terminal d s := by
  induction d generalizing s with
  | zero =>
    change (∑ _ : Unit, terminal s) = terminal s
    simp
  | succ d ih =>
    change (∑ t : Fin b × Trace b d,
      factor s t.1 * traceWeight b factor next terminal d (next s t.1) t.2) = _
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ih]
    rfl

 theorem partition_positive
    (hfactor : ∀ s j, 0 ≤ factor s j)
    (hlive : ∀ s, ∃ j, 0 < factor s j)
    (hterminal : ∀ s, 0 < terminal s) (d : ℕ) (s : State) :
    0 < partition b factor next terminal d s := by
  induction d generalizing s with
  | zero => exact hterminal s
  | succ d ih =>
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (hfactor s j) (ih (next s j)).le
    · obtain ⟨j, hj⟩ := hlive s
      exact ⟨j, Finset.mem_univ _, mul_pos hj (ih (next s j))⟩

 theorem traceWeight_nonnegative
    (hfactor : ∀ s j, 0 ≤ factor s j) (hterminal : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (t : Trace b d) :
    0 ≤ traceWeight b factor next terminal d s t := by
  induction d generalizing s with
  | zero => exact hterminal s
  | succ d ih => exact mul_nonneg (hfactor s t.1) (ih (next s t.1) t.2)

 theorem traceProbability_eq_normalized_weight
    (hpartition : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) (t : Trace b d) :
    traceProbability b factor next terminal d s t =
      traceWeight b factor next terminal d s t / partition b factor next terminal d s := by
  induction d generalizing s with
  | zero =>
    change 1 = terminal s / terminal s
    have ht : terminal s ≠ 0 := ne_of_gt (hpartition 0 s)
    simp [ht]
  | succ d ih =>
    change (factor s t.1 * partition b factor next terminal d (next s t.1) /
      partition b factor next terminal (d + 1) s) *
      traceProbability b factor next terminal d (next s t.1) t.2 = _
    rw [ih]
    change _ = (factor s t.1 * traceWeight b factor next terminal d (next s t.1) t.2) /
      partition b factor next terminal (d + 1) s
    field_simp [ne_of_gt (hpartition d (next s t.1)), ne_of_gt (hpartition (d + 1) s)]

 theorem traceProbability_total
    (hpartition : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) :
    (∑ t : Trace b d, traceProbability b factor next terminal d s t) = 1 := by
  simp_rw [traceProbability_eq_normalized_weight b factor next terminal hpartition]
  rw [← Finset.sum_div, traceWeight_sum, div_self (ne_of_gt (hpartition d s))]

/-- Fixed arbitrary observables may identify many derivations; every fiber is
summed. This does not assume that the classifier is compositional. -/
 theorem observable_probability {Class : Type*} [DecidableEq Class]
    (hpartition : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) (observe : Trace b d → Class) (c : Class) :
    (∑ t : Trace b d, if observe t = c then traceProbability b factor next terminal d s t else 0) =
      (∑ t : Trace b d, if observe t = c then traceWeight b factor next terminal d s t else 0) /
        partition b factor next terminal d s := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · exact traceProbability_eq_normalized_weight b factor next terminal hpartition d s t
  · simp

/-- An actual finite bijection removes derivation multiplicities from the
structure law. No unambiguity conclusion is hidden in a grammar record. -/
 theorem unambiguous_observable_probability {Structure Class : Type*}
    [Fintype Structure] [DecidableEq Class]
    (hpartition : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) (decode : Trace b d ≃ Structure)
    (sourceWeight : Structure → ℝ) (classify : Structure → Class)
    (hweight : ∀ t, traceWeight b factor next terminal d s t = sourceWeight (decode t))
    (c : Class) :
    (∑ t : Trace b d, if classify (decode t) = c then
        traceProbability b factor next terminal d s t else 0) =
      (∑ r : Structure, if classify r = c then sourceWeight r else 0) /
        (∑ r : Structure, sourceWeight r) := by
  rw [observable_probability b factor next terminal hpartition]
  have hden : partition b factor next terminal d s = ∑ r : Structure, sourceWeight r := by
    rw [← traceWeight_sum b factor next terminal d s]
    simp_rw [hweight]
    exact Equiv.sum_comp decode sourceWeight
  rw [hden]
  congr 1
  simp_rw [hweight]
  exact Equiv.sum_comp decode (fun r => if classify r = c then sourceWeight r else 0)

end E8FiniteTracebackLaw
#print axioms E8FiniteTracebackLaw.traceWeight_sum
#print axioms E8FiniteTracebackLaw.partition_positive
#print axioms E8FiniteTracebackLaw.traceProbability_eq_normalized_weight
#print axioms E8FiniteTracebackLaw.traceProbability_total
#print axioms E8FiniteTracebackLaw.observable_probability
#print axioms E8FiniteTracebackLaw.unambiguous_observable_probability
