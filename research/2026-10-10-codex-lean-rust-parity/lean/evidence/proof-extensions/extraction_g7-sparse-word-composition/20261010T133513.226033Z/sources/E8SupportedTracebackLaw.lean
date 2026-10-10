import E8FiniteTracebackLaw

/-!
Supported-root strengthening of the classical finite traceback theorem.
RNA inside tables may contain zero-mass subproblems. Nonnegative production
and terminal weights force every derivation below a zero partition to have
zero weight. Exact branch selection assigns that subtree zero probability.
Thus only the starting partition must be positive, not every state/depth.
This removes a genuine source-admission mismatch; carrier, exact weights,
independent input and RNA bijection remain separate source obligations.
-/
noncomputable section
namespace E8SupportedTracebackLaw
open E8FiniteTracebackLaw
open scoped BigOperators

variable {State : Type*} (b : ℕ) (factor : State → Fin b → ℝ)
    (next : State → Fin b → State) (terminal : State → ℝ)

theorem partition_nonnegative
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s) (d : ℕ) (s : State) :
    0 ≤ partition b factor next terminal d s := by
  rw [← traceWeight_sum b factor next terminal d s]
  exact Finset.sum_nonneg (fun t _ => traceWeight_nonnegative b factor next terminal hf ht d s t)

theorem zero_partition_derivation_weight
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (hz : partition b factor next terminal d s = 0) (t : Trace b d) :
    traceWeight b factor next terminal d s t = 0 := by
  have hlo := traceWeight_nonnegative b factor next terminal hf ht d s t
  have hhi : traceWeight b factor next terminal d s t ≤
      ∑ u : Trace b d, traceWeight b factor next terminal d s u :=
    Finset.single_le_sum (fun u _ => traceWeight_nonnegative b factor next terminal hf ht d s u)
      (Finset.mem_univ t)
  rw [traceWeight_sum, hz] at hhi
  exact le_antisymm hhi hlo

theorem supported_traceProbability_eq_normalized_weight
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (hroot : 0 < partition b factor next terminal d s) (t : Trace b d) :
    traceProbability b factor next terminal d s t =
      traceWeight b factor next terminal d s t / partition b factor next terminal d s := by
  induction d generalizing s with
  | zero =>
    change 1 = terminal s / terminal s
    exact (div_self (ne_of_gt hroot)).symm
  | succ d ih =>
    change (factor s t.1 * partition b factor next terminal d (next s t.1) /
      partition b factor next terminal (d + 1) s) *
      traceProbability b factor next terminal d (next s t.1) t.2 =
      (factor s t.1 * traceWeight b factor next terminal d (next s t.1) t.2) /
        partition b factor next terminal (d + 1) s
    by_cases hchild : 0 < partition b factor next terminal d (next s t.1)
    · rw [ih (next s t.1) hchild]
      field_simp [ne_of_gt hchild, ne_of_gt hroot]
    · have hz : partition b factor next terminal d (next s t.1) = 0 := by
        have hnonneg := partition_nonnegative b factor next terminal hf ht d (next s t.1)
        linarith
      have hw := zero_partition_derivation_weight b factor next terminal hf ht d (next s t.1) hz t.2
      rw [hz, hw]
      simp

theorem supported_traceProbability_total
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (hroot : 0 < partition b factor next terminal d s) :
    (∑ t : Trace b d, traceProbability b factor next terminal d s t) = 1 := by
  simp_rw [supported_traceProbability_eq_normalized_weight b factor next terminal hf ht d s hroot]
  rw [← Finset.sum_div, traceWeight_sum, div_self (ne_of_gt hroot)]

theorem supported_observable_probability {Class : Type*} [DecidableEq Class]
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (hroot : 0 < partition b factor next terminal d s)
    (observe : Trace b d → Class) (c : Class) :
    (∑ t : Trace b d, if observe t = c then traceProbability b factor next terminal d s t else 0) =
      (∑ t : Trace b d, if observe t = c then traceWeight b factor next terminal d s t else 0) /
        partition b factor next terminal d s := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs
  · exact supported_traceProbability_eq_normalized_weight b factor next terminal hf ht d s hroot t
  · simp

end E8SupportedTracebackLaw
#print axioms E8SupportedTracebackLaw.partition_nonnegative
#print axioms E8SupportedTracebackLaw.zero_partition_derivation_weight
#print axioms E8SupportedTracebackLaw.supported_traceProbability_eq_normalized_weight
#print axioms E8SupportedTracebackLaw.supported_traceProbability_total
#print axioms E8SupportedTracebackLaw.supported_observable_probability
