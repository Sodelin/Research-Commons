import E8MidpointProductionKernel

/-!
End-to-end composition INSIDE the explicit finite grammar model:
actual exact-real midpoint-selector fiber counts -> normalized production
kernels -> independent conditional-product traceback law -> arbitrary fixed
observable -> normalized weighted derivation/structure law, with explicit
bias bound depth*(branchBound-1)/(2*gridSize).
This is a model bridge, not PRISM executable verification. In particular, the
actual continuation-stack carrier/depth, RNA bijection, source energy factors,
classifier agreement, MT random law and floating arithmetic remain obligations.
-/
noncomputable section
namespace E8GridTracebackBridge
open E8FiniteTracebackLaw E8TracebackErrorComposition E8MidpointProductionKernel
open scoped BigOperators

variable {State : Type*} (b : ℕ) (factor : State → Fin b → ℝ)
    (next : State → Fin b → State) (terminal : State → ℝ)

 theorem branchProbability_nonnegative
    (hf : ∀ s j, 0 ≤ factor s j)
    (hP : ∀ d s, 0 < partition b factor next terminal d s) (d : ℕ) (s : State) (j : Fin b) :
    0 ≤ branchProbability b factor next terminal d s j :=
  div_nonneg (mul_nonneg (hf s j) (hP d (next s j)).le) (hP (d + 1) s).le

 theorem branchProbability_total
    (hP : ∀ d s, 0 < partition b factor next terminal d s) (d : ℕ) (s : State) :
    (∑ j, branchProbability b factor next terminal d s j) = 1 := by
  simp only [branchProbability, ← Finset.sum_div]
  change partition b factor next terminal (d + 1) s / partition b factor next terminal (d + 1) s = 1
  exact div_self (ne_of_gt (hP (d + 1) s))

 theorem pathLaw_eq_traceProbability (d : ℕ) (s : State) (t : Trace b d) :
    pathLaw b next (branchProbability b factor next terminal) d s t =
      traceProbability b factor next terminal d s t := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih =>
    change branchProbability b factor next terminal d s t.1 *
      pathLaw b next (branchProbability b factor next terminal) d (next s t.1) t.2 = _
    rw [ih]
    rfl

def gridProductionKernel (N : ℕ)
    (hP : ∀ d s, 0 < partition b factor next terminal d s) (d : ℕ) (s : State) (j : Fin b) : ℝ :=
  gridKernel N (productionWeights b factor next terminal d s)
    (by rw [productionWeight_total]; exact hP (d + 1) s) j

 theorem grid_trace_observable_error
    (N : ℕ) (hN : 0 < N) (hf : ∀ s j, 0 ≤ factor s j)
    (hP : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) (event : Trace b d → Prop) [DecidablePred event] :
    |(∑ t, if event t then traceProbability b factor next terminal d s t else 0) -
      (∑ t, if event t then
        pathLaw b next (gridProductionKernel b factor next terminal N hP) d s t else 0)| ≤
      (d : ℝ) * ((b - 1 : ℕ) / (2 * N)) := by
  have hp0 := branchProbability_nonnegative b factor next terminal hf hP
  have hp1 := branchProbability_total b factor next terminal hP
  have hq0 : ∀ r s j, 0 ≤ gridProductionKernel b factor next terminal N hP r s j := by
    intro r s j
    exact gridKernel_nonnegative N (productionWeights b factor next terminal r s) _ j
  have hq1 : ∀ r s, (∑ j, gridProductionKernel b factor next terminal N hP r s j) = 1 := by
    intro r s
    exact gridKernel_total N hN (productionWeights b factor next terminal r s) _
  have hloc : ∀ r s, (∑ j, |branchProbability b factor next terminal r s j -
      gridProductionKernel b factor next terminal N hP r s j|) ≤
      2 * ((b - 1 : ℕ) / (2 * N)) := by
    intro r s
    have hw : ∀ j, 0 ≤ productionWeights b factor next terminal r s j := fun j =>
      mul_nonneg (hf s j) (hP r (next s j)).le
    have ht := gridKernel_TV N hN (productionWeights b factor next terminal r s) hw
      (by rw [productionWeight_total]; exact hP (r + 1) s)
    have heq : (∑ j, |branchProbability b factor next terminal r s j -
        gridProductionKernel b factor next terminal N hP r s j|) =
        ∑ j, |gridKernel N (productionWeights b factor next terminal r s)
          (by rw [productionWeight_total]; exact hP (r + 1) s) j -
          productionWeights b factor next terminal r s j /
            (∑ k, productionWeights b factor next terminal r s k)| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_sub_comm]
      rfl
    rw [heq]
    linarith
  have h := observable_trace_error b next (branchProbability b factor next terminal)
    (gridProductionKernel b factor next terminal N hP) hp0 hq0 hp1 hq1
    ((b - 1 : ℕ) / (2 * N)) hloc d s event
  simpa only [pathLaw_eq_traceProbability] using h

/-- The final class observable can be non-compositional; no fast class-DP
algorithm is asserted. A literal source bijection/weight agreement is required. -/
 theorem unambiguous_grid_class_error {Structure Class : Type*} [Fintype Structure] [DecidableEq Class]
    (N : ℕ) (hN : 0 < N) (hf : ∀ s j, 0 ≤ factor s j)
    (hP : ∀ d s, 0 < partition b factor next terminal d s)
    (d : ℕ) (s : State) (decode : Trace b d ≃ Structure)
    (sourceWeight : Structure → ℝ) (classify : Structure → Class)
    (hweight : ∀ t, traceWeight b factor next terminal d s t = sourceWeight (decode t))
    (c : Class) :
    |(∑ t, if classify (decode t) = c then
        pathLaw b next (gridProductionKernel b factor next terminal N hP) d s t else 0) -
      (∑ r : Structure, if classify r = c then sourceWeight r else 0) /
        (∑ r : Structure, sourceWeight r)| ≤ (d : ℝ) * ((b - 1 : ℕ) / (2 * N)) := by
  have h := grid_trace_observable_error b factor next terminal N hN hf hP d s
    (fun t => classify (decode t) = c)
  rw [unambiguous_observable_probability b factor next terminal hP d s decode sourceWeight classify hweight c] at h
  rwa [abs_sub_comm]

end E8GridTracebackBridge
#print axioms E8GridTracebackBridge.branchProbability_total
#print axioms E8GridTracebackBridge.pathLaw_eq_traceProbability
#print axioms E8GridTracebackBridge.grid_trace_observable_error
#print axioms E8GridTracebackBridge.unambiguous_grid_class_error
