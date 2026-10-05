import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.BigOperators
import E8SupportedTracebackLaw

/-!
# E8 paper/source/observable bridge using existing mathlib laws

This module reuses `Equiv.sum_comp`, `PMF.normalize`, `PMF.map_apply`, and
`PMF.map_ofFintype`. It does not supply a new grammar or sampling principle.
CParty section 4 Theorem 1 already gives completeness/correctness/unambiguity
for the paper recurrences; PRISM section 2.1 already gives the traceback law.

The record below lists the actual source admission obligations. In particular,
its equivalence, weights and classifier commutation are NOT proved for C++ by
constructing a record or by compiling this file. No equality of the desired
probability laws is a field. The selected-class equality is derived from the
separate finite-bijection/weight/classifier premises.

The class type need not be finite: current shape strings range over an infinite
type, even though one fixed finite ensemble has a finite observable image.
The stronger finite-class table theorem is explicitly restricted to that case.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace UnifiedLean.Source.E8PaperObservableBridge

variable {Derivation Structure Class : Type*}

/-- Source-to-paper admission data. The paper theorem does not automatically
instantiate these fields for a changed/re-expressed program. -/
structure SourceContract (Derivation Structure Class : Type*) where
  interpret : Derivation ≃ Structure
  sourceWeight : Derivation → ℝ≥0∞
  paperWeight : Structure → ℝ≥0∞
  weight_preserved : ∀ d, sourceWeight d = paperWeight (interpret d)
  actualClassify : Derivation → Class
  paperClassify : Structure → Class
  classifier_commutes : ∀ d, actualClassify d = paperClassify (interpret d)

def normalizer {α : Type*} [Fintype α] (weight : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a, weight a

def classMass {α : Type*} [Fintype α] [DecidableEq Class]
    (weight : α → ℝ≥0∞) (classify : α → Class) (c : Class) : ℝ≥0∞ :=
  ∑ a with classify a = c, weight a

/-- Existing mathlib normalized PMF; zero-weight outcomes are admitted. Only
the root normalizer is required to be nonzero and finite. -/
def law {α : Type*} [Fintype α] (weight : α → ℝ≥0∞)
    (hzero : normalizer weight ≠ 0) (hfinite : normalizer weight ≠ ∞) : PMF α :=
  PMF.normalize weight
    (by simpa only [tsum_fintype, normalizer] using hzero)
    (by simpa only [tsum_fintype, normalizer] using hfinite)

theorem law_apply {α : Type*} [Fintype α] (weight : α → ℝ≥0∞)
    (hzero : normalizer weight ≠ 0) (hfinite : normalizer weight ≠ ∞) (a : α) :
    law weight hzero hfinite a = weight a * (normalizer weight)⁻¹ := by
  simp only [law, PMF.normalize_apply, tsum_fintype, normalizer]

section LibraryBindings
variable {α : Type*} [Fintype α]

open scoped Classical in
/-- Direct reuse of mathlib's finite PMF mapping law. No classifier injectivity
is imposed: a class receives the SUM of its members. -/
theorem finite_class_table [Fintype Class] (density : α → ℝ≥0∞)
    (htotal : ∑ a, density a = 1) (classify : α → Class) :
    (PMF.ofFintype density htotal).map classify =
      PMF.ofFintype (fun c => ∑ a with classify a = c, density a)
        (by simpa [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ classify density]) := by
  exact PMF.map_ofFintype density htotal classify

/-- Arbitrary class labels, including String, need no globally finite class
universe. This is mathlib map_apply and finite tsum conversion. -/
theorem selected_class_probability [DecidableEq Class]
    (weight : α → ℝ≥0∞) (hzero : normalizer weight ≠ 0)
    (hfinite : normalizer weight ≠ ∞) (classify : α → Class) (c : Class) :
    ((law weight hzero hfinite).map classify) c =
      classMass weight classify c * (normalizer weight)⁻¹ := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  simp_rw [law_apply]
  simp only [classMass, Finset.sum_filter]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : classify a = c
  · simp [h]
  · simp [h, Ne.symm h]

/-- Type-level reuse of mathlib supported continuation, avoiding arbitrary
fallback kernels on zero-weight/dead outcomes. No recursive source law is
asserted by this abbreviation. -/
abbrev SupportedContinuation {β : Type*} (p : PMF α) :=
  ∀ a ∈ p.support, PMF β

end LibraryBindings

section PaperTransport
variable [Fintype Derivation] [Fintype Structure]
    (contract : SourceContract Derivation Structure Class)

theorem normalizer_preserved :
    normalizer contract.sourceWeight = normalizer contract.paperWeight := by
  simp only [normalizer]
  simp_rw [contract.weight_preserved]
  exact Equiv.sum_comp contract.interpret contract.paperWeight

theorem classMass_preserved [DecidableEq Class] (c : Class) :
    classMass contract.sourceWeight contract.actualClassify c =
      classMass contract.paperWeight contract.paperClassify c := by
  classical
  simp only [classMass, Finset.sum_filter]
  simp_rw [contract.classifier_commutes, contract.weight_preserved]
  exact Equiv.sum_comp contract.interpret
    (fun r => if contract.paperClassify r = c then contract.paperWeight r else 0)

/-- A paper/source bridge derives a selected-class probability law. Its weight
and classifier premises remain actual program obligations, not conclusions
manufactured by naming the record. -/
theorem source_selected_class_is_paper_mass [DecidableEq Class]
    (hzero : normalizer contract.paperWeight ≠ 0)
    (hfinite : normalizer contract.paperWeight ≠ ∞) (c : Class) :
    ((law contract.sourceWeight
        (by rw [normalizer_preserved contract]; exact hzero)
        (by rw [normalizer_preserved contract]; exact hfinite)).map
          contract.actualClassify) c =
      classMass contract.paperWeight contract.paperClassify c *
        (normalizer contract.paperWeight)⁻¹ := by
  rw [selected_class_probability, classMass_preserved, normalizer_preserved]

end PaperTransport

section SupportedTraceTransport
open E8FiniteTracebackLaw E8SupportedTracebackLaw

variable {State : Type*} (b : ℕ) (factor : State → Fin b → ℝ)
    (next : State → Fin b → State) (terminal : State → ℝ)

/-- Only positive-weight traces require an RNA interpretation. Invalid/padded
zero-weight tuples are outside this subtype. This is the declared finite
traceback model, not a C++ continuation-stack implementation. -/
abbrev PositiveTrace (d : ℕ) (s : State) :=
  {t : Trace b d // 0 < traceWeight b factor next terminal d s t}

instance positiveTraceFintype (d : ℕ) (s : State) :
    Fintype (PositiveTrace b factor next terminal d s) :=
  Fintype.ofFinite _

/-- Nonnegative model weights make the complement of positive support zero.
No positivity of child partitions is assumed. -/
theorem trace_weight_zero_outside_positive
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (t : Trace b d)
    (hout : ¬ 0 < traceWeight b factor next terminal d s t) :
    traceWeight b factor next terminal d s t = 0 :=
  le_antisymm (le_of_not_gt hout)
    (traceWeight_nonnegative b factor next terminal hf ht d s t)

/-- Existing finite-sum restriction theorem removes the zero complement.
It does not require a bijection on all padded trace tuples. -/
theorem sum_restrict_positive_traces
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (d : ℕ) (s : State) (f : Trace b d → ℝ)
    (hzero : ∀ t, traceWeight b factor next terminal d s t = 0 → f t = 0) :
    (∑ t : Trace b d, f t) =
      ∑ t : PositiveTrace b factor next terminal d s, f t.val := by
  classical
  have h := Finset.sum_congr_set
    {t | 0 < traceWeight b factor next terminal d s t} f
    (fun t => f t.val) (fun _ _ => rfl)
    (fun t hout => hzero t
      (trace_weight_zero_outside_positive b factor next terminal hf ht d s t hout))
  refine h.trans ?_
  apply Finset.sum_congr
  · ext t
    simp
  · intro _ _
    rfl

/-- Named source/paper obligation on POSITIVE support. Neither the probability
equality nor a C++ source refinement is a field. The weights on the left are
fixed by the imported trace model, rather than an arbitrary claimed law. -/
structure SupportedTracePaperContract (d : ℕ) (s : State)
    (Structure Class : Type*) where
  interpret : PositiveTrace b factor next terminal d s ≃ Structure
  paperWeight : Structure → ℝ
  actualClassify : Trace b d → Class
  paperClassify : Structure → Class
  weight_preserved : ∀ t,
    traceWeight b factor next terminal d s t.val = paperWeight (interpret t)
  classifier_commutes : ∀ t, actualClassify t.val = paperClassify (interpret t)

variable [Fintype Structure] (d : ℕ) (s : State)
    (contract : SupportedTracePaperContract b factor next terminal d s Structure Class)

theorem supported_paper_normalizer
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s) :
    partition b factor next terminal d s = ∑ r : Structure, contract.paperWeight r := by
  rw [← traceWeight_sum b factor next terminal d s,
    sum_restrict_positive_traces b factor next terminal hf ht d s
      (traceWeight b factor next terminal d s) (fun _ h => h)]
  simp_rw [contract.weight_preserved]
  exact Equiv.sum_comp contract.interpret contract.paperWeight

theorem supported_paper_class_mass [DecidableEq Class]
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s) (c : Class) :
    (∑ t : Trace b d, if contract.actualClassify t = c then
        traceWeight b factor next terminal d s t else 0) =
      ∑ r : Structure, if contract.paperClassify r = c then contract.paperWeight r else 0 := by
  rw [sum_restrict_positive_traces b factor next terminal hf ht d s
    (fun t => if contract.actualClassify t = c then traceWeight b factor next terminal d s t else 0)
    (by intro t h; simp [h])]
  simp_rw [contract.classifier_commutes, contract.weight_preserved]
  exact Equiv.sum_comp contract.interpret
    (fun r => if contract.paperClassify r = c then contract.paperWeight r else 0)

/-- End-to-end mathematical endpoint: the existing supported-root traceback
law plus the positive-support paper interpretation yields the current class
mass. Only the starting partition is positive; zero child states and arbitrary
labels on zero-weight invalid/padded traces are harmless. Class may be String.
An actual source interpretation/physical-weight/classifier instance and
executable RNG/numeric refinement remain open. -/
theorem supported_trace_paper_class_probability [DecidableEq Class]
    (hf : ∀ s j, 0 ≤ factor s j) (ht : ∀ s, 0 ≤ terminal s)
    (hroot : 0 < partition b factor next terminal d s) (c : Class) :
    (∑ t : Trace b d, if contract.actualClassify t = c then
        traceProbability b factor next terminal d s t else 0) =
      (∑ r : Structure, if contract.paperClassify r = c then contract.paperWeight r else 0) /
        (∑ r : Structure, contract.paperWeight r) := by
  rw [supported_observable_probability b factor next terminal hf ht d s hroot,
    supported_paper_class_mass b factor next terminal d s contract hf ht c,
    supported_paper_normalizer b factor next terminal d s contract hf ht]

end SupportedTraceTransport

end UnifiedLean.Source.E8PaperObservableBridge

#print axioms UnifiedLean.Source.E8PaperObservableBridge.law_apply
#print axioms UnifiedLean.Source.E8PaperObservableBridge.finite_class_table
#print axioms UnifiedLean.Source.E8PaperObservableBridge.selected_class_probability
#print axioms UnifiedLean.Source.E8PaperObservableBridge.normalizer_preserved
#print axioms UnifiedLean.Source.E8PaperObservableBridge.classMass_preserved
#print axioms UnifiedLean.Source.E8PaperObservableBridge.source_selected_class_is_paper_mass
#print axioms UnifiedLean.Source.E8PaperObservableBridge.trace_weight_zero_outside_positive
#print axioms UnifiedLean.Source.E8PaperObservableBridge.sum_restrict_positive_traces
#print axioms UnifiedLean.Source.E8PaperObservableBridge.supported_paper_normalizer
#print axioms UnifiedLean.Source.E8PaperObservableBridge.supported_paper_class_mass
#print axioms UnifiedLean.Source.E8PaperObservableBridge.supported_trace_paper_class_probability
