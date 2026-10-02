import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Fintype.BigOperators

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

end UnifiedLean.Source.E8PaperObservableBridge

#print axioms UnifiedLean.Source.E8PaperObservableBridge.law_apply
#print axioms UnifiedLean.Source.E8PaperObservableBridge.finite_class_table
#print axioms UnifiedLean.Source.E8PaperObservableBridge.selected_class_probability
#print axioms UnifiedLean.Source.E8PaperObservableBridge.normalizer_preserved
#print axioms UnifiedLean.Source.E8PaperObservableBridge.classMass_preserved
#print axioms UnifiedLean.Source.E8PaperObservableBridge.source_selected_class_is_paper_mass
