import UnifiedLean.G6.FiniteCorruptionBoundary

/-!
CLOUD-G6-SOL-ULTRA-20261007. Compiler UNCHECKED, outside179.
Class-level finite-law separation; original G6 hand proof supplies its
mathematical context. Closure, a closest law and finite-read impossibility
must not be silently replaced by pointwise actual-source separation.
-/
namespace UnifiedLean.G6.CorruptionClasses

open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.FiniteCorruptionBoundary
open scoped BigOperators Classical

variable {A : Type*} [Fintype A]

theorem pmfTV_self (p : PMF A) : pmfTV p p = 0 := by
  simp [pmfTV, tv]

theorem pmfTV_nonneg (p q : PMF A) : 0 ≤ pmfTV p q := by
  unfold pmfTV tv
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

/-- Closed TV output-error expansion of an explicitly given clean-law class.
This is an observed class, not a biological source construction. -/
def expanded (W : Set (PMF A)) (beta : ℝ) : Set (PMF A) :=
  {z | ∃ q ∈ W, pmfTV q z ≤ beta}

/-- Closure in finite TV, without assuming a PMF topology instance. -/
def tvClosure (W : Set (PMF A)) : Set (PMF A) :=
  {q | ∀ epsilon : ℝ, 0 < epsilon →
    ∃ r ∈ W, pmfTV q r < epsilon}

theorem mem_tvClosure {W : Set (PMF A)} {q : PMF A} (hq : q ∈ W) :
    q ∈ tvClosure W := by
  intro epsilon hepsilon
  exact ⟨q, hq, by simpa only [pmfTV_self] using hepsilon⟩

theorem tvClosure_monotone {W U : Set (PMF A)} (hWU : W ⊆ U) :
    tvClosure W ⊆ tvClosure U := by
  intro q hq epsilon hepsilon
  obtain ⟨r, hr, hqr⟩ := hq epsilon hepsilon
  exact ⟨r, hWU hr, hqr⟩

theorem tvClosure_idempotent (W : Set (PMF A)) :
    tvClosure (tvClosure W) = tvClosure W := by
  apply Set.Subset.antisymm
  · intro q hq epsilon hepsilon
    obtain ⟨r, hr, hqr⟩ := hq (epsilon / 2) (by linarith)
    obtain ⟨s, hs, hrs⟩ := hr (epsilon / 2) (by linarith)
    refine ⟨s, hs, ?_⟩
    have ht := pmfTV_triangle q r s
    linarith
  · exact tvClosure_monotone (fun _ h => mem_tvClosure h)

theorem tvClosure_empty : tvClosure (∅ : Set (PMF A)) = ∅ := by
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨r, hr, _⟩ := hq 1 (by norm_num)
    exact hr
  · exact Set.empty_subset _

/-- Every allowed observed law at p avoids every corrupted law of W. -/
def allCorruptionsSeparated (p : PMF A) (W : Set (PMF A)) (beta : ℝ) : Prop :=
  ∀ z : PMF A, pmfTV p z ≤ beta → z ∉ expanded W beta

/-- For an arbitrary class, exact disjointness is a pointwise statement.
For robust certification W must be the WRONG CLOSURE class, not raw images. -/
theorem all_corruptions_separated_iff (p : PMF A)
    (W : Set (PMF A)) (beta : ℝ) :
    allCorruptionsSeparated p W beta ↔
      ∀ q ∈ W, 2 * beta < pmfTV p q := by
  constructor
  · intro h q hq
    apply (no_shared_corruption_iff p q beta).mp
    rintro ⟨z, hpz, hqz⟩
    exact h z hpz ⟨q, hq, hqz⟩
  · intro h z hpz
    rintro ⟨q, hq, hqz⟩
    exact (no_shared_corruption_iff p q beta).mpr (h q hq) ⟨z, hpz, hqz⟩

theorem shared_wrong_corruption_iff (p : PMF A)
    (W : Set (PMF A)) (beta : ℝ) :
    (∃ z : PMF A, pmfTV p z ≤ beta ∧ z ∈ expanded W beta) ↔
      ∃ q ∈ W, pmfTV p q ≤ 2 * beta := by
  constructor
  · rintro ⟨z, hpz, q, hq, hqz⟩
    exact ⟨q, hq, (shared_corruption_iff p q beta).mp ⟨z, hpz, hqz⟩⟩
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨z, hpz, hqz⟩ := (shared_corruption_iff p q beta).mpr hpq
    exact ⟨z, hpz, q, hq, hqz⟩

/-- Explicit attainment hypothesis, never stored in a biological source.
Compact closure/attainment is a separate obligation for a numerical distance. -/
theorem closest_wrong_class_boundary (p closest : PMF A)
    (W : Set (PMF A)) (beta : ℝ) (hc : closest ∈ W)
    (hmin : ∀ q ∈ W, pmfTV p closest ≤ pmfTV p q) :
    allCorruptionsSeparated p W beta ↔ 2 * beta < pmfTV p closest := by
  rw [all_corruptions_separated_iff]
  constructor
  · exact fun h => h closest hc
  · intro h q hq
    exact lt_of_lt_of_le h (hmin q hq)

/-- Equality is on the ambiguity side when a closest wrong law is attained. -/
theorem closest_wrong_equality_overlaps (p closest : PMF A)
    (W : Set (PMF A)) (beta : ℝ) (hc : closest ∈ W)
    (heq : pmfTV p closest = 2 * beta) :
    ∃ z : PMF A, pmfTV p z ≤ beta ∧ z ∈ expanded W beta := by
  exact (shared_wrong_corruption_iff p W beta).mpr ⟨closest, hc, heq.le⟩

#print axioms pmfTV_self
#print axioms pmfTV_nonneg
#print axioms mem_tvClosure
#print axioms tvClosure_monotone
#print axioms tvClosure_idempotent
#print axioms tvClosure_empty
#print axioms all_corruptions_separated_iff
#print axioms shared_wrong_corruption_iff
#print axioms closest_wrong_class_boundary
#print axioms closest_wrong_equality_overlaps

end UnifiedLean.G6.CorruptionClasses
