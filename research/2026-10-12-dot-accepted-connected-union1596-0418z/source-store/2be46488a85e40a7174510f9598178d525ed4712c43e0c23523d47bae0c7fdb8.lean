import E8TracebackCallRanks
import E8MidpointProductionKernel
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.NormNum

/-!
Concrete Sample_V loop-domain bound for the pinned public PRISM source.
The literal inner lower limit forces u1+u2 <= MAXLOOP; at MAXLOOP=30
there are at most 496 distinct internal (k,l) candidates and 498 slots
including the optional hairpin and multiloop. The source loops visit each
(k,l) once in ordinary unbounded-integer semantics. Formal C++ vector-loop
refinement, index overflow and floating branch weights are not claimed.
-/
noncomputable section
namespace E8SourceVBranchBound
open E8TracebackCallRanks E8MidpointProductionKernel
open scoped BigOperators

def unpairedCells (M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (M + 1)).biUnion Finset.antidiagonal

theorem unpairedCells_mem (M u1 u2 : ℕ) (h : u1 + u2 ≤ M) :
    (u1, u2) ∈ unpairedCells M := by
  apply Finset.mem_biUnion.mpr
  refine ⟨u1 + u2, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_antidiagonal.mpr rfl

theorem unpairedCells_card_le (M : ℕ) :
    (unpairedCells M).card ≤ ∑ r ∈ Finset.range (M + 1), (r + 1) := by
  unfold unpairedCells
  have h := Finset.card_biUnion_le (s := Finset.range (M + 1)) (t := Finset.antidiagonal)
  simpa only [Finset.Nat.card_antidiagonal] using h

theorem unpairedCells_thirty_card : (unpairedCells 30).card ≤ 496 := by
  calc
    _ ≤ ∑ r ∈ Finset.range 31, (r + 1) := unpairedCells_card_le 30
    _ = 496 := by norm_num [Finset.sum_range_succ]

/-- The second operand of the literal max lower limit enforces the loop budget. -/
theorem sampleV_loop_budget (i j k l turn maxloop : ℤ)
    (hl : sampleVMinL i j k turn maxloop ≤ l) :
    (k - i - 1) + (j - l - 1) ≤ maxloop := by
  have hm := le_max_right (k + turn + 1 + maxloop + 2) (k + j - i)
  unfold sampleVMinL at hl
  omega

def encodeUnpaired (i j : ℤ) (p : ℤ × ℤ) : ℕ × ℕ :=
  ((p.1 - i - 1).toNat, (j - p.2 - 1).toNat)

theorem internal_candidate_card_le (i j turn : ℤ) (M : ℕ) (cases : Finset (ℤ × ℤ))
    (hcases : ∀ p ∈ cases, i + 1 ≤ p.1 ∧
      sampleVMinL i j p.1 turn M ≤ p.2 ∧ p.2 ≤ j - 1) :
    cases.card ≤ (unpairedCells M).card := by
  apply Finset.card_le_card_of_injOn (encodeUnpaired i j)
  · intro p hp
    obtain ⟨hk, hl, hupper⟩ := hcases p hp
    have hbudget := sampleV_loop_budget i j p.1 p.2 turn M hl
    apply unpairedCells_mem
    omega
  · intro p hp q hq heq
    obtain ⟨hpk, _, hpl⟩ := hcases p hp
    obtain ⟨hqk, _, hql⟩ := hcases q hq
    have hs := Prod.ext_iff.mp heq
    dsimp [encodeUnpaired] at hs
    apply Prod.ext <;> omega

theorem sampleV_internal_candidates_le496 (i j turn : ℤ) (cases : Finset (ℤ × ℤ))
    (hcases : ∀ p ∈ cases, i + 1 ≤ p.1 ∧
      sampleVMinL i j p.1 turn 30 ≤ p.2 ∧ p.2 ≤ j - 1) :
    cases.card ≤ 496 :=
  le_trans (internal_candidate_card_le i j turn 30 cases hcases) unpairedCells_thirty_card

theorem sampleV_slots_le498 (i j turn : ℤ) (cases : Finset (ℤ × ℤ))
    (hcases : ∀ p ∈ cases, i + 1 ≤ p.1 ∧
      sampleVMinL i j p.1 turn 30 ≤ p.2 ∧ p.2 ≤ j - 1) :
    cases.card + 2 ≤ 498 := by
  have h := sampleV_internal_candidates_le496 i j turn cases hcases
  omega

/-- Once the executed branch-vector length is refined to the checked 498-slot
bound, the exact-real midpoint-grid local TV has this concrete constant. -/
theorem sampleV_grid_kernel_bound {b : ℕ} (hb : b ≤ 498)
    (N : ℕ) (hN : 0 < N) (weight : Fin b → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hW : 0 < ∑ j, weight j) :
    (∑ j, |gridKernel N weight hW j - weight j / (∑ k, weight k)|) / 2 ≤
      497 / (2 * N) := by
  have h := gridKernel_TV N hN weight hw hW
  have hNr : (0 : ℝ) ≤ 2 * N := by positivity
  have hb' : ((b - 1 : ℕ) : ℝ) ≤ 497 := by exact_mod_cast (show b - 1 ≤ 497 by omega)
  exact le_trans h (div_le_div_of_nonneg_right hb' hNr)

end E8SourceVBranchBound
#print axioms E8SourceVBranchBound.sampleV_loop_budget
#print axioms E8SourceVBranchBound.internal_candidate_card_le
#print axioms E8SourceVBranchBound.sampleV_internal_candidates_le496
#print axioms E8SourceVBranchBound.sampleV_slots_le498
#print axioms E8SourceVBranchBound.sampleV_grid_kernel_bound
