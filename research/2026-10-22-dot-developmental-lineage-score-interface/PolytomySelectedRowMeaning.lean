/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact selected-row meaning of the actual outer loop's mathematical fold.
An empty selected row is selected once and returns no membership; later
rows cannot substitute for it. Out-of-range selection returns no hit.
-/
import PolytomySelectedRowsOuter

namespace PolytomyReductionModel

def selectedRowMembership (C : ℕ) : ℕ → List (List ℕ) → Bool
  | _, [] => false
  | 0, row :: _ => decide (C ∈ row)
  | n + 1, _ :: rows => selectedRowMembership C n rows

theorem selectedRowStep_eq (C i : ℕ) (f : SelectedRowFrame) (row : List ℕ) :
    selectedRowStep C (i, f) row =
      (i - 1, ⟨f.found || ((!f.chosen && decide (i = 0)) && decide (C ∈ row)),
        f.chosen || decide (i = 0), !f.chosen && decide (i = 0)⟩) := by
  simp only [selectedRowStep, selectedRow_fold, selectedRowStart]

theorem selectedRowFold_found (C : ℕ) (rows : List (List ℕ)) : ∀ i f,
    (rows.foldl (selectedRowStep C) (i, f)).2.found =
      f.found || (!f.chosen && selectedRowMembership C i rows) := by
  induction rows with
  | nil => intro i f; simp [selectedRowMembership]
  | cons row rows ih =>
      intro i f
      cases i with
      | zero =>
          rw [List.foldl_cons, selectedRowStep_eq, ih]
          rcases f with ⟨found, chosen, active⟩
          cases found <;> cases chosen <;> simp [selectedRowMembership]
      | succ i =>
          rw [List.foldl_cons, selectedRowStep_eq, ih]
          simp [selectedRowMembership]

theorem selectedRowMembership_get (C : ℕ) (rows : List (List ℕ)) : ∀ n (hn : n < rows.length),
    selectedRowMembership C n rows = decide (C ∈ rows.get ⟨n, hn⟩) := by
  induction rows with
  | nil => intro n hn; simp at hn
  | cons row rows ih =>
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
          simpa only [selectedRowMembership] using ih n (Nat.lt_of_succ_lt_succ hn)

theorem selectedRowMembership_oob (C : ℕ) (rows : List (List ℕ)) : ∀ n,
    rows.length ≤ n → selectedRowMembership C n rows = false := by
  induction rows with
  | nil => intro n hn; rfl
  | cons row rows ih =>
      intro n hn
      cases n with
      | zero => simp at hn
      | succ n => exact ih n (Nat.le_of_succ_le_succ hn)

theorem selectedRowFold_original (C : ℕ) (rows : List (List ℕ)) (i : Fin rows.length) :
    (rows.foldl (selectedRowStep C) (i.val, ⟨false, false, false⟩)).2.found =
      decide (C ∈ rows.get i) := by
  rw [selectedRowFold_found, selectedRowMembership_get C rows i.val i.isLt]
  simp

/- This identifies the actual fold with the ORIGINAL List.get row used
by rawRowMember. It does not replace that predicate with membership in
rows.flatten. The original n<N guard and shared marker threshold must
still be implemented/joined by the full canonical membership controller.
-/

end PolytomyReductionModel
