/-
UNCHECKED DRAFT — Codex contracts role, 2026-10-09.
No compiler execution. Original Cloud retains compiler scheduling.
These generic contracts do not assert soundness of any Python/Rust primitive,
source admission, statistical coverage or whole-application equivalence.
-/
import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PracticalRelease.SoftwareCoverContracts

def Covers {S : Type*} (compatible cover : S → Prop) : Prop :=
  ∀ s, compatible s → cover s

-- One source fitting every row implies row-wise fits. The converse is absent.
theorem shared_source_implies_rowwise {S R : Type*} (fits : S → R → Prop)
    (h : ∃ s, ∀ r, fits s r) : ∀ r, ∃ s, fits s r := by
  obtain ⟨s, hs⟩ := h
  intro r
  exact ⟨s, hs r⟩

-- Replace one cell only after every compatible point in it is retained.
theorem replacement_retains_cover {S : Type*}
    (compatible rest old replacement : S → Prop)
    (hcover : Covers compatible (fun s => rest s ∨ old s))
    (hretain : ∀ s, compatible s → old s → replacement s) :
    Covers compatible (fun s => rest s ∨ replacement s) := by
  intro s hs
  rcases hcover s hs with hr | ho
  · exact Or.inl hr
  · exact Or.inr (hretain s hs ho)

-- UNKNOWN can conservatively widen a cover, including fallback to full D.
theorem widening_retains_cover {S : Type*}
    (compatible narrow wide : S → Prop) (hcover : Covers compatible narrow)
    (hwiden : ∀ s, narrow s → wide s) : Covers compatible wide := by
  intro s hs
  exact hwiden s (hcover s hs)

theorem closed_split_complete (lo mid hi x : ℚ)
    (hx : lo ≤ x ∧ x ≤ hi) :
    (lo ≤ x ∧ x ≤ mid) ∨ (mid ≤ x ∧ x ≤ hi) := by
  rcases le_total x mid with hm | hm
  · exact Or.inl ⟨hx.1, hm⟩
  · exact Or.inr ⟨hm, hx.2⟩

-- Every hull enclosing two witnessed points is at least their separation.
theorem two_points_force_width (lo hi p q : ℚ)
    (hp : lo ≤ p) (hq : q ≤ hi) : q - p ≤ hi - lo := by
  linarith

-- No enclosure retaining those witnesses can meet the requested tolerance.
theorem separation_prevents_tolerance (lo hi p q span target : ℚ)
    (hp : lo ≤ p) (hq : q ≤ hi)
    (hsep : span * target < q - p) : ¬ (hi - lo ≤ span * target) := by
  have hw := two_points_force_width lo hi p q hp hq
  linarith

-- This arithmetic fact does not prove that the archived points are sources
-- or that their means lie in the observed bands: audit_contracts.py checks
-- the saved rigorous enclosures; their provider contract remains explicit.
theorem archived_normalized_separation : (1 / 20 : ℚ) < 3 / 55 := by
  norm_num

theorem archived_physical_separation :
    ((6 - 1 / 2 : ℚ) * (1 / 20)) < 13 / 10 - 1 := by
  norm_num

end PracticalRelease.SoftwareCoverContracts
