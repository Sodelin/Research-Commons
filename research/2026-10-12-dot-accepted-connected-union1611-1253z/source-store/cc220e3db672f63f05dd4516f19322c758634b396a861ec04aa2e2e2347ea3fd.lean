import UnifiedLean.G6.BinHistory
import G2ActualDecorationFold

/-!
UNCHECKED root draft, 7 October 2026. Pointwise finite-tag coarsening of the
inherited actual clock-record fold. No law/menu/source-admission claim.
-/
namespace UnifiedLean.G6.BinFold
open Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualDecorationFold
open UnifiedLean.G6.BinHistory
open scoped Classical

variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def foldTags (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) : (n : ℕ) → Code N sample → ℝ → (Copy → Copy → Tag) →
      ClockTrace N sample n → (Copy → Copy → Tag)
  | 0, _, _, M, _ => M
  | n+1, s, offset, M, z =>
      if (z 0).1 = true then
        foldTags N bin n (z 0).2.2 offset
          (tagUpdate N s (z 0).2.2 (bin (offset+(z 0).2.1)) M)
          (fun i => z i.succ)
      else foldTags N bin n s offset M (fun i => z i.succ)

/-- All old tags and all genuine new tags are the quotient of the SAME real-age fold. -/
theorem map_actual_age_fold (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (n : ℕ) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (z : ClockTrace N sample n) :
    (fun x y => bin (foldMatrix N n s offset M z x y)) =
      foldTags N bin n s offset (fun x y => bin (M x y)) z := by
  induction n generalizing s offset M with
  | zero => rfl
  | succ n ih =>
      by_cases h : (z 0).1 = true
      · simp only [foldMatrix, foldTags, if_pos h]
        rw [ih, map_coded_age_update]
      · simp only [foldMatrix, foldTags, if_neg h]
        exact ih s offset M (fun i => z i.succ)

/-- Replace actual ages by one bin only when every ACTIVE record has that bin.
Inactive padding has no premise and writes no tag. -/
theorem bin_constant_active_fold (N : RootedBinary V E X) {sample : Copy → X}
    (bin : ℝ → Tag) (tag : Tag) (n : ℕ) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → Tag) (z : ClockTrace N sample n)
    (hbin : ∀ i, (z i).1 = true → bin (offset+(z i).2.1) = tag) :
    foldTags N bin n s offset M z = foldTags N (fun _ => tag) n s offset M z := by
  induction n generalizing s M with
  | zero => rfl
  | succ n ih =>
      have htail : ∀ i : Fin n, (z i.succ).1 = true →
          bin (offset+(z i.succ).2.1) = tag := fun i hi => hbin i.succ hi
      by_cases h : (z 0).1 = true
      · simp only [foldTags, if_pos h, hbin 0 h]
        exact ih (z 0).2.2 _ (fun i => z i.succ) htail
      · simp only [foldTags, if_neg h]
        exact ih s M (fun i => z i.succ) htail

#print axioms map_actual_age_fold
#print axioms bin_constant_active_fold
end UnifiedLean.G6.BinFold
