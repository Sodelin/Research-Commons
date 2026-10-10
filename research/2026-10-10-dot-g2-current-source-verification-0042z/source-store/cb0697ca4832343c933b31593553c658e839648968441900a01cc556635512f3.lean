import G2ActualDecorationFold
import G2SameClockContinuation

/-!
# First pair births in the original active records

Contributor: dot (OpenAI), 7 October 2026. New deterministic reconstruction.
The source ancestry, Bool flags, ages, destinations and matrix fold are the
existing ones. First means first in record order, without imposing chronology
on arbitrary raw ages. Original merge_never_splits supplies the actual-source
premise. No probability, rational-age, success or regular-clock law is assumed.
-/

namespace GProgram.G2.PairBirthFold
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.SourceGraftDecoration
open GProgram.G2.ActualDecorationFold GProgram.G2.MarkedTraceCuts
open GProgram.G2.SameClockContinuation
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Only equality of the chosen pair is required to persist across active
transitions. Inactive destinations are ignored. -/
noncomputable def PairTraceMonotone (N : RootedBinary V E X)
    {sample : Copy → X} :
    (n : Nat) → Code N sample → ClockTrace N sample n → Copy → Copy → Prop
  | 0, _, _, _, _ => True
  | n+1, s, z, x, y =>
      if (z 0).1 = true then
        (((state s).ancestor x = (state s).ancestor y →
          (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) ∧
          PairTraceMonotone N n (z 0).2.2 (fun i => z i.succ) x y)
      else PairTraceMonotone N n s (fun i => z i.succ) x y

/-- First newly joining active record, with the original absolute-age offset.
For an already joined initial pair, the source monotonicity premise ensures
that no new birth occurs. Arbitrary splitting raw vectors need not do so. -/
noncomputable def firstPairBirth (N : RootedBinary V E X)
    {sample : Copy → X} :
    (n : Nat) → Code N sample → ℝ → ClockTrace N sample n →
      Copy → Copy → Option ℝ
  | 0, _, _, _, _, _ => none
  | n+1, s, offset, z, x, y =>
      if (z 0).1 = true then
        if (state s).ancestor x ≠ (state s).ancestor y ∧
            (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y then
          some (offset + (z 0).2.1)
        else firstPairBirth N n (z 0).2.2 offset (fun i => z i.succ) x y
      else firstPairBirth N n s offset (fun i => z i.succ) x y

lemma pair_monotone_empty (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (x y : Copy) :
    PairTraceMonotone N n s (emptyTrace N n s) x y := by
  induction n with
  | zero => trivial
  | succ n ih =>
      change PairTraceMonotone N n s (emptyTrace N n s) x y
      exact ih

lemma pair_monotone_shift_ages (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (age : ℝ) (z : ClockTrace N sample n)
    (x y : Copy) :
    PairTraceMonotone N n s (shiftTraceAges N age z) x y ↔
      PairTraceMonotone N n s z x y := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · simp only [PairTraceMonotone,shiftTraceAges,if_pos ha]
        exact and_congr Iff.rfl (ih (s := (z 0).2.2) (z := fun i => z i.succ))
      · simp only [PairTraceMonotone,shiftTraceAges,if_neg ha]
        exact ih (s := s) (z := fun i => z i.succ)

lemma pair_monotone_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s d : Code N sample) (age : ℝ) (z : ClockTrace N sample n)
    (x y : Copy) :
    PairTraceMonotone N (n+1) s (prependTrace N age d z) x y ↔
      (((state s).ancestor x = (state s).ancestor y →
        (state d).ancestor x = (state d).ancestor y) ∧
        PairTraceMonotone N n d z x y) := by
  change (((state s).ancestor x = (state s).ancestor y →
      (state d).ancestor x = (state d).ancestor y) ∧
      PairTraceMonotone N n d (shiftTraceAges N age z) x y) ↔ _
  exact and_congr Iff.rfl (pair_monotone_shift_ages N n d age z x y)

/-- Original source merger monotonicity, transported through the exact
coded destination ancestor fields. -/
lemma actual_step_never_splits (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (x y : Copy)
    (hxy : (state s).ancestor x = (state s).ancestor y) :
    (state (stepDestination N s (some p))).ancestor x =
      (state (stepDestination N s (some p))).ancestor y := by
  change (merge (state s) p.2.val.1 p.2.val.2).ancestor x =
    (merge (state s) p.2.val.1 p.2.val.2).ancestor y
  exact merge_never_splits (state s) p.2.val.1 p.2.val.2 hxy

theorem actual_literal_pair_monotone (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ) (x y : Copy) :
    PairTraceMonotone N n s (literalMarkedTrace N n H s c).2 x y := by
  induction n generalizing H s with
  | zero => trivial
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, H < c p
      · simpa only [literalMarkedTrace,if_pos hstop] using
          pair_monotone_empty N (n+1) s x y
      · simp only [literalMarkedTrace,if_neg hstop]
        cases hw : selectedWinner c with
        | none => exact pair_monotone_empty N (n+1) s x y
        | some p =>
            by_cases hp : c p ≤ H
            · simp only [if_pos hp,pair_monotone_prepend]
              exact ⟨actual_step_never_splits N s p x y,
                ih (H := H-c p) (s := stepDestination N s (some p))
                  (c := fun q => c (destinationClockEmbedding N s p q).val-c p)⟩
            · simpa only [if_neg hp] using pair_monotone_empty N (n+1) s x y

theorem fold_entry_preserved_of_joined (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) (z : ClockTrace N sample n)
    (x y : Copy) (hm : PairTraceMonotone N n s z x y)
    (hxy : (state s).ancestor x = (state s).ancestor y) :
    foldMatrix N n s offset M z x y = M x y := by
  induction n generalizing s M with
  | zero => rfl
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · have hm' := (show
            ((state s).ancestor x = (state s).ancestor y →
              (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) ∧
              PairTraceMonotone N n (z 0).2.2 (fun i => z i.succ) x y from
            by simpa only [PairTraceMonotone,if_pos ha] using hm)
        simp only [foldMatrix,if_pos ha]
        exact (ih (s := (z 0).2.2)
          (M := codedAgeUpdate N s (z 0).2.2 (offset+(z 0).2.1) M)
          (z := fun i => z i.succ) hm'.2 (hm'.1 hxy)).trans
            (by simp [codedAgeUpdate,hxy])
      · have ht : PairTraceMonotone N n s (fun i => z i.succ) x y := by
          simpa only [PairTraceMonotone,if_neg ha] using hm
        simpa only [foldMatrix,if_neg ha] using
          ih (s := s) (M := M) (z := fun i => z i.succ) ht hxy

theorem fold_entry_eq_first_pair_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) (z : ClockTrace N sample n)
    (x y : Copy) (hm : PairTraceMonotone N n s z x y) :
    foldMatrix N n s offset M z x y =
      (firstPairBirth N n s offset z x y).getD (M x y) := by
  induction n generalizing s M with
  | zero => rfl
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · have ht : PairTraceMonotone N n (z 0).2.2 (fun i => z i.succ) x y := by
          exact (show _ ∧ _ from by simpa only [PairTraceMonotone,if_pos ha] using hm).2
        by_cases hb : (state s).ancestor x ≠ (state s).ancestor y ∧
            (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y
        · simp only [foldMatrix,firstPairBirth,if_pos ha,if_pos hb,Option.getD_some]
          have hp := fold_entry_preserved_of_joined N n (z 0).2.2 offset
            (codedAgeUpdate N s (z 0).2.2 (offset+(z 0).2.1) M)
            (fun i => z i.succ) x y ht hb.2
          simpa only [codedAgeUpdate,if_pos hb] using hp
        · simp only [foldMatrix,firstPairBirth,if_pos ha,if_neg hb]
          rw [ih (s := (z 0).2.2)
            (M := codedAgeUpdate N s (z 0).2.2 (offset+(z 0).2.1) M)
            (z := fun i => z i.succ) ht]
          simp only [codedAgeUpdate,if_neg hb]
      · have ht : PairTraceMonotone N n s (fun i => z i.succ) x y := by
          simpa only [PairTraceMonotone,if_neg ha] using hm
        simpa only [foldMatrix,firstPairBirth,if_neg ha] using
          ih (s := s) (M := M) (z := fun i => z i.succ) ht

theorem actual_literal_fold_entry_eq_first_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ) (offset : ℝ) (M : Copy → Copy → ℝ) (x y : Copy) :
    foldMatrix N n s offset M (literalMarkedTrace N n H s c).2 x y =
      (firstPairBirth N n s offset (literalMarkedTrace N n H s c).2 x y).getD (M x y) :=
  fold_entry_eq_first_pair_birth N n s offset M _ x y
    (actual_literal_pair_monotone N n H s c x y)

/-- The first-index witness requires initial separation, but does not need
monotonicity of later raw destinations or ordering of their real ages. -/
theorem firstPairBirth_first_active_index (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (offset : ℝ)
    (z : ClockTrace N sample n) (x y : Copy) (age : ℝ)
    (hxy : (state s).ancestor x ≠ (state s).ancestor y)
    (h : firstPairBirth N n s offset z x y = some age) :
    ∃ i : Fin n, (z i).1 = true ∧ age = offset+(z i).2.1 ∧
      (state (z i).2.2).ancestor x = (state (z i).2.2).ancestor y ∧
      ∀ j : Fin n, j < i → (z j).1 = true →
        (state (z j).2.2).ancestor x ≠ (state (z j).2.2).ancestor y := by
  induction n generalizing s with
  | zero => simp [firstPairBirth] at h
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · by_cases hb : (state s).ancestor x ≠ (state s).ancestor y ∧
            (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y
        · have hag : offset+(z 0).2.1 = age := by
            simpa only [firstPairBirth,if_pos ha,if_pos hb,Option.some.injEq] using h
          refine ⟨0,ha,hag.symm,hb.2,?_⟩
          intro j hj _
          exact False.elim (Fin.not_lt_zero j hj)
        · have hd : (state (z 0).2.2).ancestor x ≠
              (state (z 0).2.2).ancestor y := fun he => hb ⟨hxy,he⟩
          have ht : firstPairBirth N n (z 0).2.2 offset
              (fun i => z i.succ) x y = some age := by
            simpa only [firstPairBirth,if_pos ha,if_neg hb] using h
          obtain ⟨i,hi,hage,heq,hprev⟩ := ih (s := (z 0).2.2)
            (z := fun i => z i.succ) hd ht
          refine ⟨i.succ,hi,hage,heq,?_⟩
          intro j hj hjactive
          cases j using Fin.cases with
          | zero => exact hd
          | succ j => exact hprev j (Fin.succ_lt_succ_iff.mp hj) hjactive
      · have ht : firstPairBirth N n s offset (fun i => z i.succ) x y = some age := by
          simpa only [firstPairBirth,if_neg ha] using h
        obtain ⟨i,hi,hage,heq,hprev⟩ := ih (s := s) (z := fun i => z i.succ) hxy ht
        refine ⟨i.succ,hi,hage,heq,?_⟩
        intro j hj hjactive
        cases j using Fin.cases with
        | zero => exact False.elim (ha hjactive)
        | succ j => exact hprev j (Fin.succ_lt_succ_iff.mp hj) hjactive

/-- The already accepted active-list endpoint is used on arbitrary raw
vectors; no equality with their last padded destination is asserted. -/
lemma carried_endpoint_succ (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (z : ClockTrace N sample (n+1)) :
    recordEndpoint s (activeRecords z) =
      if (z 0).1 = true then
        recordEndpoint (z 0).2.2 (activeRecords (fun i : Fin n => z i.succ))
      else recordEndpoint s (activeRecords (fun i : Fin n => z i.succ)) := by
  by_cases ha : (z 0).1 = true <;>
    simp [activeRecords,List.ofFn_succ,recordEndpoint,ha]

lemma carried_endpoint_preserves_joined (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample n)
    (x y : Copy) (hm : PairTraceMonotone N n s z x y)
    (hxy : (state s).ancestor x = (state s).ancestor y) :
    (state (recordEndpoint s (activeRecords z))).ancestor x =
      (state (recordEndpoint s (activeRecords z))).ancestor y := by
  induction n generalizing s with
  | zero => simpa [activeRecords,recordEndpoint] using hxy
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · simp only [carried_endpoint_succ,if_pos ha]
        have hm' := (show
            ((state s).ancestor x = (state s).ancestor y →
              (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) ∧
              PairTraceMonotone N n (z 0).2.2 (fun i => z i.succ) x y from
            by simpa only [PairTraceMonotone,if_pos ha] using hm)
        exact ih (s := (z 0).2.2) (z := fun i => z i.succ) hm'.2 (hm'.1 hxy)
      · simp only [carried_endpoint_succ,if_neg ha]
        have ht : PairTraceMonotone N n s (fun i => z i.succ) x y := by
          simpa only [PairTraceMonotone,if_neg ha] using hm
        exact ih (s := s) (z := fun i => z i.succ) ht hxy

theorem firstPairBirth_exists_iff_carried_endpoint (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (offset : ℝ)
    (z : ClockTrace N sample n) (x y : Copy)
    (hm : PairTraceMonotone N n s z x y)
    (hxy : (state s).ancestor x ≠ (state s).ancestor y) :
    (∃ age : ℝ, firstPairBirth N n s offset z x y = some age) ↔
      (state (recordEndpoint s (activeRecords z))).ancestor x =
        (state (recordEndpoint s (activeRecords z))).ancestor y := by
  induction n generalizing s with
  | zero => simp [firstPairBirth,activeRecords,recordEndpoint,hxy]
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · have ht : PairTraceMonotone N n (z 0).2.2 (fun i => z i.succ) x y := by
          exact (show _ ∧ _ from by simpa only [PairTraceMonotone,if_pos ha] using hm).2
        by_cases hd : (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y
        · have hb := And.intro hxy hd
          have hend := carried_endpoint_preserves_joined N n (z 0).2.2
            (fun i => z i.succ) x y ht hd
          constructor
          · intro _
            simpa only [carried_endpoint_succ,if_pos ha] using hend
          · intro _
            exact ⟨offset+(z 0).2.1,by simp only [firstPairBirth,if_pos ha,if_pos hb]⟩
        · have hb : ¬ ((state s).ancestor x ≠ (state s).ancestor y ∧
              (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) :=
            fun h => hd h.2
          simpa only [firstPairBirth,if_pos ha,if_neg hb,carried_endpoint_succ] using
            ih (s := (z 0).2.2) (z := fun i => z i.succ) ht hd
      · have ht : PairTraceMonotone N n s (fun i => z i.succ) x y := by
          simpa only [PairTraceMonotone,if_neg ha] using hm
        simpa only [firstPairBirth,if_neg ha,carried_endpoint_succ] using
          ih (s := s) (z := fun i => z i.succ) ht hxy

/-- Physical endpoint specialization uses the accepted literal active-list
bridge, including failed/incomplete prefixes, rather than a padding claim. -/
theorem actual_first_pair_birth_iff_endpoint (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample)
    (c : Choice N s → ℝ) (offset : ℝ) (x y : Copy)
    (hxy : (state s).ancestor x ≠ (state s).ancestor y) :
    (∃ age : ℝ, firstPairBirth N n s offset (literalMarkedTrace N n H s c).2 x y = some age) ↔
      (state (traceEndpoint N n s (literalMarkedTrace N n H s c).2)).ancestor x =
        (state (traceEndpoint N n s (literalMarkedTrace N n H s c).2)).ancestor y := by
  simp only [actual_trace_endpoint_fold N n H s c]
  exact firstPairBirth_exists_iff_carried_endpoint N n s offset _ x y
    (actual_literal_pair_monotone N n H s c x y) hxy

#print axioms actual_step_never_splits
#print axioms actual_literal_pair_monotone
#print axioms fold_entry_preserved_of_joined
#print axioms fold_entry_eq_first_pair_birth
#print axioms actual_literal_fold_entry_eq_first_birth
#print axioms firstPairBirth_first_active_index
#print axioms carried_endpoint_preserves_joined
#print axioms firstPairBirth_exists_iff_carried_endpoint
#print axioms actual_first_pair_birth_iff_endpoint

end GProgram.G2.PairBirthFold
