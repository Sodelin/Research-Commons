import G2LiteralMarkedClockTrace

/-!
# Deterministic active-record cuts of the actual marked clock trace

Contributor: dot (OpenAI), 2026-10-06. New phase04 source. The only owned
import is frozen phase01 G2LiteralMarkedClockTrace. No phase02/03 law,
projectivity premise, or independently resampled clock is used.

Inactive padding is removed before comparing traces: prependTrace shifts
every padded age, but an inactive record is never an event. The raw active
prefix statements below are stronger than the regular sufficient-budget
corollaries. They assert no success flag for a pathological or short-budget
trace. Exact same-clock retained-coordinate recursion is preserved.
-/

namespace GProgram.G2.MarkedTraceCuts
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def shiftRecord {S : Type*} (a : ℝ) (r : Bool × ℝ × S) : Bool × ℝ × S :=
  (r.1,a+r.2.1,r.2.2)

def activeRecords {N : RootedBinary V E X} {sample : Copy → X} {n : Nat}
    (z : ClockTrace N sample n) : List (Bool × ℝ × Code N sample) :=
  (List.ofFn z).filter (fun r => r.1)

noncomputable def cutRecords {S : Type*} (u : ℝ)
    (l : List (Bool × ℝ × S)) : List (Bool × ℝ × S) :=
  l.filter (fun r => decide (r.2.1 ≤ u))

noncomputable def activeTrace (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    List (Bool × ℝ × Code N sample) :=
  activeRecords (literalMarkedTrace N n t s c).2

@[simp] theorem activeRecords_empty (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) : activeRecords (emptyTrace N n s) = [] := by
  unfold activeRecords
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  simp [emptyTrace]

@[simp] theorem activeRecords_prepend (N : RootedBinary V E X) {sample : Copy → X}
    {n : Nat} (a : ℝ) (d : Code N sample) (z : ClockTrace N sample n) :
    activeRecords (prependTrace N a d z) =
      (true,a,d) :: (activeRecords z).map (shiftRecord a) := by
  have hlist : List.ofFn (prependTrace N a d z) =
      (true,a,d) :: (List.ofFn z).map (shiftRecord a) := by
    rw [List.ofFn_succ,List.map_ofFn]
    rfl
  rw [activeRecords,hlist,List.filter_cons,List.filter_map]
  rfl

@[simp] theorem activeTrace_zero (N : RootedBinary V E X) {sample : Copy → X}
    (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    activeTrace N 0 t s c = [] := by
  simp [activeTrace,literalMarkedTrace]

/-- Horizon-independent winner dispatch for the literal recorded active prefix. -/
theorem activeTrace_succ (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    activeTrace N (n+1) t s c =
      match selectedWinner c with
      | none => []
      | some p => if c p ≤ t then
          (true,c p,stepDestination N s (some p)) ::
            (activeTrace N n (t-c p) (stepDestination N s (some p))
              (fun q => c (destinationClockEmbedding N s p q).val-c p)).map
                (shiftRecord (c p))
        else [] := by
  cases hp : selectedWinner c with
  | none =>
      by_cases hs : ∀ q : Choice N s, t < c q <;>
        simp [activeTrace,literalMarkedTrace,hs,hp]
  | some p =>
      simp only
      by_cases ht : c p ≤ t
      · have hs : ¬ ∀ q : Choice N s, t < c q := by
          intro h
          exact (not_lt_of_ge ht) (h p)
        simp [activeTrace,literalMarkedTrace,hs,hp,ht]
      · by_cases hs : ∀ q : Choice N s, t < c q <;>
          simp [activeTrace,literalMarkedTrace,hs,hp,ht]

/-- Recorded active ages are nonnegative and do not exceed their horizon,
even when the raw trace has an unsuccessful or exhausted-budget flag. -/
theorem activeTrace_mem_bounds (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    ∀ r ∈ activeTrace N n t s c, 0 ≤ r.2.1 ∧ r.2.1 ≤ t := by
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
      rw [activeTrace_succ]
      cases hp : selectedWinner c with
      | none => simp
      | some p =>
          simp only
          by_cases ht : c p ≤ t
          · rw [if_pos ht]
            have hw := (selectedWinner_eq_some_iff c p).mp hp
            intro r hr
            rcases List.mem_cons.mp hr with he | hr
            · subst r
              exact ⟨hw.1,ht⟩
            · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
              have hb := ih (t := t-c p) (s := stepDestination N s (some p))
                (c := fun q => c (destinationClockEmbedding N s p q).val-c p) v hv
              dsimp [shiftRecord]
              constructor <;> linarith [hw.1]
          · simp [ht]

/-- A strict lower bound on every initial coordinate is inherited by every
active age; no hidden clock readout or extra source law is assumed. -/
theorem activeTrace_mem_gt (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (a : ℝ) (ha : ∀ p, a < c p) :
    ∀ r ∈ activeTrace N n t s c, a < r.2.1 := by
  cases n with
  | zero => simp
  | succ n =>
      rw [activeTrace_succ]
      cases hp : selectedWinner c with
      | none => simp
      | some p =>
          simp only
          by_cases ht : c p ≤ t
          · rw [if_pos ht]
            intro r hr
            rcases List.mem_cons.mp hr with he | hr
            · subst r
              exact ha p
            · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
              have hb := (activeTrace_mem_bounds N n (t-c p)
                (stepDestination N s (some p))
                (fun q => c (destinationClockEmbedding N s p q).val-c p) v hv).1
              dsimp [shiftRecord]
              linarith [ha p]
          · simp [ht]

/-- Every retained destination clock is strictly later than the selected
winner. This is the unchanged original coordinate embedding. -/
lemma selected_retained_residual_pos (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) (p : Choice N s)
    (hp : selectedWinner c = some p) :
    ∀ q : Choice N (stepDestination N s (some p)),
      0 < c (destinationClockEmbedding N s p q).val-c p := by
  intro q
  exact sub_pos.mpr (((selectedWinner_eq_some_iff c p).mp hp).2
    (destinationClockEmbedding N s p q))

theorem activeTrace_strict_chronology (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    (activeTrace N n t s c).Pairwise (fun r v => r.2.1 < v.2.1) := by
  induction n generalizing s t with
  | zero => simp
  | succ n ih =>
      rw [activeTrace_succ]
      cases hp : selectedWinner c with
      | none => simp
      | some p =>
          simp only
          by_cases ht : c p ≤ t
          · rw [if_pos ht]
            apply List.pairwise_cons.mpr
            constructor
            · intro r hr
              obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
              have hvpos := activeTrace_mem_gt N n (t-c p)
                (stepDestination N s (some p))
                (fun q => c (destinationClockEmbedding N s p q).val-c p) 0
                (selected_retained_residual_pos N s c p hp) v hv
              dsimp [shiftRecord]
              linarith
            · apply List.pairwise_map.mpr
              apply (ih (t := t-c p) (s := stepDestination N s (some p))
                (c := fun q => c (destinationClockEmbedding N s p q).val-c p)).imp
              intro v w h
              dsimp [shiftRecord]
              linarith
          · simp [ht]

@[simp] theorem cutRecords_nil {S : Type*} (u : ℝ) :
    cutRecords u ([] : List (Bool × ℝ × S)) = [] := rfl

theorem cutRecords_cons {S : Type*} (u : ℝ) (r : Bool × ℝ × S)
    (l : List (Bool × ℝ × S)) :
    cutRecords u (r::l) = if r.2.1 ≤ u then r::cutRecords u l else cutRecords u l := by
  by_cases h : r.2.1 ≤ u <;> simp [cutRecords,h]

theorem cutRecords_shift {S : Type*} (u a : ℝ) (l : List (Bool × ℝ × S)) :
    cutRecords u (l.map (shiftRecord a)) =
      (cutRecords (u-a) l).map (shiftRecord a) := by
  induction l with
  | nil => simp
  | cons r l ih =>
      by_cases h : r.2.1 ≤ u-a
      · have h' : (shiftRecord a r).2.1 ≤ u := by dsimp [shiftRecord]; linarith
        simp [List.map_cons,cutRecords_cons,h,h',ih]
      · have h' : ¬ (shiftRecord a r).2.1 ≤ u := by
          dsimp [shiftRecord]
          intro hh
          apply h
          linarith
        simp [List.map_cons,cutRecords_cons,h,h',ih]

theorem cutRecords_shift_eq_nil {S : Type*} (u a : ℝ) (l : List (Bool × ℝ × S))
    (hu : u < a) (hl : ∀ r ∈ l, 0 ≤ r.2.1) :
    cutRecords u (l.map (shiftRecord a)) = [] := by
  unfold cutRecords
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
  have hv0 := hl v hv
  have h : ¬ (shiftRecord a v).2.1 ≤ u := by dsimp [shiftRecord]; linarith
  simpa using h

/-- The two horizons use the same original clocks and the same recursively
retained destination coordinates. This is an exact list identity. -/
theorem activeTrace_horizon_restriction (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (u t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (hut : u ≤ t) :
    activeTrace N n u s c = cutRecords u (activeTrace N n t s c) := by
  induction n generalizing s u t with
  | zero => simp
  | succ n ih =>
      rw [activeTrace_succ,activeTrace_succ]
      cases hp : selectedWinner c with
      | none => simp
      | some p =>
          simp only
          by_cases hu : c p ≤ u
          · have ht : c p ≤ t := le_trans hu hut
            rw [if_pos hu,if_pos ht,cutRecords_cons,if_pos hu,cutRecords_shift]
            have hrec := ih (u := u-c p) (t := t-c p)
              (s := stepDestination N s (some p))
              (c := fun q => c (destinationClockEmbedding N s p q).val-c p)
              (sub_le_sub_right hut (c p))
            rw [hrec]
          · by_cases ht : c p ≤ t
            · rw [if_neg hu,if_pos ht,cutRecords_cons,if_neg hu]
              symm
              apply cutRecords_shift_eq_nil u (c p) _ (lt_of_not_ge hu)
              intro r hr
              exact (activeTrace_mem_bounds N n (t-c p)
                (stepDestination N s (some p))
                (fun q => c (destinationClockEmbedding N s p q).val-c p) r hr).1
            · simp [hu,ht]

/-- Requested regular, sufficient-budget same-clock cut. No conclusion is
drawn about shifted inactive padding or a separately initialized clock law. -/
theorem regular_active_records_horizon_restriction
    (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (u t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (_hc : ClockRegular c) (_hn : liveCard s ≤ n) (_hu : 0 ≤ u) (hut : u ≤ t) :
    activeRecords (literalMarkedTrace N n u s c).2 =
      (activeRecords (literalMarkedTrace N n t s c).2).filter
        (fun r => decide (r.2.1 ≤ u)) := by
  simpa only [activeTrace,cutRecords] using
    activeTrace_horizon_restriction N n u t s c hut

/-- Strictly increasing ages of actual active records. An initial age zero
is allowed by ClockRegular; every later retained age is strictly larger. -/
theorem regular_active_ages_strict (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (t : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (_hc : ClockRegular c) (_hn : liveCard s ≤ n) (_ht : 0 ≤ t) :
    ((activeRecords (literalMarkedTrace N n t s c).2).map (fun r => r.2.1)).Pairwise
      (fun a b => a < b) := by
  apply List.pairwise_map.mpr
  exact activeTrace_strict_chronology N n t s c

#print axioms activeRecords_empty
#print axioms activeRecords_prepend
#print axioms activeTrace_zero
#print axioms activeTrace_succ
#print axioms activeTrace_mem_bounds
#print axioms activeTrace_mem_gt
#print axioms selected_retained_residual_pos
#print axioms activeTrace_strict_chronology
#print axioms cutRecords_nil
#print axioms cutRecords_cons
#print axioms cutRecords_shift
#print axioms cutRecords_shift_eq_nil
#print axioms activeTrace_horizon_restriction
#print axioms regular_active_records_horizon_restriction
#print axioms regular_active_ages_strict

end GProgram.G2.MarkedTraceCuts
