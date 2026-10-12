import G2PairBirthFold
import G2EpochHistoryReadout
import G2RationalAgeReadout
import Mathlib.Data.List.OfFn

/-!
Inclusive pair-birth thresholds in the original finite active records.
Contributor: dot (OpenAI), 7 October 2026.

The true cut predicate is derived from original flags, destinations and
ordered active ages before applying the countable-coordinate rational reader.
No birth refers only to this finite trace. An initially joined pair has reader
zero; its separate, supplied matrix seed age is not identified with zero.
-/
namespace GProgram.G2.PairBirthThreshold
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.PairBirthFold GProgram.G2.EpochHistoryReadout
open GProgram.G2.RationalAgeReadout
open scoped Classical NNReal ENNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

def ActiveAgeNonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (z : ClockTrace N sample n) : Prop :=
  ∀ i : Fin n, (z i).1 = true → 0 ≤ (z i).2.1

def ActiveAgeOrdered (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (z : ClockTrace N sample n) : Prop :=
  ∀ i j : Fin n, i < j → (z i).1 = true → (z j).1 = true →
    (z i).2.1 ≤ (z j).2.1

lemma active_age_ordered_tail (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (z : ClockTrace N sample (n+1)) (ho : ActiveAgeOrdered N (n+1) z) :
    ActiveAgeOrdered N n (Fin.tail z) := by
  intro i j hij hi hj
  exact ho i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij) hi hj

/-- The cut selects only the initial state and active destinations. -/
lemma cut_endpoint_preserves_predicate (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (u : ℝ) (s : Code N sample) (z : ClockTrace N sample n)
    (P : Code N sample → Prop) (hs : P s)
    (hz : ∀ i : Fin n, (z i).1 = true → P (z i).2.2) :
    P (cutEndpoint N n u s z) := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih =>
      by_cases h : (z 0).1 = true ∧ (z 0).2.1 ≤ u
      · simp only [cutEndpoint,if_pos h]
        exact ih (s := (z 0).2.2) (z := Fin.tail z) (hz 0 h.1)
          (fun i hi => hz i.succ hi)
      · simp only [cutEndpoint,if_neg h]
        exact ih (s := s) (z := Fin.tail z) hs (fun i hi => hz i.succ hi)

lemma active_destinations_joined (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (z : ClockTrace N sample n) (x y : Copy)
    (hm : PairTraceMonotone N n s z x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    ∀ i : Fin n, (z i).1 = true →
      (state (z i).2.2).ancestor x = (state (z i).2.2).ancestor y := by
  induction n generalizing s with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · simp only [PairTraceMonotone,if_pos ha] at hm
        intro i hi
        cases i using Fin.cases with
        | zero => exact hm.1 hs
        | succ i => exact ih (s := (z 0).2.2) (z := Fin.tail z) hm.2 (hm.1 hs) i hi
      · simp only [PairTraceMonotone,if_neg ha] at hm
        intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (ha hi)
        | succ i => exact ih (s := s) (z := Fin.tail z) hm hs i hi

lemma cut_pair_joined_of_initial (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (z : ClockTrace N sample n) (x y : Copy)
    (hm : PairTraceMonotone N n s z x y)
    (hs : (state s).ancestor x = (state s).ancestor y) (u : ℝ) :
    (state (cutEndpoint N n u s z)).ancestor x =
      (state (cutEndpoint N n u s z)).ancestor y :=
  cut_endpoint_preserves_predicate N n u s z
    (fun d => (state d).ancestor x = (state d).ancestor y) hs
    (active_destinations_joined N n s z x y hm hs)

lemma cut_endpoint_eq_initial_of_all_after (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample n)
    (u : ℝ) (hu : ∀ i : Fin n, (z i).1 = true → u < (z i).2.1) :
    cutEndpoint N n u s z = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have h : ¬ ((z 0).1 = true ∧ (z 0).2.1 ≤ u) :=
        fun h => (not_le_of_gt (hu 0 h.1)) h.2
      simp only [cutEndpoint,if_neg h]
      exact ih (s := s) (z := Fin.tail z) (fun i hi => hu i.succ hi)

lemma cut_endpoint_eq_initial_before_head (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample (n+1))
    (ho : ActiveAgeOrdered N (n+1) z) (ha : (z 0).1 = true)
    (u : ℝ) (hu : u < (z 0).2.1) : cutEndpoint N (n+1) u s z = s := by
  apply cut_endpoint_eq_initial_of_all_after
  intro i hi
  cases i using Fin.cases with
  | zero => exact hu
  | succ i => exact hu.trans_le (ho 0 i.succ (Fin.succ_pos i) ha hi)

lemma first_pair_birth_ge_head (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (z : ClockTrace N sample (n+1)) (x y : Copy)
    (a : ℝ) (ho : ActiveAgeOrdered N (n+1) z) (ha : (z 0).1 = true)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N (n+1) s 0 z x y = some a) : (z 0).2.1 ≤ a := by
  obtain ⟨i,hi,hage,_,_⟩ := firstPairBirth_first_active_index N (n+1) s 0 z x y a hs hb
  simp only [zero_add] at hage
  cases i using Fin.cases with
  | zero => exact le_of_eq hage.symm
  | succ i => exact (ho 0 i.succ (Fin.succ_pos i) ha hi).trans_eq hage.symm

/-- Order, persistence and the actual first-birth recursion determine the
inclusive threshold, even before imposing nonnegative active ages. -/
lemma cut_pair_birth_iff (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (z : ClockTrace N sample n) (x y : Copy) (a : ℝ)
    (hm : PairTraceMonotone N n s z x y) (ho : ActiveAgeOrdered N n z)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 z x y = some a) :
    ∀ u : ℝ, ((state (cutEndpoint N n u s z)).ancestor x =
      (state (cutEndpoint N n u s z)).ancestor y ↔ a ≤ u) := by
  induction n generalizing s with
  | zero => simp [firstPairBirth] at hb
  | succ n ih =>
      have hot := active_age_ordered_tail N n z ho
      by_cases ha : (z 0).1 = true
      · simp only [PairTraceMonotone,if_pos ha] at hm
        by_cases hd : (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y
        · have hbirth := And.intro hs hd
          have hage : a = (z 0).2.1 := by
            have he : 0+(z 0).2.1 = a := by
              simpa only [firstPairBirth,if_pos ha,if_pos hbirth,Option.some.injEq] using hb
            simpa only [zero_add] using he.symm
          subst a
          intro u
          by_cases hu : (z 0).2.1 ≤ u
          · have hc := cut_pair_joined_of_initial N n (z 0).2.2 (Fin.tail z) x y hm.2 hd u
            simp only [cutEndpoint,if_pos (And.intro ha hu)]
            exact iff_of_true hc hu
          · rw [cut_endpoint_eq_initial_before_head N n s z ho ha u (lt_of_not_ge hu)]
            exact iff_of_false hs hu
        · have hbirth : ¬ ((state s).ancestor x ≠ (state s).ancestor y ∧
              (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) := fun h => hd h.2
          have hbt : firstPairBirth N n (z 0).2.2 0 (Fin.tail z) x y = some a := by
            simpa only [firstPairBirth,if_pos ha,if_neg hbirth,Fin.tail_def] using hb
          intro u
          by_cases hu : (z 0).2.1 ≤ u
          · simpa only [cutEndpoint,if_pos (And.intro ha hu)] using
              ih (s := (z 0).2.2) (z := Fin.tail z) hm.2 hot hd hbt u
          · have hage := first_pair_birth_ge_head N n s z x y a ho ha hs hb
            rw [cut_endpoint_eq_initial_before_head N n s z ho ha u (lt_of_not_ge hu)]
            exact iff_of_false hs (fun h => hu (hage.trans h))
      · have hmt : PairTraceMonotone N n s (Fin.tail z) x y := by
          simpa only [PairTraceMonotone,if_neg ha,Fin.tail_def] using hm
        have hbt : firstPairBirth N n s 0 (Fin.tail z) x y = some a := by
          simpa only [firstPairBirth,if_neg ha,Fin.tail_def] using hb
        intro u
        have hcut : ¬ ((z 0).1 = true ∧ (z 0).2.1 ≤ u) := fun h => ha h.1
        simpa only [cutEndpoint,if_neg hcut] using
          ih (s := s) (z := Fin.tail z) hmt hot hs hbt u

theorem cut_pair_birth_threshold (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (z : ClockTrace N sample n) (x y : Copy) (a : ℝ)
    (hm : PairTraceMonotone N n s z x y) (hn : ActiveAgeNonnegative N n z)
    (ho : ActiveAgeOrdered N n z)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 z x y = some a) :
    0 ≤ a ∧ ∀ u : ℝ, ((state (cutEndpoint N n u s z)).ancestor x =
      (state (cutEndpoint N n u s z)).ancestor y ↔ a ≤ u) := by
  obtain ⟨i,hi,hage,_,_⟩ := firstPairBirth_first_active_index N n s 0 z x y a hs hb
  have hnonneg : 0 ≤ a := by rw [hage,zero_add]; exact hn i hi
  exact ⟨hnonneg,cut_pair_birth_iff N n s z x y a hm ho hs hb⟩

theorem rational_age_of_first_pair_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample n)
    (x y : Copy) (a : ℝ) (hm : PairTraceMonotone N n s z x y)
    (hn : ActiveAgeNonnegative N n z) (ho : ActiveAgeOrdered N n z)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 z x y = some a) :
    rationalAge (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
      (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s z) = ENNReal.ofReal a := by
  obtain ⟨ha,ht⟩ := cut_pair_birth_threshold N n s z x y a hm hn ho hs hb
  exact rational_age_of_threshold _ _ a ha
    (fun t hlt he => (not_le_of_gt hlt) ((ht (t : ℝ)).mp he))
    (fun t hlt => (ht (t : ℝ)).mpr hlt.le)

lemma active_destinations_separated_of_no_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample n)
    (x y : Copy) (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 z x y = none) :
    ∀ i : Fin n, (z i).1 = true →
      (state (z i).2.2).ancestor x ≠ (state (z i).2.2).ancestor y := by
  induction n generalizing s with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · have hd : (state (z 0).2.2).ancestor x ≠ (state (z 0).2.2).ancestor y := by
          intro he
          have hbad : some (0+(z 0).2.1) = (none : Option ℝ) := by
            simpa only [firstPairBirth,if_pos ha,if_pos (And.intro hs he)] using hb
          cases hbad
        have hbirth : ¬ ((state s).ancestor x ≠ (state s).ancestor y ∧
            (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) := fun h => hd h.2
        have hbt : firstPairBirth N n (z 0).2.2 0 (Fin.tail z) x y = none := by
          simpa only [firstPairBirth,if_pos ha,if_neg hbirth,Fin.tail_def] using hb
        intro i hi
        cases i using Fin.cases with
        | zero => exact hd
        | succ i => exact ih (s := (z 0).2.2) (z := Fin.tail z) hd hbt i hi
      · have hbt : firstPairBirth N n s 0 (Fin.tail z) x y = none := by
          simpa only [firstPairBirth,if_neg ha,Fin.tail_def] using hb
        intro i hi
        cases i using Fin.cases with
        | zero => exact False.elim (ha hi)
        | succ i => exact ih (s := s) (z := Fin.tail z) hs hbt i hi

/-- Infinity here concerns this supplied finite vector, not future extensions. -/
theorem rational_age_of_no_pair_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample n)
    (x y : Copy) (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 z x y = none) :
    rationalAge (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
      (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s z) = ⊤ := by
  apply rational_age_eq_top
  intro q _
  exact cut_endpoint_preserves_predicate N n _ s z
    (fun d => (state d).ancestor x ≠ (state d).ancestor y) hs
    (active_destinations_separated_of_no_birth N n s z x y hs hb)

/-- The reader's zero for an initially joined pair is not its historical
matrix seed age, which the separate fold theorem preserves unchanged. -/
theorem rational_age_of_initially_joined (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (s : Code N sample) (z : ClockTrace N sample n)
    (x y : Copy) (hm : PairTraceMonotone N n s z x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    rationalAge (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
      (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s z) = 0 := by
  have h := rational_age_of_threshold
    (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
    (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s z) 0 le_rfl
    (fun t ht => False.elim ((not_lt_of_ge t.property) ht))
    (fun t _ => cut_pair_joined_of_initial N n s z x y hm hs (t : ℝ))
  simpa only [ENNReal.ofReal_zero] using h

lemma actual_literal_active_nonnegative (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    ActiveAgeNonnegative N n (literalMarkedTrace N n H s c).2 := by
  intro i hi
  have hmem : ((literalMarkedTrace N n H s c).2 i) ∈ activeTrace N n H s c := by
    change _ ∈ (List.ofFn (literalMarkedTrace N n H s c).2).filter (fun r => r.1)
    exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩
  exact (activeTrace_mem_bounds N n H s c _ hmem).1

/-- The index/list bridge retains flags and original record order. The
accepted source chronology theorem is stronger than the regular-clock wrapper. -/
lemma actual_literal_active_ordered (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ) :
    ActiveAgeOrdered N n (literalMarkedTrace N n H s c).2 := by
  have h := activeTrace_strict_chronology N n H s c
  change ((List.ofFn (literalMarkedTrace N n H s c).2).filter
    (fun r => r.1)).Pairwise (fun r v => r.2.1 < v.2.1) at h
  have hi := List.pairwise_ofFn.mp (List.pairwise_filter.mp h)
  intro i j hij hai haj
  exact (hi hij hai haj).le

/-- Original regular-clock signature, including failed or short prefixes. -/
theorem actual_literal_cut_pair_birth_threshold (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (_hc : ClockRegular c) (x y : Copy) (a : ℝ)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 (literalMarkedTrace N n H s c).2 x y = some a) :
    0 ≤ a ∧ ∀ u : ℝ, ((state (cutEndpoint N n u s (literalMarkedTrace N n H s c).2)).ancestor x =
      (state (cutEndpoint N n u s (literalMarkedTrace N n H s c).2)).ancestor y ↔ a ≤ u) :=
  cut_pair_birth_threshold N n s _ x y a (actual_literal_pair_monotone N n H s c x y)
    (actual_literal_active_nonnegative N n H s c) (actual_literal_active_ordered N n H s c) hs hb

theorem actual_literal_rational_age_of_first_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (_hc : ClockRegular c) (x y : Copy) (a : ℝ)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 (literalMarkedTrace N n H s c).2 x y = some a) :
    rationalAge (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
      (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s (literalMarkedTrace N n H s c).2) =
        ENNReal.ofReal a :=
  rational_age_of_first_pair_birth N n s _ x y a (actual_literal_pair_monotone N n H s c x y)
    (actual_literal_active_nonnegative N n H s c) (actual_literal_active_ordered N n H s c) hs hb

theorem actual_literal_rational_age_of_no_birth (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (x y : Copy) (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : firstPairBirth N n s 0 (literalMarkedTrace N n H s c).2 x y = none) :
    rationalAge (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
      (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s (literalMarkedTrace N n H s c).2) = ⊤ :=
  rational_age_of_no_pair_birth N n s _ x y hs hb

theorem actual_literal_rational_age_of_initially_joined (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) (H : ℝ) (s : Code N sample) (c : Choice N s → ℝ)
    (x y : Copy) (hs : (state s).ancestor x = (state s).ancestor y) :
    rationalAge (fun d : Code N sample => (state d).ancestor x = (state d).ancestor y)
      (fun t : ℝ≥0 => cutEndpoint N n (t : ℝ) s (literalMarkedTrace N n H s c).2) = 0 :=
  rational_age_of_initially_joined N n s _ x y (actual_literal_pair_monotone N n H s c x y) hs

#print axioms cut_endpoint_preserves_predicate
#print axioms active_destinations_joined
#print axioms cut_pair_joined_of_initial
#print axioms cut_endpoint_eq_initial_before_head
#print axioms first_pair_birth_ge_head
#print axioms cut_pair_birth_iff
#print axioms cut_pair_birth_threshold
#print axioms rational_age_of_first_pair_birth
#print axioms active_destinations_separated_of_no_birth
#print axioms rational_age_of_no_pair_birth
#print axioms rational_age_of_initially_joined
#print axioms actual_literal_active_nonnegative
#print axioms actual_literal_active_ordered
#print axioms actual_literal_cut_pair_birth_threshold
#print axioms actual_literal_rational_age_of_first_birth
#print axioms actual_literal_rational_age_of_no_birth
#print axioms actual_literal_rational_age_of_initially_joined
end GProgram.G2.PairBirthThreshold
