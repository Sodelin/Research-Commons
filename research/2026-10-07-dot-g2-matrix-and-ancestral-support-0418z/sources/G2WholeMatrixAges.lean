import G2CompleteDecoration
import G2PairBirthFold
import G2ClockBoundaryNull

/-!
Deterministic whole-calendar first-birth/matrix bridge.
Contributor: dot (OpenAI), 7 October 2026.
Actual support and numerical chronology are separate source obligations.
-/
namespace GProgram.G2.WholeMatrixAges
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.SameClockContinuation GProgram.G2.ActualDecorationFold
open GProgram.G2.PairBirthFold GProgram.G2.CalendarDecoration
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompleteDecoration GProgram.G2.ChronologicalPathReadout
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def SegmentPairCoherent (N : RootedBinary V E X)
    {sample : Copy → X} (op : ProgramStep N) (s : Code N sample)
    (z : SegmentRecord N sample) (x y : Copy) : Prop :=
  match op with
  | .interval _ => PairTraceMonotone N (Fintype.card Copy) s z.1.2 x y ∧
      z.2 = recordEndpoint s (activeRecords z.1.2)
  | .boundary _ => ((state s).ancestor x = (state s).ancestor y ↔
      (state z.2).ancestor x = (state z.2).ancestor y)

noncomputable def CalendarPairCoherent (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → Code N sample →
      (Fin ops.length → SegmentRecord N sample) → Copy → Copy → Prop
  | [],_,_,_,_ => True
  | op::ops,s,past,x,y => SegmentPairCoherent N op s (past 0) x y ∧
      CalendarPairCoherent N ops (past 0).2 (Fin.tail past) x y

noncomputable def segmentFirstPairBirth (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ)
    (z : SegmentRecord N sample) (x y : Copy) : Option ℝ :=
  match op with
  | .interval _ => firstPairBirth N (Fintype.card Copy) s offset z.1.2 x y
  | .boundary _ => none

noncomputable def calendarFirstPairBirth (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → Code N sample → ℝ →
      (Fin ops.length → SegmentRecord N sample) → Copy → Copy → Option ℝ
  | [],_,_,_,_,_ => none
  | op::ops,s,offset,past,x,y =>
      (segmentFirstPairBirth N op s offset (past 0) x y).orElse
        (fun _ => calendarFirstPairBirth N ops (past 0).2
          (segmentOffset N op offset) (Fin.tail past) x y)

noncomputable def CompletePairCoherent (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (z : CompleteCalendarRecord N sample ops) (x y : Copy) : Prop :=
  CalendarPairCoherent N ops s z.2.1 x y ∧ z.1 = calendarEnd N ops s z.2.1 ∧
  PairTraceMonotone N (Fintype.card Copy) z.1 z.2.2.2 x y ∧
  traceEndpoint N (Fintype.card Copy) z.1 z.2.2.2 =
    recordEndpoint z.1 (activeRecords z.2.2.2)

noncomputable def completeFirstPairBirth (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (z : CompleteCalendarRecord N sample ops) (x y : Copy) : Option ℝ :=
  (calendarFirstPairBirth N ops s offset z.2.1 x y).orElse
    (fun _ => firstPairBirth N (Fintype.card Copy) z.1
      (offset+(programDuration N ops : ℝ)) z.2.2.2 x y)

lemma first_pair_birth_none_of_joined (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (offset : ℝ) (z : ClockTrace N sample n)
    (x y : Copy) (hm : PairTraceMonotone N n s z x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    firstPairBirth N n s offset z x y = none := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · have ht := hm
        simp only [PairTraceMonotone,if_pos ha] at ht
        have hn : ¬ ((state s).ancestor x ≠ (state s).ancestor y ∧
            (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y) := fun h => h.1 hs
        simpa only [firstPairBirth,if_pos ha,if_neg hn,Fin.tail_def] using
          ih (s := (z 0).2.2) (z := Fin.tail z) ht.2 (ht.1 hs)
      · have ht := hm
        simp only [PairTraceMonotone,if_neg ha] at ht
        simpa only [firstPairBirth,if_neg ha,Fin.tail_def] using
          ih (s := s) (z := Fin.tail z) ht hs

lemma segment_preserves_joined (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (z : SegmentRecord N sample)
    (x y : Copy) (hc : SegmentPairCoherent N op s z x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    (state z.2).ancestor x = (state z.2).ancestor y := by
  cases op with
  | interval h =>
      rw [hc.2]
      exact carried_endpoint_preserves_joined N _ s z.1.2 x y hc.1 hs
  | boundary b => exact hc.mp hs

lemma segment_matrix_preserves_joined (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (z : SegmentRecord N sample) (x y : Copy) (hc : SegmentPairCoherent N op s z x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    segmentMatrix N op s offset M z x y = M x y := by
  cases op with
  | interval h => exact fold_entry_preserved_of_joined N _ s offset M z.1.2 x y hc.1 hs
  | boundary b => rfl

lemma segment_matrix_entry (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (z : SegmentRecord N sample) (x y : Copy) (hc : SegmentPairCoherent N op s z x y) :
    segmentMatrix N op s offset M z x y =
      (segmentFirstPairBirth N op s offset z x y).getD (M x y) := by
  cases op with
  | interval h => exact fold_entry_eq_first_pair_birth N _ s offset M z.1.2 x y hc.1
  | boundary b => rfl

lemma segment_birth_exists_iff (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ)
    (z : SegmentRecord N sample) (x y : Copy) (hc : SegmentPairCoherent N op s z x y)
    (hs : (state s).ancestor x ≠ (state s).ancestor y) :
    (∃ a, segmentFirstPairBirth N op s offset z x y = some a) ↔
      (state z.2).ancestor x = (state z.2).ancestor y := by
  cases op with
  | interval h =>
      rw [hc.2]
      exact firstPairBirth_exists_iff_carried_endpoint N _ s offset z.1.2 x y hc.1 hs
  | boundary b => simp only [segmentFirstPairBirth,reduceCtorEq,false_and,exists_false]
                  exact iff_of_false (fun h => h) (fun h => hs (hc.mpr h))

lemma segment_birth_implies_joined (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (offset : ℝ)
    (z : SegmentRecord N sample) (x y : Copy) (hc : SegmentPairCoherent N op s z x y)
    {a : ℝ} (hb : segmentFirstPairBirth N op s offset z x y = some a) :
    (state z.2).ancestor x = (state z.2).ancestor y := by
  by_cases hs : (state s).ancestor x = (state s).ancestor y
  · exact segment_preserves_joined N op s z x y hc hs
  · exact (segment_birth_exists_iff N op s offset z x y hc hs).mp ⟨a,hb⟩

lemma calendar_preserves_joined (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample) (x y : Copy)
    (hc : CalendarPairCoherent N ops s past x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    (state (calendarEnd N ops s past)).ancestor x =
      (state (calendarEnd N ops s past)).ancestor y := by
  induction ops generalizing s with
  | nil => exact hs
  | cons op ops ih =>
      exact ih (s := (past 0).2) (past := Fin.tail past) hc.2
        (segment_preserves_joined N op s (past 0) x y hc.1 hs)

lemma calendar_matrix_preserves_joined (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (past : Fin ops.length → SegmentRecord N sample) (x y : Copy)
    (hc : CalendarPairCoherent N ops s past x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    calendarMatrix N ops s offset M past x y = M x y := by
  induction ops generalizing s offset M with
  | nil => rfl
  | cons op ops ih =>
      rw [calendarMatrix,ih _ _ _ _ hc.2
        (segment_preserves_joined N op s (past 0) x y hc.1 hs)]
      exact segment_matrix_preserves_joined N op s offset M (past 0) x y hc.1 hs

lemma calendar_birth_implies_joined (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (past : Fin ops.length → SegmentRecord N sample) (x y : Copy)
    (hc : CalendarPairCoherent N ops s past x y) {a : ℝ}
    (hb : calendarFirstPairBirth N ops s offset past x y = some a) :
    (state (calendarEnd N ops s past)).ancestor x =
      (state (calendarEnd N ops s past)).ancestor y := by
  induction ops generalizing s offset with
  | nil => cases hb
  | cons op ops ih =>
      cases hh : segmentFirstPairBirth N op s offset (past 0) x y with
      | none =>
          apply ih (s := (past 0).2) (offset := segmentOffset N op offset)
            (past := Fin.tail past) hc.2
          simpa only [calendarFirstPairBirth,hh,Option.orElse] using hb
      | some b =>
          exact calendar_preserves_joined N ops (past 0).2 (Fin.tail past) x y hc.2
            (segment_birth_implies_joined N op s offset (past 0) x y hc.1 hh)

theorem calendar_matrix_entry_eq_first_birth (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) (past : Fin ops.length → SegmentRecord N sample)
    (x y : Copy) (hc : CalendarPairCoherent N ops s past x y) :
    calendarMatrix N ops s offset M past x y =
      (calendarFirstPairBirth N ops s offset past x y).getD (M x y) := by
  induction ops generalizing s offset M with
  | nil => rfl
  | cons op ops ih =>
      have hm := segment_matrix_entry N op s offset M (past 0) x y hc.1
      cases hh : segmentFirstPairBirth N op s offset (past 0) x y with
      | none =>
          rw [hh] at hm
          simpa only [calendarMatrix,calendarFirstPairBirth,hh,Option.orElse,hm,Option.getD_none] using
            ih (s := (past 0).2) (offset := segmentOffset N op offset)
              (M := segmentMatrix N op s offset M (past 0)) (past := Fin.tail past) hc.2
      | some a =>
          have hj := segment_birth_implies_joined N op s offset (past 0) x y hc.1 hh
          rw [hh] at hm
          simp only [calendarMatrix,calendarFirstPairBirth,hh,Option.orElse,Option.getD_some]
          exact (calendar_matrix_preserves_joined N ops (past 0).2 _ _ (Fin.tail past) x y hc.2 hj).trans hm

theorem complete_matrix_entry_eq_first_birth (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) (z : CompleteCalendarRecord N sample ops)
    (x y : Copy) (hc : CompletePairCoherent N ops s z x y) :
    completeMatrix N ops s offset M z x y =
      (completeFirstPairBirth N ops s offset z x y).getD (M x y) := by
  have hm := calendar_matrix_entry_eq_first_birth N ops s offset M z.2.1 x y hc.1
  cases hh : calendarFirstPairBirth N ops s offset z.2.1 x y with
  | none =>
      rw [hh] at hm
      simpa only [completeMatrix,completeFirstPairBirth,hh,Option.orElse,hm,Option.getD_none] using
        fold_entry_eq_first_pair_birth N _ z.1 (offset+(programDuration N ops : ℝ))
          (calendarMatrix N ops s offset M z.2.1) z.2.2.2 x y hc.2.2.1
  | some a =>
      have hj : (state z.1).ancestor x = (state z.1).ancestor y := by
        rw [hc.2.1]
        exact calendar_birth_implies_joined N ops s offset z.2.1 x y hc.1 hh
      rw [hh] at hm
      simp only [completeMatrix,completeFirstPairBirth,hh,Option.orElse,Option.getD_some]
      exact (fold_entry_preserved_of_joined N _ z.1 _ _ z.2.2.2 x y hc.2.2.1 hj).trans hm

theorem complete_matrix_eq_first_birth_matrix (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (M : Copy → Copy → ℝ) (z : CompleteCalendarRecord N sample ops)
    (hc : ∀ x y : Copy, CompletePairCoherent N ops s z x y) :
    completeMatrix N ops s offset M z =
      fun x y => (completeFirstPairBirth N ops s offset z x y).getD (M x y) := by
  funext x y
  exact complete_matrix_entry_eq_first_birth N ops s offset M z x y (hc x y)

lemma calendar_birth_exists_iff_endpoint (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (past : Fin ops.length → SegmentRecord N sample) (x y : Copy)
    (hc : CalendarPairCoherent N ops s past x y)
    (hs : (state s).ancestor x ≠ (state s).ancestor y) :
    (∃ a, calendarFirstPairBirth N ops s offset past x y = some a) ↔
      (state (calendarEnd N ops s past)).ancestor x =
        (state (calendarEnd N ops s past)).ancestor y := by
  constructor
  · rintro ⟨a,ha⟩
    exact calendar_birth_implies_joined N ops s offset past x y hc ha
  · intro he
    induction ops generalizing s offset with
    | nil => exact False.elim (hs he)
    | cons op ops ih =>
        cases hh : segmentFirstPairBirth N op s offset (past 0) x y with
        | none =>
            have hd : (state (past 0).2).ancestor x ≠ (state (past 0).2).ancestor y := by
              intro hd
              obtain ⟨a,ha⟩ := (segment_birth_exists_iff N op s offset (past 0) x y hc.1 hs).mpr hd
              rw [hh] at ha
              cases ha
            obtain ⟨a,ha⟩ := ih (s := (past 0).2) (offset := segmentOffset N op offset)
              (past := Fin.tail past) hc.2 hd he
            exact ⟨a,by simpa only [calendarFirstPairBirth,hh,Option.orElse] using ha⟩
        | some a => exact ⟨a,by simp only [calendarFirstPairBirth,hh,Option.orElse]⟩

theorem complete_first_birth_exists_iff_endpoint (N : RootedBinary V E X)
    {sample : Copy → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (offset : ℝ) (z : CompleteCalendarRecord N sample ops) (x y : Copy)
    (hc : CompletePairCoherent N ops s z x y)
    (hs : (state s).ancestor x ≠ (state s).ancestor y) :
    (∃ a, completeFirstPairBirth N ops s offset z x y = some a) ↔
      (state (completeEnd N ops z)).ancestor x = (state (completeEnd N ops z)).ancestor y := by
  cases hh : calendarFirstPairBirth N ops s offset z.2.1 x y with
  | none =>
      have hd : (state z.1).ancestor x ≠ (state z.1).ancestor y := by
        intro hd
        rw [hc.2.1] at hd
        obtain ⟨a,ha⟩ := (calendar_birth_exists_iff_endpoint N ops s offset z.2.1 x y hc.1 hs).mpr hd
        rw [hh] at ha
        cases ha
      simpa only [completeFirstPairBirth,hh,Option.orElse,completeEnd,hc.2.2.2] using
        firstPairBirth_exists_iff_carried_endpoint N _ z.1
          (offset+(programDuration N ops : ℝ)) z.2.2.2 x y hc.2.2.1 hd
  | some a =>
      have hd : (state z.1).ancestor x = (state z.1).ancestor y := by
        rw [hc.2.1]
        exact calendar_birth_implies_joined N ops s offset z.2.1 x y hc.1 hh
      have he := carried_endpoint_preserves_joined N _ z.1 z.2.2.2 x y hc.2.2.1 hd
      constructor
      · intro _
        simpa only [completeEnd,hc.2.2.2] using he
      · intro _
        exact ⟨a,by simp only [completeFirstPairBirth,hh,Option.orElse]⟩

#print axioms first_pair_birth_none_of_joined
#print axioms segment_preserves_joined
#print axioms segment_matrix_entry
#print axioms calendar_preserves_joined
#print axioms calendar_matrix_preserves_joined
#print axioms calendar_birth_implies_joined
#print axioms calendar_matrix_entry_eq_first_birth
#print axioms complete_matrix_entry_eq_first_birth
#print axioms complete_matrix_eq_first_birth_matrix
#print axioms calendar_birth_exists_iff_endpoint
#print axioms complete_first_birth_exists_iff_endpoint
end GProgram.G2.WholeMatrixAges
