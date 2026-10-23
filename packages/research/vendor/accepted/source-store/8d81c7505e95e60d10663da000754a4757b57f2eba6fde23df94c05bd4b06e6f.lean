import G2AncestralAgeCertificate
import G2ChronologicalTraceCompatibility

/-!
Numerical ages from the same complete calendar records.
Contributor: dot (OpenAI), 7 October 2026.
The original inclusive cut and strict interval-switch convention are retained.
This source is a working draft until its complete interface is frozen and checked.
-/
namespace GProgram.G2.CalendarFirstAge
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.MarkedTraceCuts
open GProgram.G2.ActualCalendarTrace GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.PairBirthFold GProgram.G2.PairBirthThreshold
open GProgram.G2.WholeMatrixAges GProgram.G2.AncestralAgeCertificate
open GProgram.G2.CalendarDecoration GProgram.G2.CompleteDecoration
open GProgram.G2.ActualPairCoalescence GProgram.G2.RationalAgeReadout
open scoped Classical NNReal ENNReal
variable {V E Copy X Q : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Exact historical bare-tail reader, through the already proved Bool adapter. -/
noncomputable abbrev recordPath (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) : ℝ≥0 → Code N sample :=
  ChronologicalTraceCompatibility.bareRecordPath N ops s past tail

lemma record_path_is_chronological [MeasurableSpace Q]
    (N : RootedBinary V E X) {sample : Copy → X} (f : Code N sample → Q)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (t : ℝ≥0) :
    ChronologicalPathReadout.chronologicalPath N ops
      (CalendarPathProjection.observeCalendar N f ops s past,
        CompleteEpochPath.completePath N f (calendarEnd N ops s past) (false,tail)) t =
      f (recordPath N ops s past tail t) :=
  ChronologicalTraceCompatibility.bare_record_path_is_chronological N f ops s past tail t

lemma first_pair_birth_translate (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (a b : ℝ) (z : ClockTrace N sample n) (x y : Copy) :
    firstPairBirth N n s (a+b) z x y =
      (firstPairBirth N n s b z x y).map (fun t => a+t) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      by_cases ha : (z 0).1 = true
      · by_cases hb : (state s).ancestor x ≠ (state s).ancestor y ∧
            (state (z 0).2.2).ancestor x = (state (z 0).2.2).ancestor y
        · simp only [firstPairBirth,if_pos ha,if_pos hb,Option.map_some,add_assoc]
        · simpa only [firstPairBirth,if_pos ha,if_neg hb,Fin.tail_def] using
            ih (s := (z 0).2.2) (z := Fin.tail z)
      · simpa only [firstPairBirth,if_neg ha,Fin.tail_def] using ih (s := s) (z := Fin.tail z)

lemma segment_offset_translate (N : RootedBinary V E X) (op : ProgramStep N) (a b : ℝ) :
    segmentOffset N op (a+b) = a+segmentOffset N op b := by
  cases op <;> simp only [segmentOffset,add_assoc]

lemma segment_birth_translate (N : RootedBinary V E X) {sample : Copy → X}
    (op : ProgramStep N) (s : Code N sample) (a b : ℝ)
    (z : SegmentRecord N sample) (x y : Copy) :
    segmentFirstPairBirth N op s (a+b) z x y =
      (segmentFirstPairBirth N op s b z x y).map (fun t => a+t) := by
  cases op with
  | interval h => exact first_pair_birth_translate N _ s a b z.1.2 x y
  | boundary _ => rfl

/-- A recursion following the chronological reader, with an arbitrary finite
ancestral trace after the calendar. It retains the original source offsets. -/
noncomputable def recordFirstPairBirth (N : RootedBinary V E X) {sample : Copy → X} :
    (ops : List (ProgramStep N)) → Code N sample → ℝ →
      (Fin ops.length → SegmentRecord N sample) →
      ClockTrace N sample (Fintype.card Copy) → Copy → Copy → Option ℝ
  | [],s,offset,_,tail,x,y => firstPairBirth N (Fintype.card Copy) s offset tail x y
  | op::ops,s,offset,past,tail,x,y =>
      (segmentFirstPairBirth N op s offset (past 0) x y).orElse (fun _ =>
        recordFirstPairBirth N ops (past 0).2 (segmentOffset N op offset)
          (Fin.tail past) tail x y)

lemma record_birth_translate (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (a b : ℝ)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (x y : Copy) :
    recordFirstPairBirth N ops s (a+b) past tail x y =
      (recordFirstPairBirth N ops s b past tail x y).map (fun t => a+t) := by
  induction ops generalizing s b with
  | nil => exact first_pair_birth_translate N _ s a b tail x y
  | cons op ops ih =>
      rw [recordFirstPairBirth,recordFirstPairBirth,segment_birth_translate]
      cases hb : segmentFirstPairBirth N op s b (past 0) x y with
      | none =>
          simp only [hb,Option.map_none,Option.orElse]
          rw [segment_offset_translate]
          exact ih (s := (past 0).2) (b := segmentOffset N op b) (past := Fin.tail past)
      | some t => simp only [hb,Option.map_some,Option.orElse]

lemma record_birth_as_calendar (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (x y : Copy) :
    recordFirstPairBirth N ops s offset past tail x y =
      (calendarFirstPairBirth N ops s offset past x y).orElse (fun _ =>
        firstPairBirth N (Fintype.card Copy) (calendarEnd N ops s past)
          (offset+(ChronologicalPathReadout.programDuration N ops : ℝ)) tail x y) := by
  induction ops generalizing s offset with
  | nil => simp only [recordFirstPairBirth,calendarFirstPairBirth,calendarEnd,
      ChronologicalPathReadout.programDuration,NNReal.coe_zero,add_zero,Option.orElse]
  | cons op ops ih =>
      cases op with
      | boundary b =>
          simpa only [recordFirstPairBirth,calendarFirstPairBirth,segmentFirstPairBirth,
            segmentOffset,calendarEnd,ChronologicalPathReadout.programDuration,Option.orElse] using
            ih (s := (past 0).2) (offset := offset) (past := Fin.tail past)
      | interval h =>
          cases hh : segmentFirstPairBirth N (.interval h) s offset (past 0) x y with
          | some a => simp only [recordFirstPairBirth,calendarFirstPairBirth,hh,Option.orElse]
          | none =>
              simp only [recordFirstPairBirth,calendarFirstPairBirth,hh,Option.orElse]
              simpa only [segmentOffset,calendarEnd,ChronologicalPathReadout.programDuration,
                NNReal.coe_add,add_assoc,Option.orElse] using
                ih (s := (past 0).2) (offset := offset+(h : ℝ)) (past := Fin.tail past)

lemma record_path_joined_of_initial (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (x y : Copy)
    (hc : CalendarPairCoherent N ops s past x y)
    (ht : PairTraceMonotone N (Fintype.card Copy) (calendarEnd N ops s past) tail x y)
    (hs : (state s).ancestor x = (state s).ancestor y) :
    ∀ t : ℝ≥0, (state (recordPath N ops s past tail t)).ancestor x =
      (state (recordPath N ops s past tail t)).ancestor y := by
  induction ops generalizing s with
  | nil =>
      intro t
      exact cut_pair_joined_of_initial N _ s tail x y ht hs (t : ℝ)
  | cons op ops ih =>
      have hn := segment_preserves_joined N op s (past 0) x y hc.1 hs
      have htt : PairTraceMonotone N (Fintype.card Copy)
          (calendarEnd N ops (past 0).2 (Fin.tail past)) tail x y := by
        simpa only [calendarEnd] using ht
      have hp := ih (s := (past 0).2) (past := Fin.tail past) hc.2 htt hn
      cases op with
      | boundary b => exact hp
      | interval h =>
          intro t
          by_cases hth : t < h
          · simpa only [recordPath,ChronologicalTraceCompatibility.bareRecordPath,
              ChronologicalPathReadout.recordPath,if_pos hth] using
              cut_pair_joined_of_initial N _ s (past 0).1.2 x y hc.1.1 hs (t : ℝ)
          · simpa only [recordPath,ChronologicalTraceCompatibility.bareRecordPath,
              ChronologicalPathReadout.recordPath,if_neg hth] using hp (t-h)

/-- The inclusive numerical threshold follows by following the exact reader
recursion. The tail remains a supplied finite vector in this deterministic theorem. -/
theorem record_birth_threshold (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample)
    (tail : ClockTrace N sample (Fintype.card Copy)) (x y : Copy) (a : ℝ)
    (hc : CalendarPairCoherent N ops s past x y)
    (ht : PairTraceMonotone N (Fintype.card Copy) (calendarEnd N ops s past) tail x y)
    (ha : CalendarAgeCertificate N ops past)
    (hn : ActiveAgeNonnegative N (Fintype.card Copy) tail)
    (ho : ActiveAgeOrdered N (Fintype.card Copy) tail)
    (hs : (state s).ancestor x ≠ (state s).ancestor y)
    (hb : recordFirstPairBirth N ops s 0 past tail x y = some a) :
    0 ≤ a ∧ ∀ t : ℝ≥0,
      ((state (recordPath N ops s past tail t)).ancestor x =
        (state (recordPath N ops s past tail t)).ancestor y ↔ a ≤ (t : ℝ)) := by
  induction ops generalizing s a with
  | nil =>
      obtain ⟨hna,hcut⟩ := cut_pair_birth_threshold N _ s tail x y a ht hn ho hs hb
      exact ⟨hna,fun t => hcut (t : ℝ)⟩
  | cons op ops ih =>
      have htt : PairTraceMonotone N (Fintype.card Copy)
          (calendarEnd N ops (past 0).2 (Fin.tail past)) tail x y := by
        simpa only [calendarEnd] using ht
      cases op with
      | boundary b =>
          have hs' : (state (past 0).2).ancestor x ≠ (state (past 0).2).ancestor y :=
            fun h => hs (hc.1.mpr h)
          have hb' : recordFirstPairBirth N ops (past 0).2 0 (Fin.tail past) tail x y = some a := by
            simpa only [recordFirstPairBirth,segmentFirstPairBirth,segmentOffset,Option.orElse] using hb
          exact ih (s := (past 0).2) (past := Fin.tail past) (a := a)
            hc.2 htt ha.2 hs' hb'
      | interval h =>
          cases hh : firstPairBirth N (Fintype.card Copy) s 0 (past 0).1.2 x y with
          | some b =>
              have hba : b = a := by
                simpa only [recordFirstPairBirth,segmentFirstPairBirth,hh,
                  Option.orElse,Option.some.injEq] using hb
              subst a
              obtain ⟨hbn,hcut⟩ := cut_pair_birth_threshold N _ s (past 0).1.2 x y b
                hc.1.1 ha.1.1 ha.1.2.1 hs hh
              have hbh : b ≤ (h : ℝ) := by
                obtain ⟨i,hi,hage,_,_⟩ := firstPairBirth_first_active_index N _ s 0
                  (past 0).1.2 x y b hs hh
                rw [hage,zero_add]
                exact ha.1.2.2 i hi
              have hj := segment_birth_implies_joined N (.interval h) s 0 (past 0) x y hc.1 hh
              have hp := record_path_joined_of_initial N ops (past 0).2 (Fin.tail past)
                tail x y hc.2 htt hj
              refine ⟨hbn,?_⟩
              intro t
              by_cases hth : t < h
              · simpa only [recordPath,ChronologicalTraceCompatibility.bareRecordPath,
                  ChronologicalPathReadout.recordPath,if_pos hth] using hcut (t : ℝ)
              · have hbt : b ≤ (t : ℝ) := hbh.trans (by exact_mod_cast (not_lt.mp hth))
                simpa only [recordPath,ChronologicalTraceCompatibility.bareRecordPath,
                  ChronologicalPathReadout.recordPath,if_neg hth] using iff_of_true (hp (t-h)) hbt
          | none =>
              have hs' : (state (past 0).2).ancestor x ≠ (state (past 0).2).ancestor y := by
                intro hj
                obtain ⟨b,hbirth⟩ := (segment_birth_exists_iff N (.interval h) s 0
                  (past 0) x y hc.1 hs).mpr hj
                change firstPairBirth N _ s 0 (past 0).1.2 x y = some b at hbirth
                rw [hh] at hbirth
                cases hbirth
              have hb' : recordFirstPairBirth N ops (past 0).2 (h : ℝ)
                  (Fin.tail past) tail x y = some a := by
                simpa only [recordFirstPairBirth,segmentFirstPairBirth,hh,
                  Option.orElse,segmentOffset,zero_add] using hb
              have hshift := record_birth_translate N ops (past 0).2 (h : ℝ) 0
                (Fin.tail past) tail x y
              cases hr : recordFirstPairBirth N ops (past 0).2 0 (Fin.tail past) tail x y with
              | none =>
                  simp only [add_zero,hr,Option.map_none] at hshift
                  rw [hshift] at hb'
                  cases hb'
              | some b =>
                  simp only [add_zero,hr,Option.map_some] at hshift
                  have hab : (h : ℝ)+b = a := Option.some.inj (hshift.symm.trans hb')
                  obtain ⟨hbn,hbt⟩ := ih (s := (past 0).2) (past := Fin.tail past) (a := b)
                    hc.2 htt ha.2 hs' hr
                  refine ⟨by linarith [h.property],?_⟩
                  intro t
                  by_cases hth : t < h
                  · have hsep := cut_endpoint_preserves_predicate N (Fintype.card Copy)
                      (t : ℝ) s (past 0).1.2
                      (fun d => (state d).ancestor x ≠ (state d).ancestor y) hs
                      (active_destinations_separated_of_no_birth N _ s (past 0).1.2 x y hs hh)
                    have hna : ¬ a ≤ (t : ℝ) := by
                      have ht' : (t : ℝ) < (h : ℝ) := by exact_mod_cast hth
                      linarith
                    simpa only [recordPath,ChronologicalTraceCompatibility.bareRecordPath,
                      ChronologicalPathReadout.recordPath,if_pos hth] using iff_of_false hsep hna
                  · have hle : h ≤ t := not_lt.mp hth
                    have he : b ≤ ((t-h : ℝ≥0) : ℝ) ↔ a ≤ (t : ℝ) := by
                      rw [NNReal.coe_sub hle]
                      constructor <;> intro hh <;> linarith
                    simpa only [recordPath,ChronologicalTraceCompatibility.bareRecordPath,
                      ChronologicalPathReadout.recordPath,if_neg hth] using (hbt (t-h)).trans he

lemma record_birth_as_complete (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (z : CompleteCalendarRecord N sample ops) (x y : Copy)
    (hz : z.1 = calendarEnd N ops s z.2.1) :
    recordFirstPairBirth N ops s offset z.2.1 z.2.2.2 x y =
      completeFirstPairBirth N ops s offset z x y := by
  rw [record_birth_as_calendar]
  simp only [completeFirstPairBirth,hz]

/-- Exact matrix/selected-path consumer signature. A finite elapsed age is
obtained from actual terminal pair support, then the threshold is proved.
Initially joined pairs are deliberately excluded here; their seed is preserved. -/
theorem complete_matrix_first_age (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ)
    (M : Copy → Copy → ℝ) (z : CompleteCalendarRecord N sample ops) (x y : Copy)
    (hz : CompleteAgeCertificate N
      (fun d => sameBlock (selectedView (state d) Finset.univ) x y) ops s z)
    (hs : ¬ sameBlock (selectedView (state s) Finset.univ) x y) :
    ∃ a : ℝ, 0 ≤ a ∧ completeMatrix N ops s offset M z x y = offset+a ∧
      rationalAge (fun d => sameBlock (selectedView (state d) Finset.univ) x y)
        (recordPath N ops s z.2.1 z.2.2.2) = ENNReal.ofReal a := by
  rcases hz with ⟨hst,hpair,hcal,hn,ho,hend⟩
  have hc := hpair x y
  have hs' : (state s).ancestor x ≠ (state s).ancestor y := by
    intro h
    exact hs ((selected_same_block (state s) s.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y)).mpr h)
  have he : (state (completeEnd N ops z)).ancestor x = (state (completeEnd N ops z)).ancestor y :=
    (selected_same_block (state (completeEnd N ops z)) (completeEnd N ops z).property.forest
      Finset.univ (Finset.mem_univ x) (Finset.mem_univ y)).mp hend
  obtain ⟨a,hbirth⟩ := (complete_first_birth_exists_iff_endpoint N ops s 0 z x y hc hs').mpr he
  have hrbirth : recordFirstPairBirth N ops s 0 z.2.1 z.2.2.2 x y = some a := by
    rw [record_birth_as_complete N ops s 0 z x y hst]
    exact hbirth
  have ht : PairTraceMonotone N (Fintype.card Copy) (calendarEnd N ops s z.2.1) z.2.2.2 x y := by
    rw [←hst]
    exact hc.2.2.1
  obtain ⟨hann,hth⟩ := record_birth_threshold N ops s z.2.1 z.2.2.2 x y a
    hc.1 ht hcal hn ho hs' hrbirth
  have hboff : completeFirstPairBirth N ops s offset z x y = some (offset+a) := by
    rw [←record_birth_as_complete N ops s offset z x y hst]
    simpa only [add_zero,hrbirth,Option.map_some] using
      record_birth_translate N ops s offset 0 z.2.1 z.2.2.2 x y
  have hm : completeMatrix N ops s offset M z x y = offset+a := by
    rw [complete_matrix_entry_eq_first_birth N ops s offset M z x y hc,hboff]
    rfl
  have hr : rationalAge (fun d => sameBlock (selectedView (state d) Finset.univ) x y)
      (recordPath N ops s z.2.1 z.2.2.2) = ENNReal.ofReal a := by
    apply rational_age_of_threshold _ _ a hann
    · intro t hlt hp
      have h := (selected_same_block
        (state (recordPath N ops s z.2.1 z.2.2.2 t))
        (recordPath N ops s z.2.1 z.2.2.2 t).property.forest Finset.univ
        (Finset.mem_univ x) (Finset.mem_univ y)).mp hp
      exact (not_le_of_gt hlt) ((hth t).mp h)
    · intro t hlt
      exact (selected_same_block
        (state (recordPath N ops s z.2.1 z.2.2.2 t))
        (recordPath N ops s z.2.1 z.2.2.2 t).property.forest Finset.univ
        (Finset.mem_univ x) (Finset.mem_univ y)).mpr ((hth t).mpr hlt.le)
  exact ⟨a,hann,hm,hr⟩

#print axioms record_path_is_chronological
#print axioms first_pair_birth_translate
#print axioms segment_offset_translate
#print axioms segment_birth_translate
#print axioms record_birth_translate
#print axioms record_birth_as_calendar
#print axioms record_path_joined_of_initial
#print axioms record_birth_threshold
#print axioms record_birth_as_complete
#print axioms complete_matrix_first_age
end GProgram.G2.CalendarFirstAge
