import G7OriginalCompletedCalendarRoot

/-!
# Same-bank physical calendar law for the three literal completed controls

Contributor: Codex / solver_design, 2026-10-10.
DRAFT: no kernel/audit acceptance asserted. Consumes the exact finite phase
Perm wrappers, oldest original-date sorting/program composition and actual
natural register law, then the existing full selected completion consumer.
The physical slot durations are the consecutive ORIGINAL date differences.
Same-phase PMF equality is used pointwise for every entering Code; operation
list equality under choice-based Finset.toList is never assumed. No independent
multi-slot physical cube, numerical exponential evaluation, native parser or
universal calendar refinement is introduced.
-/
namespace UnifiedLean.G7.OriginalCompletedCalendarLaw
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open GProgram.G7.BoundaryPhasePermutation
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.SparseRowProducts
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.EffectiveCompletedWordCoefficients
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.CompletedCalendarPolynomial
open UnifiedLean.G7.OriginalWordFixture UnifiedLean.G7.OriginalCompletedCalendarFixture
open UnifiedLean.G7.OriginalCompletedCalendarPhases
open UnifiedLean.G7.OriginalCompletedCalendarRoot
open scoped Classical NNReal

variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

private theorem sorted_dates_of_membership {V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (dates : List ℝ)
    (hn : dates.Nodup) (ho : dates.Pairwise (· ≤ ·))
    (hm : ∀ a : ℝ, a ∈ dates ↔ ∃ v : V, C.age v = a) :
    sortedOriginalDates N C = dates := by
  have he : originalDates N C = dates.toFinset := by
    ext a
    simpa only [originalDates,Finset.mem_image,Finset.mem_univ,true_and,List.mem_toFinset]
      using (hm a).symm
  change (originalDates N C).sort (· ≤ ·) = dates
  rw [he]
  exact (List.toFinset_sort (r := (· ≤ ·)) hn).mpr ho

theorem twoTip_sorted_dates : sortedOriginalDates N2 twoTipCalendar = ([0,2] : List ℝ) := by
  apply sorted_dates_of_membership N2 twoTipCalendar [0,2]
    (by norm_num [List.nodup_cons,List.mem_cons,List.not_mem_nil])
    (by norm_num [List.pairwise_cons,List.mem_cons,List.not_mem_nil])
  intro a
  constructor
  · intro ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with h0 | h1
    · subst a
      refine ⟨(1 : Fin 3),?_⟩
      change ((twoTipAge (1 : Fin 3) : Rat) : ℝ) = 0
      have hage : twoTipAge (1 : Fin 3) = 0 := by decide
      rw [hage] <;> norm_num
    · subst a
      refine ⟨(0 : Fin 3),?_⟩
      change ((twoTipAge (0 : Fin 3) : Rat) : ℝ) = 2
      have hage : twoTipAge (0 : Fin 3) = 2 := by decide
      rw [hage] <;> norm_num
  · rintro ⟨v,rfl⟩
    fin_cases v
    · change ((twoTipAge (0 : Fin 3) : Rat) : ℝ) ∈ [0,2]
      have hage : twoTipAge (0 : Fin 3) = 2 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((twoTipAge (1 : Fin 3) : Rat) : ℝ) ∈ [0,2]
      have hage : twoTipAge (1 : Fin 3) = 0 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((twoTipAge (2 : Fin 3) : Rat) : ℝ) ∈ [0,2]
      have hage : twoTipAge (2 : Fin 3) = 0 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]

theorem serial_sorted_dates : sortedOriginalDates N2 serialCalendar = ([(-3 / 2),(1 / 4),(3 / 2)] : List ℝ) := by
  apply sorted_dates_of_membership N2 serialCalendar [(-3 / 2),(1 / 4),(3 / 2)]
    (by norm_num [List.nodup_cons,List.mem_cons,List.not_mem_nil])
    (by norm_num [List.pairwise_cons,List.mem_cons,List.not_mem_nil])
  intro a
  constructor
  · intro ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with h0 | h1 | h2
    · subst a
      refine ⟨(1 : Fin 3),?_⟩
      change ((serialAge (1 : Fin 3) : Rat) : ℝ) = (-3 / 2)
      have hage : serialAge (1 : Fin 3) = -3 / 2 := by
        rw [serialAge,if_neg (show (1 : Fin 3) ≠ 0 by decide),if_pos rfl]
      rw [hage] <;> norm_num
    · subst a
      refine ⟨(2 : Fin 3),?_⟩
      change ((serialAge (2 : Fin 3) : Rat) : ℝ) = (1 / 4)
      have hage : serialAge (2 : Fin 3) = 1 / 4 := by
        rw [serialAge,if_neg (show (2 : Fin 3) ≠ 0 by decide),
          if_neg (show (2 : Fin 3) ≠ 1 by decide)]
      rw [hage] <;> norm_num
    · subst a
      refine ⟨(0 : Fin 3),?_⟩
      change ((serialAge (0 : Fin 3) : Rat) : ℝ) = (3 / 2)
      have hage : serialAge (0 : Fin 3) = 3 / 2 := by
        rw [serialAge,if_pos rfl]
      rw [hage] <;> norm_num
  · rintro ⟨v,rfl⟩
    fin_cases v
    · change ((serialAge (0 : Fin 3) : Rat) : ℝ) ∈ [(-3 / 2),(1 / 4),(3 / 2)]
      have hage : serialAge (0 : Fin 3) = 3 / 2 := by
        rw [serialAge,if_pos rfl]
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((serialAge (1 : Fin 3) : Rat) : ℝ) ∈ [(-3 / 2),(1 / 4),(3 / 2)]
      have hage : serialAge (1 : Fin 3) = -3 / 2 := by
        rw [serialAge,if_neg (show (1 : Fin 3) ≠ 0 by decide),if_pos rfl]
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((serialAge (2 : Fin 3) : Rat) : ℝ) ∈ [(-3 / 2),(1 / 4),(3 / 2)]
      have hage : serialAge (2 : Fin 3) = 1 / 4 := by
        rw [serialAge,if_neg (show (2 : Fin 3) ≠ 0 by decide),
          if_neg (show (2 : Fin 3) ≠ 1 by decide)]
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]

theorem parallel_sorted_dates : sortedOriginalDates NP parallelCalendar = ([0,1,2,3] : List ℝ) := by
  apply sorted_dates_of_membership NP parallelCalendar [0,1,2,3]
    (by norm_num [List.nodup_cons,List.mem_cons,List.not_mem_nil])
    (by norm_num [List.pairwise_cons,List.mem_cons,List.not_mem_nil])
  intro a
  constructor
  · intro ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with h0 | h1 | h2 | h3
    · subst a
      refine ⟨(1 : Fin 5),?_⟩
      change ((parallelAge (1 : Fin 5) : Rat) : ℝ) = 0
      have hage : parallelAge (1 : Fin 5) = 0 := by decide
      rw [hage] <;> norm_num
    · subst a
      refine ⟨(3 : Fin 5),?_⟩
      change ((parallelAge (3 : Fin 5) : Rat) : ℝ) = 1
      have hage : parallelAge (3 : Fin 5) = 1 := by decide
      rw [hage] <;> norm_num
    · subst a
      refine ⟨(2 : Fin 5),?_⟩
      change ((parallelAge (2 : Fin 5) : Rat) : ℝ) = 2
      have hage : parallelAge (2 : Fin 5) = 2 := by decide
      rw [hage] <;> norm_num
    · subst a
      refine ⟨(0 : Fin 5),?_⟩
      change ((parallelAge (0 : Fin 5) : Rat) : ℝ) = 3
      have hage : parallelAge (0 : Fin 5) = 3 := by decide
      rw [hage] <;> norm_num
  · rintro ⟨v,rfl⟩
    fin_cases v
    · change ((parallelAge (0 : Fin 5) : Rat) : ℝ) ∈ [0,1,2,3]
      have hage : parallelAge (0 : Fin 5) = 3 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((parallelAge (1 : Fin 5) : Rat) : ℝ) ∈ [0,1,2,3]
      have hage : parallelAge (1 : Fin 5) = 0 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((parallelAge (2 : Fin 5) : Rat) : ℝ) ∈ [0,1,2,3]
      have hage : parallelAge (2 : Fin 5) = 2 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((parallelAge (3 : Fin 5) : Rat) : ℝ) ∈ [0,1,2,3]
      have hage : parallelAge (3 : Fin 5) = 1 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]
    · change ((parallelAge (4 : Fin 5) : Rat) : ℝ) ∈ [0,1,2,3]
      have hage : parallelAge (4 : Fin 5) = 0 := by decide
      rw [hage] <;> norm_num [List.mem_cons,List.not_mem_nil]

noncomputable def twoTipDuration (_ : Fin 1) : ℝ≥0 := Real.toNNReal (2-0)
noncomputable def serialDuration (j : Fin 2) : ℝ≥0 :=
  if j.val = 0 then Real.toNNReal ((1/4)-(-3/2)) else Real.toNNReal ((3/2)-(1/4))
noncomputable def parallelDuration (j : Fin 3) : ℝ≥0 :=
  if j.val = 0 then Real.toNNReal (1-0) else
    if j.val = 1 then Real.toNNReal (2-1) else Real.toNNReal (3-2)

private theorem append_program_congr {V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (xs ys as bs : List (ProgramStep N))
    (hx : ∀ s : Code N sample, sourceProgram N r xs s = sourceProgram N r ys s)
    (ha : ∀ s : Code N sample, sourceProgram N r as s = sourceProgram N r bs s)
    (s : Code N sample) : sourceProgram N r (xs ++ as) s = sourceProgram N r (ys ++ bs) s := by
  rw [program_append,program_append,hx s]
  congr 1
  funext m
  exact ha m

private theorem interval_program_congr {V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (t : ℝ≥0) (xs ys : List (ProgramStep N))
    (hx : ∀ s : Code N sample, sourceProgram N r xs s = sourceProgram N r ys s)
    (s : Code N sample) :
    sourceProgram N r (.interval t :: xs) s = sourceProgram N r (.interval t :: ys) s := by
  change (sourceProgramStep N r (.interval t) s).bind (sourceProgram N r xs) =
    (sourceProgramStep N r (.interval t) s).bind (sourceProgram N r ys)
  congr 1
  funext m
  exact hx m

theorem twoTip_program_eq (sample : Copy → Fin 2) (gamma : Hybrid N2 → unitInterval)
    (r : PositivePairRates (Fin 2)) (s : Code N2 sample) :
    sourceProgram N2 r (twoTipWord.map (instantiateGamma N2 registry2 gamma (fun _ => false) twoTipDuration)) s =
      sourceProgram N2 r (compiledCalendarProgram N2 twoTipCalendar registry2 gamma (fun _ => false)) s := by
  let p0 : List (ProgramStep N2) :=
    (([] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([1,2] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let q0 : List (ProgramStep N2) :=
    boundaryOperations N2 twoTipCalendar registry2 gamma (fun _ => false) 0
  have hp0 : ∀ m : Code N2 sample, sourceProgram N2 r p0 m = sourceProgram N2 r q0 m :=
    (twoTip_zero_consumers sample gamma r).1
  let p1 : List (ProgramStep N2) :=
    (([0,1] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([0] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let q1 : List (ProgramStep N2) :=
    boundaryOperations N2 twoTipCalendar registry2 gamma (fun _ => false) 2
  have hp1 : ∀ m : Code N2 sample, sourceProgram N2 r p1 m = sourceProgram N2 r q1 m :=
    (twoTip_root_consumers sample gamma r).1
  simp only [compiledCalendarProgram,twoTip_sorted_dates,calendarTail,List.append_nil]
  change sourceProgram N2 r (p0 ++ (.interval (twoTipDuration 0) :: p1)) s = sourceProgram N2 r (q0 ++ (.interval (twoTipDuration 0) :: q1)) s
  have htail0 : ∀ m : Code N2 sample,
      sourceProgram N2 r (p0 ++ (.interval (twoTipDuration 0) :: p1)) m = sourceProgram N2 r (q0 ++ (.interval (twoTipDuration 0) :: q1)) m :=
    append_program_congr N2 r p0 q0
      (.interval (twoTipDuration 0) :: p1)
      (.interval (twoTipDuration 0) :: q1) hp0
      (interval_program_congr N2 r (twoTipDuration 0) p1 q1 hp1)
  exact htail0 s

theorem twoTip_initialized_eq_calendar (sample : Copy → Fin 2) (p : HybridProbabilities N2)
    (r : PositivePairRates (Fin 2)) :
    initializedWordLaw N2 sample registry2 p (fun _ => false) r twoTipDuration twoTipWord =
      naturalCalendarLaw N2 twoTipCalendar sample registry2 p (fun _ => false) r := by
  rw [initializedWordLaw,naturalCalendarLaw]
  congr 1
  funext register
  exact twoTip_program_eq sample (originalGamma p) r _

theorem serial_program_eq (sample : Copy → Fin 2) (gamma : Hybrid N2 → unitInterval)
    (r : PositivePairRates (Fin 2)) (s : Code N2 sample) :
    sourceProgram N2 r (serialWord.map (instantiateGamma N2 registry2 gamma (fun _ => false) serialDuration)) s =
      sourceProgram N2 r (compiledCalendarProgram N2 serialCalendar registry2 gamma (fun _ => false)) s := by
  let p0 : List (ProgramStep N2) :=
    (([] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([1] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let q0 : List (ProgramStep N2) :=
    boundaryOperations N2 serialCalendar registry2 gamma (fun _ => false) (-3 / 2)
  have hp0 : ∀ m : Code N2 sample, sourceProgram N2 r p0 m = sourceProgram N2 r q0 m :=
    (serial_first_consumers sample gamma r).1
  let p1 : List (ProgramStep N2) :=
    (([] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([2] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let q1 : List (ProgramStep N2) :=
    boundaryOperations N2 serialCalendar registry2 gamma (fun _ => false) (1 / 4)
  have hp1 : ∀ m : Code N2 sample, sourceProgram N2 r p1 m = sourceProgram N2 r q1 m :=
    (serial_middle_consumers sample gamma r).1
  let p2 : List (ProgramStep N2) :=
    (([0,1] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([0] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let q2 : List (ProgramStep N2) :=
    boundaryOperations N2 serialCalendar registry2 gamma (fun _ => false) (3 / 2)
  have hp2 : ∀ m : Code N2 sample, sourceProgram N2 r p2 m = sourceProgram N2 r q2 m :=
    (serial_root_consumers sample gamma r).1
  simp only [compiledCalendarProgram,serial_sorted_dates,calendarTail,List.append_nil]
  change sourceProgram N2 r (p0 ++ (.interval (serialDuration 0) :: (p1 ++ (.interval (serialDuration 1) :: p2)))) s = sourceProgram N2 r (q0 ++ (.interval (serialDuration 0) :: (q1 ++ (.interval (serialDuration 1) :: q2)))) s
  have htail1 : ∀ m : Code N2 sample,
      sourceProgram N2 r (p1 ++ (.interval (serialDuration 1) :: p2)) m = sourceProgram N2 r (q1 ++ (.interval (serialDuration 1) :: q2)) m :=
    append_program_congr N2 r p1 q1
      (.interval (serialDuration 1) :: p2)
      (.interval (serialDuration 1) :: q2) hp1
      (interval_program_congr N2 r (serialDuration 1) p2 q2 hp2)
  have htail0 : ∀ m : Code N2 sample,
      sourceProgram N2 r (p0 ++ (.interval (serialDuration 0) :: (p1 ++ (.interval (serialDuration 1) :: p2)))) m = sourceProgram N2 r (q0 ++ (.interval (serialDuration 0) :: (q1 ++ (.interval (serialDuration 1) :: q2)))) m :=
    append_program_congr N2 r p0 q0
      (.interval (serialDuration 0) :: (p1 ++ (.interval (serialDuration 1) :: p2)))
      (.interval (serialDuration 0) :: (q1 ++ (.interval (serialDuration 1) :: q2))) hp0
      (interval_program_congr N2 r (serialDuration 0) (p1 ++ (.interval (serialDuration 1) :: p2)) (q1 ++ (.interval (serialDuration 1) :: q2)) htail1)
  exact htail0 s

theorem serial_initialized_eq_calendar (sample : Copy → Fin 2) (p : HybridProbabilities N2)
    (r : PositivePairRates (Fin 2)) :
    initializedWordLaw N2 sample registry2 p (fun _ => false) r serialDuration serialWord =
      naturalCalendarLaw N2 serialCalendar sample registry2 p (fun _ => false) r := by
  rw [initializedWordLaw,naturalCalendarLaw]
  congr 1
  funext register
  exact serial_program_eq sample (originalGamma p) r _

theorem parallel_program_eq (sample : Copy → Fin 2) (gamma : Hybrid NP → unitInterval)
    (r : PositivePairRates (Fin 5)) (s : Code NP sample) :
    sourceProgram NP r (parallelFiniteWord.map (instantiateGamma NP OriginalParallelEpochFixture.registry gamma (fun _ => true) parallelDuration)) s =
      sourceProgram NP r (compiledCalendarProgram NP parallelCalendar OriginalParallelEpochFixture.registry gamma (fun _ => true)) s := by
  let p0 : List (ProgramStep NP) :=
    (([] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([1,4] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let q0 : List (ProgramStep NP) :=
    boundaryOperations NP parallelCalendar OriginalParallelEpochFixture.registry gamma (fun _ => true) 0
  have hp0 : ∀ m : Code NP sample, sourceProgram NP r p0 m = sourceProgram NP r q0 m :=
    (parallel_zero_consumers sample gamma r).1
  let p1 : List (ProgramStep NP) :=
    (([4] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([3] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let q1 : List (ProgramStep NP) :=
    boundaryOperations NP parallelCalendar OriginalParallelEpochFixture.registry gamma (fun _ => true) 1
  have hp1 : ∀ m : Code NP sample, sourceProgram NP r p1 m = sourceProgram NP r q1 m :=
    (parallel_one_consumers sample gamma r).1
  let p2 : List (ProgramStep NP) :=
    (([2,3] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([2] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let q2 : List (ProgramStep NP) :=
    boundaryOperations NP parallelCalendar OriginalParallelEpochFixture.registry gamma (fun _ => true) 2
  have hp2 : ∀ m : Code NP sample, sourceProgram NP r p2 m = sourceProgram NP r q2 m :=
    (parallel_two_consumers sample gamma r).1
  let p3 : List (ProgramStep NP) :=
    (([0,1] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([0] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let q3 : List (ProgramStep NP) :=
    boundaryOperations NP parallelCalendar OriginalParallelEpochFixture.registry gamma (fun _ => true) 3
  have hp3 : ∀ m : Code NP sample, sourceProgram NP r p3 m = sourceProgram NP r q3 m :=
    (parallel_root_consumers sample gamma r).1
  simp only [compiledCalendarProgram,parallel_sorted_dates,calendarTail,List.append_nil]
  change sourceProgram NP r (p0 ++ (.interval (parallelDuration 0) :: (p1 ++ (.interval (parallelDuration 1) :: (p2 ++ (.interval (parallelDuration 2) :: p3)))))) s = sourceProgram NP r (q0 ++ (.interval (parallelDuration 0) :: (q1 ++ (.interval (parallelDuration 1) :: (q2 ++ (.interval (parallelDuration 2) :: q3)))))) s
  have htail2 : ∀ m : Code NP sample,
      sourceProgram NP r (p2 ++ (.interval (parallelDuration 2) :: p3)) m = sourceProgram NP r (q2 ++ (.interval (parallelDuration 2) :: q3)) m :=
    append_program_congr NP r p2 q2
      (.interval (parallelDuration 2) :: p3)
      (.interval (parallelDuration 2) :: q3) hp2
      (interval_program_congr NP r (parallelDuration 2) p3 q3 hp3)
  have htail1 : ∀ m : Code NP sample,
      sourceProgram NP r (p1 ++ (.interval (parallelDuration 1) :: (p2 ++ (.interval (parallelDuration 2) :: p3)))) m = sourceProgram NP r (q1 ++ (.interval (parallelDuration 1) :: (q2 ++ (.interval (parallelDuration 2) :: q3)))) m :=
    append_program_congr NP r p1 q1
      (.interval (parallelDuration 1) :: (p2 ++ (.interval (parallelDuration 2) :: p3)))
      (.interval (parallelDuration 1) :: (q2 ++ (.interval (parallelDuration 2) :: q3))) hp1
      (interval_program_congr NP r (parallelDuration 1) (p2 ++ (.interval (parallelDuration 2) :: p3)) (q2 ++ (.interval (parallelDuration 2) :: q3)) htail2)
  have htail0 : ∀ m : Code NP sample,
      sourceProgram NP r (p0 ++ (.interval (parallelDuration 0) :: (p1 ++ (.interval (parallelDuration 1) :: (p2 ++ (.interval (parallelDuration 2) :: p3)))))) m = sourceProgram NP r (q0 ++ (.interval (parallelDuration 0) :: (q1 ++ (.interval (parallelDuration 1) :: (q2 ++ (.interval (parallelDuration 2) :: q3)))))) m :=
    append_program_congr NP r p0 q0
      (.interval (parallelDuration 0) :: (p1 ++ (.interval (parallelDuration 1) :: (p2 ++ (.interval (parallelDuration 2) :: p3)))))
      (.interval (parallelDuration 0) :: (q1 ++ (.interval (parallelDuration 1) :: (q2 ++ (.interval (parallelDuration 2) :: q3))))) hp0
      (interval_program_congr NP r (parallelDuration 0) (p1 ++ (.interval (parallelDuration 1) :: (p2 ++ (.interval (parallelDuration 2) :: p3)))) (q1 ++ (.interval (parallelDuration 1) :: (q2 ++ (.interval (parallelDuration 2) :: q3)))) htail1)
  exact htail0 s

theorem parallel_initialized_eq_calendar (sample : Copy → Fin 2) (p : HybridProbabilities NP)
    (r : PositivePairRates (Fin 5)) :
    initializedWordLaw NP sample OriginalParallelEpochFixture.registry p (fun _ => true) r parallelDuration parallelFiniteWord =
      naturalCalendarLaw NP parallelCalendar sample OriginalParallelEpochFixture.registry p (fun _ => true) r := by
  rw [initializedWordLaw,naturalCalendarLaw]
  congr 1
  funext register
  exact parallel_program_eq sample (originalGamma p) r _

variable [Nonempty Copy]

theorem twoTip_completed_calendar_law (sample : Copy → Fin 2)
    (p : HybridProbabilities N2) (r : PositivePairRates (Fin 2))
    (b : SelectedIndex N2 sample Finset.univ) :
    wordEval N2 r (originalGamma p) twoTipDuration
      (polynomial (readRows (project N2 Finset.univ)
        (completedNaturalWordRows N2 sample registry2 (fun _ => false) twoTipWord) b)) =
      ((((naturalCalendarLaw N2 twoTipCalendar sample registry2 p (fun _ => false) r).bind
        (completionKernel N2 r)).map (projection N2 Finset.univ)) b).toReal := by
  rw [twoTip_completed_polynomial sample (originalGamma p) r twoTipDuration]
  apply actual_root_law_completed_polynomial N2
    (naturalCalendarLaw N2 twoTipCalendar sample registry2 p (fun _ => false) r)
    (fun s hs => natural_calendar_ancestral_support N2 twoTipCalendar sample registry2 p (fun _ => false) r hs)
    (naturalWordPolynomial N2 sample registry2 (fun _ => false) twoTipWord)
    r (originalGamma p) twoTipDuration _ b
  intro a
  rw [← twoTip_initialized_eq_calendar sample p r]
  exact actual_natural_word_polynomial N2 sample registry2 p (fun _ => false) r twoTipDuration twoTipWord a

theorem serial_completed_calendar_law (sample : Copy → Fin 2)
    (p : HybridProbabilities N2) (r : PositivePairRates (Fin 2))
    (b : SelectedIndex N2 sample Finset.univ) :
    wordEval N2 r (originalGamma p) serialDuration
      (polynomial (readRows (project N2 Finset.univ)
        (completedNaturalWordRows N2 sample registry2 (fun _ => false) serialWord) b)) =
      ((((naturalCalendarLaw N2 serialCalendar sample registry2 p (fun _ => false) r).bind
        (completionKernel N2 r)).map (projection N2 Finset.univ)) b).toReal := by
  rw [serial_completed_polynomial sample (originalGamma p) r serialDuration]
  apply actual_root_law_completed_polynomial N2
    (naturalCalendarLaw N2 serialCalendar sample registry2 p (fun _ => false) r)
    (fun s hs => natural_calendar_ancestral_support N2 serialCalendar sample registry2 p (fun _ => false) r hs)
    (naturalWordPolynomial N2 sample registry2 (fun _ => false) serialWord)
    r (originalGamma p) serialDuration _ b
  intro a
  rw [← serial_initialized_eq_calendar sample p r]
  exact actual_natural_word_polynomial N2 sample registry2 p (fun _ => false) r serialDuration serialWord a

theorem parallel_completed_calendar_law (sample : Copy → Fin 2)
    (p : HybridProbabilities NP) (r : PositivePairRates (Fin 5))
    (b : SelectedIndex NP sample Finset.univ) :
    wordEval NP r (originalGamma p) parallelDuration
      (polynomial (readRows (project NP Finset.univ)
        (completedNaturalWordRows NP sample OriginalParallelEpochFixture.registry (fun _ => true) parallelFiniteWord) b)) =
      ((((naturalCalendarLaw NP parallelCalendar sample OriginalParallelEpochFixture.registry p (fun _ => true) r).bind
        (completionKernel NP r)).map (projection NP Finset.univ)) b).toReal := by
  rw [parallel_completed_polynomial sample (originalGamma p) r parallelDuration]
  apply actual_root_law_completed_polynomial NP
    (naturalCalendarLaw NP parallelCalendar sample OriginalParallelEpochFixture.registry p (fun _ => true) r)
    (fun s hs => natural_calendar_ancestral_support NP parallelCalendar sample OriginalParallelEpochFixture.registry p (fun _ => true) r hs)
    (naturalWordPolynomial NP sample OriginalParallelEpochFixture.registry (fun _ => true) parallelFiniteWord)
    r (originalGamma p) parallelDuration _ b
  intro a
  rw [← parallel_initialized_eq_calendar sample p r]
  exact actual_natural_word_polynomial NP sample OriginalParallelEpochFixture.registry p (fun _ => true) r parallelDuration parallelFiniteWord a

#print axioms twoTip_sorted_dates
#print axioms twoTip_program_eq
#print axioms twoTip_initialized_eq_calendar
#print axioms twoTip_completed_calendar_law
#print axioms serial_sorted_dates
#print axioms serial_program_eq
#print axioms serial_initialized_eq_calendar
#print axioms serial_completed_calendar_law
#print axioms parallel_sorted_dates
#print axioms parallel_program_eq
#print axioms parallel_initialized_eq_calendar
#print axioms parallel_completed_calendar_law

end UnifiedLean.G7.OriginalCompletedCalendarLaw
