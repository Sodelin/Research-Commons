import G7OriginalCompletedCalendarPhases

/-!
# Consume the three finite phase instances through every raw natural word

Contributor: Codex / solver_design, 2026-10-10.
DRAFT, pending sole-scheduler kernel checking and complete owned audit.
Uses the oldest singleton-tip initialization, interval-location preservation,
AfterNodes-to-next-boundary invariant and latest-date root exclusion. No agenda
or epoch algorithm is introduced. All raw rows, including zero polynomials,
are covered. Duration arguments are arbitrary for this structural conclusion;
physical calendar PMF equality still requires the exact supplied durations and
the separate phase/program transport. This source does not assert that equality.
-/
namespace UnifiedLean.G7.OriginalCompletedCalendarRoot

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar
open GProgram.G7.RawProgramLocations
open GProgram.G7.EffectiveInitializationCoefficients GProgram.G7.SparseWordComposition
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.SparseRowProducts GProgram.G7.EffectiveWordCoefficients
open GProgram.G7.EffectiveCompletedWordCoefficients GProgram.G7.SymbolicProgramPolynomial
open GProgram.G7.CompletedCalendarPolynomial
open UnifiedLean.G7.OriginalWordFixture
open UnifiedLean.G7.OriginalCompletedCalendarFixture
open UnifiedLean.G7.OriginalCompletedCalendarPhases
open scoped Classical NNReal

variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

private theorem initial_ready_lower {V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (register : V → Bool) (a : ℝ) (hlower : ∀ v : V, a ≤ C.age v) :
    BoundaryReady N C a (state (initialCode N sample register)) := by
  exact encode_epoch_compatible N C _ (initial_source_valid N sample register)
    (initial_calendar_compatible N C sample register (fun x => hlower _))

private theorem interval_next_ready {V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (a b : ℝ) (t : ℝ≥0) (s m : Code N sample)
    (hs : AfterNodes N C a (state s))
    (hgap : ∀ v : V, a < C.age v → b ≤ C.age v) (hab : a ≤ b)
    (hm : programMovement N (.interval t) s m) : BoundaryReady N C b (state m) := by
  apply epoch_to_next_ready N C _ hab
  intro x
  rw [hm x]
  exact after_nodes_to_epoch N C hs hgap x

private theorem after_latest_root {V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (a : ℝ) (d : Code N sample) (hmax : ∀ v : V, C.age v ≤ a)
    (hs : AfterNodes N C a (state d)) : AncestralRoot N d := by
  intro x
  have hready := hs.1.1 x
  cases hloc : copyLocation (state d) x with
  | node v => exact False.elim (not_lt_of_ge (hmax v) (hs.2 x v hloc))
  | edge e => exact False.elim (not_lt_of_ge (hmax (N.graph.source e)) (hs.1.2 x e hloc))
  | rootPopulation v =>
      rw [hloc] at hready
      exact congrArg Location.rootPopulation hready.1

theorem twoTip_trace_root (sample : Copy → Fin 2)
    (register : Fin 3 → Bool) (gamma : Hybrid N2 → unitInterval)
    (r : PositivePairRates (Fin 2)) (dur : Fin 1 → ℝ≥0)
    (d : Code N2 sample)
    (hd : programTrace N2
      (twoTipWord.map (instantiateGamma N2 registry2 gamma (fun _ => false) dur))
      (initialCode N2 sample register) d) : AncestralRoot N2 d := by
  let p0 : List (ProgramStep N2) :=
    (([] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([1,2] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let p1 : List (ProgramStep N2) :=
    (([0,1] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([0] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  change programTrace N2 (p0 ++ (.interval (dur 0) :: p1)) (initialCode N2 sample register) d at hd
  have hready0 : BoundaryReady N2 twoTipCalendar 0
      (state (initialCode N2 sample register)) :=
    initial_ready_lower N2 twoTipCalendar sample register 0 (by
      intro v
      fin_cases v <;> norm_num [twoTipCalendar,twoTipAge,Fin.ext_iff])
  rw [programTrace_append] at hd
  obtain ⟨s0,hphase0,htail0⟩ := hd
  have hafter0 := (twoTip_zero_consumers sample gamma r).2 (initialCode N2 sample register) s0 hready0 hphase0
  change ∃ m, programMovement N2 (.interval (dur 0)) s0 m ∧
    programTrace N2 p1 m d at htail0
  obtain ⟨m0,hm0,hrest0⟩ := htail0
  have hready1 := interval_next_ready N2 twoTipCalendar 0 2 (dur 0)
    s0 m0 hafter0 (by
      intro v hv
      fin_cases v <;> norm_num [twoTipCalendar,twoTipAge,Fin.ext_iff] at hv ⊢) (by norm_num) hm0
  have hfinal := (twoTip_root_consumers sample gamma r).2 m0 d hready1 hrest0
  exact after_latest_root N2 twoTipCalendar 2 d (by
    intro v
    fin_cases v <;> norm_num [twoTipCalendar,twoTipAge,Fin.ext_iff]) hfinal

theorem serial_trace_root (sample : Copy → Fin 2)
    (register : Fin 3 → Bool) (gamma : Hybrid N2 → unitInterval)
    (r : PositivePairRates (Fin 2)) (dur : Fin 2 → ℝ≥0)
    (d : Code N2 sample)
    (hd : programTrace N2
      (serialWord.map (instantiateGamma N2 registry2 gamma (fun _ => false) dur))
      (initialCode N2 sample register) d) : AncestralRoot N2 d := by
  let p0 : List (ProgramStep N2) :=
    (([] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([1] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let p1 : List (ProgramStep N2) :=
    (([] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([2] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  let p2 : List (ProgramStep N2) :=
    (([0,1] : List (Fin 2)).map (fun e => .boundary (.exit e))) ++
      (([0] : List (Fin 3)).map (fun v =>
        .boundary (originalNodeOperation N2 registry2 gamma (fun _ => false) v)))
  change programTrace N2 (p0 ++ (.interval (dur 0) :: (p1 ++ (.interval (dur 1) :: p2)))) (initialCode N2 sample register) d at hd
  have hready0 : BoundaryReady N2 serialCalendar (-3 / 2)
      (state (initialCode N2 sample register)) :=
    initial_ready_lower N2 serialCalendar sample register (-3 / 2) (by
      intro v
      fin_cases v <;> norm_num [serialCalendar,serialAge,Fin.ext_iff])
  rw [programTrace_append] at hd
  obtain ⟨s0,hphase0,htail0⟩ := hd
  have hafter0 := (serial_first_consumers sample gamma r).2 (initialCode N2 sample register) s0 hready0 hphase0
  change ∃ m, programMovement N2 (.interval (dur 0)) s0 m ∧
    programTrace N2 (p1 ++ (.interval (dur 1) :: p2)) m d at htail0
  obtain ⟨m0,hm0,hrest0⟩ := htail0
  have hready1 := interval_next_ready N2 serialCalendar (-3 / 2) (1 / 4) (dur 0)
    s0 m0 hafter0 (by
      intro v hv
      fin_cases v <;> norm_num [serialCalendar,serialAge,Fin.ext_iff] at hv ⊢) (by norm_num) hm0
  rw [programTrace_append] at hrest0
  obtain ⟨s1,hphase1,htail1⟩ := hrest0
  have hafter1 := (serial_middle_consumers sample gamma r).2 m0 s1 hready1 hphase1
  change ∃ m, programMovement N2 (.interval (dur 1)) s1 m ∧
    programTrace N2 p2 m d at htail1
  obtain ⟨m1,hm1,hrest1⟩ := htail1
  have hready2 := interval_next_ready N2 serialCalendar (1 / 4) (3 / 2) (dur 1)
    s1 m1 hafter1 (by
      intro v hv
      fin_cases v <;> norm_num [serialCalendar,serialAge,Fin.ext_iff] at hv ⊢) (by norm_num) hm1
  have hfinal := (serial_root_consumers sample gamma r).2 m1 d hready2 hrest1
  exact after_latest_root N2 serialCalendar (3 / 2) d (by
    intro v
    fin_cases v <;> norm_num [serialCalendar,serialAge,Fin.ext_iff]) hfinal

theorem parallel_trace_root (sample : Copy → Fin 2)
    (register : Fin 5 → Bool) (gamma : Hybrid NP → unitInterval)
    (r : PositivePairRates (Fin 5)) (dur : Fin 3 → ℝ≥0)
    (d : Code NP sample)
    (hd : programTrace NP
      (parallelFiniteWord.map (instantiateGamma NP OriginalParallelEpochFixture.registry gamma (fun _ => true) dur))
      (initialCode NP sample register) d) : AncestralRoot NP d := by
  let p0 : List (ProgramStep NP) :=
    (([] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([1,4] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let p1 : List (ProgramStep NP) :=
    (([4] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([3] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let p2 : List (ProgramStep NP) :=
    (([2,3] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([2] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  let p3 : List (ProgramStep NP) :=
    (([0,1] : List (Fin 5)).map (fun e => .boundary (.exit e))) ++
      (([0] : List (Fin 5)).map (fun v =>
        .boundary (originalNodeOperation NP OriginalParallelEpochFixture.registry gamma (fun _ => true) v)))
  change programTrace NP (p0 ++ (.interval (dur 0) :: (p1 ++ (.interval (dur 1) :: (p2 ++ (.interval (dur 2) :: p3)))))) (initialCode NP sample register) d at hd
  have hready0 : BoundaryReady NP parallelCalendar 0
      (state (initialCode NP sample register)) :=
    initial_ready_lower NP parallelCalendar sample register 0 (by
      intro v
      fin_cases v
      · change 0 ≤ ((parallelAge (0 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (0 : Fin 5) = 3 := by decide
        rw [hage] <;> norm_num
      · change 0 ≤ ((parallelAge (1 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (1 : Fin 5) = 0 := by decide
        rw [hage] <;> norm_num
      · change 0 ≤ ((parallelAge (2 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (2 : Fin 5) = 2 := by decide
        rw [hage] <;> norm_num
      · change 0 ≤ ((parallelAge (3 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (3 : Fin 5) = 1 := by decide
        rw [hage] <;> norm_num
      · change 0 ≤ ((parallelAge (4 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (4 : Fin 5) = 0 := by decide
        rw [hage] <;> norm_num)
  rw [programTrace_append] at hd
  obtain ⟨s0,hphase0,htail0⟩ := hd
  have hafter0 := (parallel_zero_consumers sample gamma r).2 (initialCode NP sample register) s0 hready0 hphase0
  change ∃ m, programMovement NP (.interval (dur 0)) s0 m ∧
    programTrace NP (p1 ++ (.interval (dur 1) :: (p2 ++ (.interval (dur 2) :: p3)))) m d at htail0
  obtain ⟨m0,hm0,hrest0⟩ := htail0
  have hready1 := interval_next_ready NP parallelCalendar 0 1 (dur 0)
    s0 m0 hafter0 (by
      intro v hv
      fin_cases v
      · change 0 < ((parallelAge (0 : Fin 5) : Rat) : ℝ) at hv
        change 1 ≤ ((parallelAge (0 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (0 : Fin 5) = 3 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 0 < ((parallelAge (1 : Fin 5) : Rat) : ℝ) at hv
        change 1 ≤ ((parallelAge (1 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (1 : Fin 5) = 0 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 0 < ((parallelAge (2 : Fin 5) : Rat) : ℝ) at hv
        change 1 ≤ ((parallelAge (2 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (2 : Fin 5) = 2 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 0 < ((parallelAge (3 : Fin 5) : Rat) : ℝ) at hv
        change 1 ≤ ((parallelAge (3 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (3 : Fin 5) = 1 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 0 < ((parallelAge (4 : Fin 5) : Rat) : ℝ) at hv
        change 1 ≤ ((parallelAge (4 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (4 : Fin 5) = 0 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢) (by norm_num) hm0
  rw [programTrace_append] at hrest0
  obtain ⟨s1,hphase1,htail1⟩ := hrest0
  have hafter1 := (parallel_one_consumers sample gamma r).2 m0 s1 hready1 hphase1
  change ∃ m, programMovement NP (.interval (dur 1)) s1 m ∧
    programTrace NP (p2 ++ (.interval (dur 2) :: p3)) m d at htail1
  obtain ⟨m1,hm1,hrest1⟩ := htail1
  have hready2 := interval_next_ready NP parallelCalendar 1 2 (dur 1)
    s1 m1 hafter1 (by
      intro v hv
      fin_cases v
      · change 1 < ((parallelAge (0 : Fin 5) : Rat) : ℝ) at hv
        change 2 ≤ ((parallelAge (0 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (0 : Fin 5) = 3 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 1 < ((parallelAge (1 : Fin 5) : Rat) : ℝ) at hv
        change 2 ≤ ((parallelAge (1 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (1 : Fin 5) = 0 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 1 < ((parallelAge (2 : Fin 5) : Rat) : ℝ) at hv
        change 2 ≤ ((parallelAge (2 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (2 : Fin 5) = 2 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 1 < ((parallelAge (3 : Fin 5) : Rat) : ℝ) at hv
        change 2 ≤ ((parallelAge (3 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (3 : Fin 5) = 1 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 1 < ((parallelAge (4 : Fin 5) : Rat) : ℝ) at hv
        change 2 ≤ ((parallelAge (4 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (4 : Fin 5) = 0 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢) (by norm_num) hm1
  rw [programTrace_append] at hrest1
  obtain ⟨s2,hphase2,htail2⟩ := hrest1
  have hafter2 := (parallel_two_consumers sample gamma r).2 m1 s2 hready2 hphase2
  change ∃ m, programMovement NP (.interval (dur 2)) s2 m ∧
    programTrace NP p3 m d at htail2
  obtain ⟨m2,hm2,hrest2⟩ := htail2
  have hready3 := interval_next_ready NP parallelCalendar 2 3 (dur 2)
    s2 m2 hafter2 (by
      intro v hv
      fin_cases v
      · change 2 < ((parallelAge (0 : Fin 5) : Rat) : ℝ) at hv
        change 3 ≤ ((parallelAge (0 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (0 : Fin 5) = 3 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 2 < ((parallelAge (1 : Fin 5) : Rat) : ℝ) at hv
        change 3 ≤ ((parallelAge (1 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (1 : Fin 5) = 0 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 2 < ((parallelAge (2 : Fin 5) : Rat) : ℝ) at hv
        change 3 ≤ ((parallelAge (2 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (2 : Fin 5) = 2 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 2 < ((parallelAge (3 : Fin 5) : Rat) : ℝ) at hv
        change 3 ≤ ((parallelAge (3 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (3 : Fin 5) = 1 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢
      · change 2 < ((parallelAge (4 : Fin 5) : Rat) : ℝ) at hv
        change 3 ≤ ((parallelAge (4 : Fin 5) : Rat) : ℝ)
        have hage : parallelAge (4 : Fin 5) = 0 := by decide
        rw [hage] at hv ⊢ <;> norm_num at hv ⊢) (by norm_num) hm2
  have hfinal := (parallel_root_consumers sample gamma r).2 m2 d hready3 hrest2
  exact after_latest_root NP parallelCalendar 3 d (by
    intro v
    fin_cases v
    · change ((parallelAge (0 : Fin 5) : Rat) : ℝ) ≤ 3
      have hage : parallelAge (0 : Fin 5) = 3 := by decide
      rw [hage] <;> norm_num
    · change ((parallelAge (1 : Fin 5) : Rat) : ℝ) ≤ 3
      have hage : parallelAge (1 : Fin 5) = 0 := by decide
      rw [hage] <;> norm_num
    · change ((parallelAge (2 : Fin 5) : Rat) : ℝ) ≤ 3
      have hage : parallelAge (2 : Fin 5) = 2 := by decide
      rw [hage] <;> norm_num
    · change ((parallelAge (3 : Fin 5) : Rat) : ℝ) ≤ 3
      have hage : parallelAge (3 : Fin 5) = 1 := by decide
      rw [hage] <;> norm_num
    · change ((parallelAge (4 : Fin 5) : Rat) : ℝ) ≤ 3
      have hage : parallelAge (4 : Fin 5) = 0 := by decide
      rw [hage] <;> norm_num) hfinal

private theorem natural_raw_root_of_trace {J V E X : Type*}
    [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
    [FinEnum V] [FinEnum E]
    (N : RootedBinary V E X) (sample : Copy → X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (dur : J → ℝ≥0) (word : List (UnifiedLean.G6.OriginalCalendarSchema.Symbol J V E))
    (htrace : ∀ register d, programTrace N
      (word.map (instantiateGamma N H gamma common dur))
      (initialCode N sample register) d → AncestralRoot N d)
    (row : Code N sample × Sparse (WordVariable N J))
    (hrow : row ∈ naturalWordRows N sample H common word) : AncestralRoot N row.1 := by
  change row ∈ bindRows (initialRows N sample Sum.inr) (wordRows N H common word) at hrow
  rcases List.mem_flatMap.mp hrow with ⟨a,ha,hrow⟩
  rcases List.mem_map.mp hrow with ⟨b,hb,he⟩
  rw [← he]
  have ht := wordRows_trace N H gamma common dur word a.1 b hb
  rcases List.mem_map.mp ha with ⟨coin,_,ha⟩
  rw [← ha,initialCodeEffective_eq] at ht
  exact htrace (originalRegisterEffective N coin) b.1 ht

theorem twoTip_natural_raw_root (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2))
    (dur : Fin 1 → ℝ≥0) (row : Code N2 sample × Sparse (WordVariable N2 (Fin 1)))
    (hrow : row ∈ naturalWordRows N2 sample registry2 (fun _ => false) twoTipWord) :
    AncestralRoot N2 row.1 :=
  natural_raw_root_of_trace N2 sample registry2 gamma (fun _ => false) dur twoTipWord
    (fun register d hd => twoTip_trace_root sample register gamma r dur d hd) row hrow

theorem serial_natural_raw_root (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2))
    (dur : Fin 2 → ℝ≥0) (row : Code N2 sample × Sparse (WordVariable N2 (Fin 2)))
    (hrow : row ∈ naturalWordRows N2 sample registry2 (fun _ => false) serialWord) :
    AncestralRoot N2 row.1 :=
  natural_raw_root_of_trace N2 sample registry2 gamma (fun _ => false) dur serialWord
    (fun register d hd => serial_trace_root sample register gamma r dur d hd) row hrow

theorem parallel_natural_raw_root (sample : Copy → Fin 2)
    (gamma : Hybrid NP → unitInterval) (r : PositivePairRates (Fin 5))
    (dur : Fin 3 → ℝ≥0) (row : Code NP sample × Sparse (WordVariable NP (Fin 3)))
    (hrow : row ∈ naturalWordRows NP sample OriginalParallelEpochFixture.registry (fun _ => true) parallelFiniteWord) :
    AncestralRoot NP row.1 :=
  natural_raw_root_of_trace NP sample OriginalParallelEpochFixture.registry gamma (fun _ => true) dur parallelFiniteWord
    (fun register d hd => parallel_trace_root sample register gamma r dur d hd) row hrow

variable [Nonempty Copy]

theorem twoTip_completed_polynomial (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2))
    (dur : Fin 1 → ℝ≥0) (b : SelectedIndex N2 sample Finset.univ) :
    polynomial (readRows (project N2 Finset.univ)
      (completedNaturalWordRows N2 sample registry2 (fun _ => false) twoTipWord) b) =
      completedPolynomial N2 (naturalWordPolynomial N2 sample registry2 (fun _ => false) twoTipWord) b :=
  polynomial_completedNaturalWordRows N2 sample registry2 (fun _ => false) twoTipWord
    (fun row hrow => twoTip_natural_raw_root sample gamma r dur row hrow) r b

theorem serial_completed_polynomial (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2))
    (dur : Fin 2 → ℝ≥0) (b : SelectedIndex N2 sample Finset.univ) :
    polynomial (readRows (project N2 Finset.univ)
      (completedNaturalWordRows N2 sample registry2 (fun _ => false) serialWord) b) =
      completedPolynomial N2 (naturalWordPolynomial N2 sample registry2 (fun _ => false) serialWord) b :=
  polynomial_completedNaturalWordRows N2 sample registry2 (fun _ => false) serialWord
    (fun row hrow => serial_natural_raw_root sample gamma r dur row hrow) r b

theorem parallel_completed_polynomial (sample : Copy → Fin 2)
    (gamma : Hybrid NP → unitInterval) (r : PositivePairRates (Fin 5))
    (dur : Fin 3 → ℝ≥0) (b : SelectedIndex NP sample Finset.univ) :
    polynomial (readRows (project NP Finset.univ)
      (completedNaturalWordRows NP sample OriginalParallelEpochFixture.registry (fun _ => true) parallelFiniteWord) b) =
      completedPolynomial NP (naturalWordPolynomial NP sample OriginalParallelEpochFixture.registry (fun _ => true) parallelFiniteWord) b :=
  polynomial_completedNaturalWordRows NP sample OriginalParallelEpochFixture.registry (fun _ => true) parallelFiniteWord
    (fun row hrow => parallel_natural_raw_root sample gamma r dur row hrow) r b

#print axioms twoTip_trace_root
#print axioms twoTip_natural_raw_root
#print axioms twoTip_completed_polynomial
#print axioms serial_trace_root
#print axioms serial_natural_raw_root
#print axioms serial_completed_polynomial
#print axioms parallel_trace_root
#print axioms parallel_natural_raw_root
#print axioms parallel_completed_polynomial

end UnifiedLean.G7.OriginalCompletedCalendarRoot
