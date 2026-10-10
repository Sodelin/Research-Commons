import G7OriginalCompletedCalendarFixture
import Mathlib.Data.Finset.Dedup

/-!
# Finite original phase consumers for the three completed calendar controls

Contributor: Codex / solver_design, 2026-10-10.
DRAFT: no kernel/audit acceptance claimed by this source.
The exact admitted N2/NP calendars and parent registries come from the frozen
original fixture. Membership plus Nodup gives Perm to the inherited
choice-based phase lists. Every physical and raw-trace conclusion consumes
the accepted original phase theorem; no ascending-toList equality, agenda
compiler, independent-slot polynomial equality or native decoder is introduced.
All raw traces include zero-polynomial branches. Whole-word root and completed
calendar bindings are separate consumers of these finite phase facts.
-/
namespace UnifiedLean.G7.OriginalCompletedCalendarPhases

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open GProgram.G7.RawProgramLocations
open GProgram.G7.CalendarPhaseConsumers
open UnifiedLean.G7.OriginalWordFixture
open UnifiedLean.G7.OriginalCompletedCalendarFixture
open scoped Classical

private theorem filtered_list_perm {A : Type*} [DecidableEq A] [Fintype A]
    (p : A → Prop) (xs : List A) (hn : xs.Nodup)
    (hm : ∀ x, x ∈ xs ↔ p x) :
    xs.Perm (Finset.univ.filter p).toList := by
  apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList _)).mpr
  intro x
  simpa only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    using hm x

@[simp] private theorem twoTip_age_formula (v : Fin 3) :
    twoTipCalendar.age v = if v = 0 then (2 : ℝ) else 0 := by
  by_cases h : v = 0 <;> norm_num [twoTipCalendar,twoTipAge,h]

@[simp] private theorem serial_age_formula (v : Fin 3) :
    serialCalendar.age v =
      if v = 0 then (3 : ℝ) / 2 else if v = 1 then -3 / 2 else 1 / 4 := by
  by_cases h0 : v = 0
  · norm_num [serialCalendar,serialAge,h0]
  · by_cases h1 : v = 1 <;> norm_num [serialCalendar,serialAge,h0,h1]

@[simp] private theorem parallel_age_formula (v : Fin 5) :
    parallelCalendar.age v =
      if v = 0 then (3 : ℝ) else if v = 2 then 2 else if v = 3 then 1 else 0 := by
  by_cases h0 : v = 0
  · norm_num [parallelCalendar,parallelAge,h0]
  · by_cases h2 : v = 2
    · norm_num [parallelCalendar,parallelAge,h0,h2]
    · by_cases h3 : v = 3 <;> norm_num [parallelCalendar,parallelAge,h0,h2,h3]

@[simp] private theorem n2_source_zero (e : Fin 2) : N2.graph.source e = 0 := by
  fin_cases e <;> rfl

@[simp] private theorem np_source_zero : NP.graph.source (0 : Fin 5) = 0 := rfl
@[simp] private theorem np_source_one : NP.graph.source (1 : Fin 5) = 0 := rfl
@[simp] private theorem np_source_two : NP.graph.source (2 : Fin 5) = 2 := rfl
@[simp] private theorem np_source_three : NP.graph.source (3 : Fin 5) = 2 := rfl
@[simp] private theorem np_source_four : NP.graph.source (4 : Fin 5) = 3 := rfl

theorem twoTip_zero_exits_perm :
    ([] : List (Fin 2)).Perm
      (Finset.univ.filter
        (fun e : Fin 2 => twoTipCalendar.age (N2.graph.source e) = 0)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem twoTip_zero_entries_perm :
    ([1,2] : List (Fin 3)).Perm
      (Finset.univ.filter
        (fun v : Fin 3 => twoTipCalendar.age v = 0)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem twoTip_root_exits_perm :
    ([0,1] : List (Fin 2)).Perm
      (Finset.univ.filter
        (fun e : Fin 2 => twoTipCalendar.age (N2.graph.source e) = 2)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem twoTip_root_entries_perm :
    ([0] : List (Fin 3)).Perm
      (Finset.univ.filter
        (fun v : Fin 3 => twoTipCalendar.age v = 2)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem serial_first_exits_perm :
    ([] : List (Fin 2)).Perm
      (Finset.univ.filter
        (fun e : Fin 2 => serialCalendar.age (N2.graph.source e) = (-3 / 2))).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem serial_first_entries_perm :
    ([1] : List (Fin 3)).Perm
      (Finset.univ.filter
        (fun v : Fin 3 => serialCalendar.age v = (-3 / 2))).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem serial_middle_exits_perm :
    ([] : List (Fin 2)).Perm
      (Finset.univ.filter
        (fun e : Fin 2 => serialCalendar.age (N2.graph.source e) = (1 / 4))).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem serial_middle_entries_perm :
    ([2] : List (Fin 3)).Perm
      (Finset.univ.filter
        (fun v : Fin 3 => serialCalendar.age v = (1 / 4))).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem serial_root_exits_perm :
    ([0,1] : List (Fin 2)).Perm
      (Finset.univ.filter
        (fun e : Fin 2 => serialCalendar.age (N2.graph.source e) = (3 / 2))).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem serial_root_entries_perm :
    ([0] : List (Fin 3)).Perm
      (Finset.univ.filter
        (fun v : Fin 3 => serialCalendar.age v = (3 / 2))).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem parallel_zero_exits_perm :
    ([] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun e : Fin 5 => parallelCalendar.age (NP.graph.source e) = 0)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem parallel_zero_entries_perm :
    ([1,4] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun v : Fin 5 => parallelCalendar.age v = 0)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem parallel_one_exits_perm :
    ([4] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun e : Fin 5 => parallelCalendar.age (NP.graph.source e) = 1)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem parallel_one_entries_perm :
    ([3] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun v : Fin 5 => parallelCalendar.age v = 1)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem parallel_two_exits_perm :
    ([2,3] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun e : Fin 5 => parallelCalendar.age (NP.graph.source e) = 2)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem parallel_two_entries_perm :
    ([2] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun v : Fin 5 => parallelCalendar.age v = 2)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

theorem parallel_root_exits_perm :
    ([0,1] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun e : Fin 5 => parallelCalendar.age (NP.graph.source e) = 3)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro e
  fin_cases e <;> norm_num [Fin.ext_iff]

theorem parallel_root_entries_perm :
    ([0] : List (Fin 5)).Perm
      (Finset.univ.filter
        (fun v : Fin 5 => parallelCalendar.age v = 3)).toList := by
  apply filtered_list_perm _ _ (by decide)
  intro v
  fin_cases v <;> norm_num [Fin.ext_iff]

variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

/-- A proof-only bundle. The PMF equality is pointwise on every entering Code;
the structural conclusion quantifies every raw trace, without positive-support
or coefficient hypotheses. No operation list or calendar is generated here. -/
def PhaseConclusion {V E X : Type*} [DecidableEq V] [DecidableEq E]
    [Fintype V] [Fintype E] [Fintype X] [FinEnum V] [FinEnum E]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (a : ℝ) (es : List E) (vs : List V) : Prop :=
  (∀ s : Code N sample,
    sourceProgram N r
      ((es.map (fun e => .boundary (.exit e))) ++
        (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v)))) s =
      sourceProgram N r (boundaryOperations N C H gamma common a) s) ∧
  (∀ s d : Code N sample, BoundaryReady N C a (state s) →
    programTrace N
      ((es.map (fun e => .boundary (.exit e))) ++
        (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v)))) s d →
      AfterNodes N C a (state d))

private theorem consume_phase {V E X : Type*} [DecidableEq V] [DecidableEq E]
    [Fintype V] [Fintype E] [Fintype X] [FinEnum V] [FinEnum E]
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (a : ℝ) (es : List E) (vs : List V)
    (he : es.Perm (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList)
    (hv : vs.Perm (Finset.univ.filter (fun v : V => C.age v = a)).toList) :
    PhaseConclusion N C sample H gamma common r a es vs := by
  constructor
  · intro s
    exact actual_boundary_phase_program N C H gamma common r a es vs he hv s
  · intro s d hs hd
    exact boundary_phase_trace_complete N C H gamma common a es vs he hv s hs hd

theorem twoTip_zero_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2)) :
    PhaseConclusion N2 twoTipCalendar sample registry2 gamma (fun _ => false) r
      0 [] [1,2] :=
  consume_phase N2 twoTipCalendar sample registry2 gamma (fun _ => false) r
    0 [] [1,2] twoTip_zero_exits_perm twoTip_zero_entries_perm

theorem twoTip_root_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2)) :
    PhaseConclusion N2 twoTipCalendar sample registry2 gamma (fun _ => false) r
      2 [0,1] [0] :=
  consume_phase N2 twoTipCalendar sample registry2 gamma (fun _ => false) r
    2 [0,1] [0] twoTip_root_exits_perm twoTip_root_entries_perm

theorem serial_first_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2)) :
    PhaseConclusion N2 serialCalendar sample registry2 gamma (fun _ => false) r
      (-3 / 2) [] [1] :=
  consume_phase N2 serialCalendar sample registry2 gamma (fun _ => false) r
    (-3 / 2) [] [1] serial_first_exits_perm serial_first_entries_perm

theorem serial_middle_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2)) :
    PhaseConclusion N2 serialCalendar sample registry2 gamma (fun _ => false) r
      (1 / 4) [] [2] :=
  consume_phase N2 serialCalendar sample registry2 gamma (fun _ => false) r
    (1 / 4) [] [2] serial_middle_exits_perm serial_middle_entries_perm

theorem serial_root_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid N2 → unitInterval) (r : PositivePairRates (Fin 2)) :
    PhaseConclusion N2 serialCalendar sample registry2 gamma (fun _ => false) r
      (3 / 2) [0,1] [0] :=
  consume_phase N2 serialCalendar sample registry2 gamma (fun _ => false) r
    (3 / 2) [0,1] [0] serial_root_exits_perm serial_root_entries_perm

theorem parallel_zero_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid NP → unitInterval) (r : PositivePairRates (Fin 5)) :
    PhaseConclusion NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
      0 [] [1,4] :=
  consume_phase NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
    0 [] [1,4] parallel_zero_exits_perm parallel_zero_entries_perm

theorem parallel_one_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid NP → unitInterval) (r : PositivePairRates (Fin 5)) :
    PhaseConclusion NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
      1 [4] [3] :=
  consume_phase NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
    1 [4] [3] parallel_one_exits_perm parallel_one_entries_perm

theorem parallel_two_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid NP → unitInterval) (r : PositivePairRates (Fin 5)) :
    PhaseConclusion NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
      2 [2,3] [2] :=
  consume_phase NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
    2 [2,3] [2] parallel_two_exits_perm parallel_two_entries_perm

theorem parallel_root_consumers (sample : Copy → Fin 2)
    (gamma : Hybrid NP → unitInterval) (r : PositivePairRates (Fin 5)) :
    PhaseConclusion NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
      3 [0,1] [0] :=
  consume_phase NP parallelCalendar sample OriginalParallelEpochFixture.registry gamma (fun _ => true) r
    3 [0,1] [0] parallel_root_exits_perm parallel_root_entries_perm

#print axioms twoTip_zero_consumers
#print axioms twoTip_root_consumers
#print axioms serial_first_consumers
#print axioms serial_middle_consumers
#print axioms serial_root_consumers
#print axioms parallel_zero_consumers
#print axioms parallel_one_consumers
#print axioms parallel_two_consumers
#print axioms parallel_root_consumers

end UnifiedLean.G7.OriginalCompletedCalendarPhases

