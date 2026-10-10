import G7EdgeExposureAccounting
import UnifiedLean.Source.SourceCalendarTiming

/-! Closing the actual calendar accumulator: all original node/edge dates are
used, and the emitted bank is the literal whole-edge exposure. Uncompiled
internal component of the one full gathering endpoint, dot 2026-10-10. -/
namespace GProgram.G7.CalendarExposureClosedForm
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open GProgram.G7.OriginalEdgeGathering GProgram.G7.ActualCalendarGathering
open GProgram.G7.EdgeExposureAccounting
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

lemma gatherFrom_append (N : RootedBinary V E X) (r : PositivePairRates E)
    (w : ExposureBank E) (first last : List (Event V E)) :
    gatherFrom N r w (first++last) =
      ((gatherFrom N r (gatherFrom N r w last).1 first).1,
        (gatherFrom N r (gatherFrom N r w last).1 first).2 ++ (gatherFrom N r w last).2) := by
  induction first with
  | nil => simp [gatherFrom]
  | cons op ops ih => cases op <;> simp only [List.cons_append,gatherFrom,ih,List.cons_append]

lemma gathered_exit_batch (N : RootedBinary V E X) (r : PositivePairRates E)
    (w : ExposureBank E) (edges : List E) :
    (gatherFrom N r w (edges.map Event.exit)).2 = edges.map Gathered.exit := by
  induction edges with
  | nil => rfl
  | cons e edges ih => simp only [List.map_cons,gatherFrom,ih]

lemma gather_node_batch (N : RootedBinary V E X) (r : PositivePairRates E)
    (w : ExposureBank E) (nodes : List V) (hn : nodes.Nodup) :
    gatherFrom N r w (nodes.map Event.node) =
      (retain (fun i => ∀ v ∈ nodes, ¬ Opens N v i) w,
        nodes.map (fun v => Gathered.node v (retain (Opens N v) w))) := by
  induction nodes with
  | nil =>
    apply Prod.ext
    · funext i; simp [gatherFrom,retain]
    · rfl
  | cons v nodes ih =>
    have hp := List.nodup_cons.mp hn
    simp only [List.map_cons,gatherFrom,ih hp.2]
    have he : retain (Opens N v) (retain (fun i => ∀ u ∈ nodes, ¬ Opens N u i) w) =
        retain (Opens N v) w := by
      funext i
      by_cases hv : Opens N v i
      · have hall : ∀ u ∈ nodes, ¬ Opens N u i := by
          intro u hu hui
          have hne : v ≠ u := by intro h; subst u; exact hp.1 hu
          exact opens_disjoint N hne i ⟨hv,hui⟩
        simp [retain,hv,hall]
      · simp [retain,hv]
    rw [he]
    apply Prod.ext
    · funext i
      simp only [retain,List.mem_cons,forall_eq_or_imp]
      by_cases hv : Opens N v i <;>
        by_cases hr : ∀ u ∈ nodes, ¬ Opens N u i <;> simp [hv,hr]
    · rfl

noncomputable def gatheredBoundary (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (w : ExposureBank E) : List (Gathered V E) :=
  ((Finset.univ.filter (fun e : E => C.age (N.graph.source e)=a)).toList.map Gathered.exit) ++
  ((Finset.univ.filter (fun v : V => C.age v=a)).toList.map
    (fun v => Gathered.node v (retain (Opens N v) w)))

lemma gathered_actual_boundary (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (a : ℝ) (w : ExposureBank E) :
    (gatherFrom N r w (boundaryEvents N C a)).2 = gatheredBoundary N C a w := by
  unfold boundaryEvents gatheredBoundary
  rw [gatherFrom_append,gathered_exit_batch,
    gather_node_batch N r w _ (Finset.nodup_toList _)]

/-- Whole finite-edge coordinates plus a zero FINITE root contribution. The
infinite ancestral completion is appended separately and is never zeroed. -/
noncomputable def wholeEdgeBank (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) : ExposureBank E
  | none => 0
  | some e => r.edge e * (C.age (N.graph.source e)-C.age (N.graph.target e))

/-- Exact invariant of a suffix of the sorted complete original-date list. -/
def CompleteDates (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) (dates : List ℝ) : Prop :=
  (a::dates).Pairwise (· < ·) ∧
    (∀ v : V, a ≤ C.age v → C.age v ∈ a::dates) ∧
    (∀ b ∈ a::dates, ∃ v : V, C.age v=b)

lemma completeDates_tail (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) (bs : List ℝ) (hc : CompleteDates N C a (b::bs)) : CompleteDates N C b bs := by
  have hp := List.pairwise_cons.mp hc.1
  have hab : a < b := hp.1 b (by simp)
  refine ⟨hp.2,?_,?_⟩
  · intro v hv
    have hm := hc.2.1 v (hab.le.trans hv)
    rcases List.mem_cons.mp hm with he | hm
    · exact False.elim ((not_lt_of_ge hv) (he ▸ hab))
    · exact hm
  · intro c hm
    exact hc.2.2 c (List.mem_cons_of_mem a hm)

/-- Calendar completeness DERIVES the scheduled exit required by the telescope,
and root maximality DERIVES that no finite root interval is being discarded. -/
theorem actual_node_bank_is_whole_edge (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (a : ℝ) (dates : List ℝ) (hc : CompleteDates N C a dates)
    (v : V) (hv : C.age v=a) :
    retain (Opens N v) (gather N r (tailEvents N C a dates)).1 =
      retain (Opens N v) (wholeEdgeBank N C r) := by
  funext i
  by_cases ho : Opens N v i
  · simp only [retain,if_pos ho]
    cases i with
    | none =>
      have hroot : v = N.root := ho
      have he : dates = [] := by
        cases hdates : dates with
        | nil => rfl
        | cons b bs =>
          have hab := (List.pairwise_cons.mp hc.1).1 b (by simp [hdates])
          obtain ⟨u,hu⟩ := hc.2.2 b (by simp [hdates])
          have hur := original_root_latest N C u
          rw [←hroot,hv,hu] at hur
          exact False.elim ((not_lt_of_ge hur) hab)
      simp [he,tailEvents,gather,wholeEdgeBank]
    | some e =>
      have ht : v = N.graph.target e := ho
      have ha : a = C.age (N.graph.target e) := by rw [←ht,hv]
      have hedge : C.age (N.graph.target e) < C.age (N.graph.source e) := C.edge_older e
      have hm := hc.2.1 (N.graph.source e) (by rw [ha]; exact hedge.le)
      have hp : C.age (N.graph.source e) ∈ dates := by
        rcases List.mem_cons.mp hm with he | hm
        · rw [ha] at he
          exact False.elim ((ne_of_gt hedge) he)
        · exact hm
      rw [ha] at hc ⊢
      exact actual_entry_tail_exposure N C r e dates hc.1 hp
  · simp [retain,ho]

lemma actual_boundary_bank_is_whole_edge (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (a : ℝ) (dates : List ℝ) (hc : CompleteDates N C a dates) :
    gatheredBoundary N C a (gather N r (tailEvents N C a dates)).1 =
      gatheredBoundary N C a (wholeEdgeBank N C r) := by
  unfold gatheredBoundary
  congr 1
  apply List.map_congr_left
  intro v hv
  have hage := (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
  rw [actual_node_bank_is_whole_edge N C r a dates hc v hage]

noncomputable def wholeEdgeFrontier (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (dates : List ℝ) : List (Gathered V E) :=
  dates.flatMap (fun a => gatheredBoundary N C a (wholeEdgeBank N C r))

/-- Closed form for the ENTIRE generated suffix, rather than one coordinate.
All emitted banks are shared original whole-edge exposures. -/
theorem complete_date_word_gathered (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (a : ℝ) (dates : List ℝ) (hc : CompleteDates N C a dates) :
    (gather N r (boundaryEvents N C a ++ tailEvents N C a dates)).2 =
      wholeEdgeFrontier N C r (a::dates) := by
  induction dates generalizing a with
  | nil =>
    rw [gather_append,gathered_actual_boundary,
      actual_boundary_bank_is_whole_edge N C r a [] hc]
    simp [tailEvents,gather,wholeEdgeFrontier]
  | cons b bs ih =>
    rw [gather_append,gathered_actual_boundary,
      actual_boundary_bank_is_whole_edge N C r a (b::bs) hc]
    simp only [tailEvents,gather]
    rw [ih b (completeDates_tail N C a b bs hc)]
    rfl

open UnifiedLean.Source.SourceCalendarCompatibility

lemma original_complete_dates (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (dates : List ℝ) (h : sortedOriginalDates N C = a::dates) :
    CompleteDates N C a dates := by
  refine ⟨by rw [←h]; exact original_dates_strict N C,?_,?_⟩
  · intro v _
    rw [←h]
    exact original_date_scheduled N C v
  · intro b hb
    rw [←h,sortedOriginalDates,Finset.mem_sort] at hb
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hb
    exact ⟨v,hv⟩

/-- The complete generated ORIGINAL calendar gathers to one whole-edge factor
at each original entry, with all parallel edge exit occurrences retained. -/
theorem actual_calendar_gathered_closed_form (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) :
    (gather N r (calendarEvents N C)).2 = wholeEdgeFrontier N C r (sortedOriginalDates N C) := by
  unfold calendarEvents
  cases h : sortedOriginalDates N C with
  | nil => simp [gather,wholeEdgeFrontier]
  | cons a dates => exact complete_date_word_gathered N C r a dates (original_complete_dates N C a dates h)

open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization

variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- Actual calendar source law in full whole-edge closed form. This still
retains the calendar-induced valid topological evaluation order; comparison
of different orders is the final source-domain assembly step. -/
theorem actual_initialized_whole_edge_frontier (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (d : Code N sample) :
    (sourceProgram N r (compiledCalendarProgram N C H gamma common) (initialCode N sample register) d).toReal =
      (initialRow N sample register *
        ((wholeEdgeFrontier N C r (sortedOriginalDates N C)).map (gatheredMatrix N H gamma common)).prod) () d := by
  rw [actual_initialized_calendar_gathering,actual_calendar_gathered_closed_form]

theorem actual_natural_whole_edge_frontier (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (d : Code N sample) :
    (naturalCalendarLaw N C sample H p common r d).toReal =
      ∑ register : V → Bool, (originalRegisterPMF N p register).toReal *
        (initialRow N sample register *
          ((wholeEdgeFrontier N C r (sortedOriginalDates N C)).map
            (gatheredMatrix N H (originalGamma p) common)).prod) () d := by
  rw [actual_natural_calendar_gathering,actual_calendar_gathered_closed_form]

end GProgram.G7.CalendarExposureClosedForm
