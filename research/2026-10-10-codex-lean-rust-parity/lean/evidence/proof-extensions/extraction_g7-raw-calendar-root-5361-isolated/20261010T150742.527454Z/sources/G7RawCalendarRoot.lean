import G7RawProgramLocations
import G7EffectiveCompletedWordCoefficients

/-!
# Complete original calendar puts every raw natural endpoint at its root

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses the oldest BoundaryReady/AfterExits/AfterNodes/FutureComplete pointwise
invariants and the unchanged original compiler. Existing indexedSymbols and
actual_calendar_schema identify the raw word's instantiated list exactly.
Actual singleton-tip initialization is essential. Zero-polynomial raw rows
are included; stochastic positive support is never substituted for raw support.
No native date-representative, slot-index or entering-encoder binding is claimed.
Draft pending sole-scheduler kernel checking and complete owned audit.
-/
namespace GProgram.G7.RawCalendarRoot
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.OriginalCalendarPattern
open GProgram.G7.EffectiveFullEpochCoefficients GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectiveInitializationCoefficients GProgram.G7.SparseWordComposition
open GProgram.G7.EffectiveWordCoefficients GProgram.G7.EffectiveCompletedWordCoefficients
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.CompletedCalendarPolynomial
open GProgram.G7.RawProgramLocations
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- All raw traces through an exit phase remove every scheduled occurrence.
This is independent of the coefficient of each raw row. -/
theorem exit_trace_list (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a : ℝ} (es done : List E)
    (he : ∀ e ∈ es, C.age (N.graph.source e) = a) (s : Code N sample)
    (hs : BoundaryReady N C a (state s))
    (hno : ∀ x : Copy, ∀ e ∈ done, copyLocation (state s) x ≠ .edge e)
    {d : Code N sample}
    (hd : programTrace N (es.map (fun e => .boundary (.exit e))) s d) :
    BoundaryReady N C a (state d) ∧
      ∀ x : Copy, ∀ e ∈ done ++ es, copyLocation (state d) x ≠ .edge e := by
  induction es generalizing done s with
  | nil =>
      have hds : d = s := hd
      subst d
      exact ⟨hs,by simpa using hno⟩
  | cons e es ih =>
      change ∃ m, programMovement N (.boundary (.exit e)) s m ∧
        programTrace N (es.map (fun e => .boundary (.exit e))) m d at hd
      obtain ⟨m,hm,hdm⟩ := hd
      have hloc : ∀ x : Copy,
          copyLocation (state m) x = copyLocation (state (exitCode N s e)) x :=
        fun x => (hm x).trans (exitCode_copyLocation N s e x).symm
      have hready : BoundaryReady N C a (state m) := by
        intro x
        rw [hloc x]
        exact exit_preserves_ready N C s e (he e (by simp)) hs x
      have hdone : ∀ x : Copy, ∀ f ∈ done ++ [e], copyLocation (state m) x ≠ .edge f := by
        intro x f hf
        rw [hloc x]
        rcases List.mem_append.mp hf with hf | hf
        · exact exit_never_creates_edge N s e f x (hno x f hf)
        · have hfe : f = e := by simpa using hf
          subst f
          exact exit_removes_edge N s e x
      have h := ih (done ++ [e]) (fun f hf => he f (List.mem_cons_of_mem e hf))
        m hready hdone hdm
      refine ⟨h.1,?_⟩
      intro x f hf
      apply h.2 x f
      simpa only [List.append_assoc,List.singleton_append] using hf

theorem exit_trace_batch (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (a : ℝ) (s : Code N sample)
    (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : programTrace N
      ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList.map
        (fun e => .boundary (.exit e))) s d) : AfterExits N C a (state d) := by
  let es := (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList
  have hh := exit_trace_list N C es [] (by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x e hp
  have hbound := hh.1 x
  rw [hp] at hbound
  have hne : C.age (N.graph.source e) ≠ a := by
    intro he
    have hm : e ∈ es := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    exact hh.2 x e (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound.2).resolve_right hne.symm

theorem node_trace_list (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) {a : ℝ} (vs done : List V)
    (hv : ∀ v ∈ vs, C.age v = a) (s : Code N sample)
    (hs : AfterExits N C a (state s))
    (hno : ∀ x : Copy, ∀ v ∈ done, copyLocation (state s) x ≠ .node v)
    {d : Code N sample}
    (hd : programTrace N (vs.map (fun v =>
      .boundary (originalNodeOperation N H gamma common v))) s d) :
    AfterExits N C a (state d) ∧
      ∀ x : Copy, ∀ v ∈ done ++ vs, copyLocation (state d) x ≠ .node v := by
  induction vs generalizing done s with
  | nil =>
      have hds : d = s := hd
      subst d
      exact ⟨hs,by simpa using hno⟩
  | cons v vs ih =>
      change ∃ m, programMovement N (.boundary (originalNodeOperation N H gamma common v)) s m ∧
        programTrace N (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) m d at hd
      obtain ⟨m,hm,hdm⟩ := hd
      have hmove := (programMovement_original_node N H gamma common v s m).mp hm
      have hmexits : AfterExits N C a (state m) := by
        constructor
        · intro x
          exact (node_move_preserves_after_exits N C (hv v (by simp))
            (hs.1 x) (hs.2 x) (hmove x)).1
        · intro x
          exact (node_move_preserves_after_exits N C (hv v (by simp))
            (hs.1 x) (hs.2 x) (hmove x)).2
      have hdone : ∀ x : Copy, ∀ u ∈ done ++ [v], copyLocation (state m) x ≠ .node u := by
        intro x u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact node_move_never_creates_node N (hmove x) (hno x u hu)
        · have huv : u = v := by simpa using hu
          subst u
          exact node_move_removes_node N (hmove x)
      have h := ih (done ++ [v]) (fun u hu => hv u (List.mem_cons_of_mem v hu))
        m hmexits hdone hdm
      refine ⟨h.1,?_⟩
      intro x u hu
      apply h.2 x u
      simpa only [List.append_assoc,List.singleton_append] using hu

theorem node_trace_batch (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (s : Code N sample)
    (hs : AfterExits N C a (state s)) {d : Code N sample}
    (hd : programTrace N
      ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
        (fun v => .boundary (originalNodeOperation N H gamma common v))) s d) :
    AfterNodes N C a (state d) := by
  let vs := (Finset.univ.filter (fun v : V => C.age v = a)).toList
  have hh := node_trace_list N C H gamma common vs [] (by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2) s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x v hp
  have hbound := hh.1.1 x
  rw [hp] at hbound
  have hne : C.age v ≠ a := by
    intro hv
    have hm : v ∈ vs := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
    exact hh.2 x v (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound).resolve_right hne.symm

theorem boundary_trace_batch (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) (s : Code N sample)
    (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : programTrace N (boundaryOperations N C H gamma common a) s d) :
    AfterNodes N C a (state d) := by
  rw [boundaryOperations,programTrace_append] at hd
  obtain ⟨m,hm,hdm⟩ := hd
  exact node_trace_batch N C H gamma common a m (exit_trace_batch N C a s hs hm) hdm

/-- The inherited complete sorted tail is sufficient for every structural
trace, with no PMF support or coefficient hypothesis. -/
theorem calendar_tail_trace (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dates : List ℝ) (a : ℝ)
    (hfuture : FutureComplete N C a dates) (hordered : dates.Pairwise (· < ·))
    (hafter : ∀ b ∈ dates, a < b) (s : Code N sample)
    (hs : AfterNodes N C a (state s)) {d : Code N sample}
    (hd : programTrace N (calendarTail N C H gamma common a dates) s d) :
    AfterNodes N C (finalDate a dates) (state d) ∧ ∀ v : V, C.age v ≤ finalDate a dates := by
  induction dates generalizing a s with
  | nil =>
      have hds : d = s := hd
      subst d
      refine ⟨hs,?_⟩
      intro v
      by_contra hv
      exact List.not_mem_nil (hfuture v (lt_of_not_ge hv))
  | cons b bs ih =>
      have hab : a < b := hafter b (by simp)
      have hbs := List.pairwise_cons.mp hordered
      have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v hv) with he | he
        · exact he.ge
        · exact (hbs.1 _ he).le
      have hepoch := after_nodes_to_epoch N C hs hgap
      change ∃ m, programMovement N (.interval (Real.toNNReal (b-a))) s m ∧
        programTrace N (boundaryOperations N C H gamma common b ++
          calendarTail N C H gamma common b bs) m d at hd
      obtain ⟨m,hm,hdm⟩ := hd
      have hmepoch : EpochCompatible N C a b (state m) := by
        intro x
        rw [hm x]
        exact hepoch x
      rw [programTrace_append] at hdm
      obtain ⟨z,hz,hdz⟩ := hdm
      have hzphysical := boundary_trace_batch N C H gamma common b m
        (epoch_to_next_ready N C hmepoch hab.le) hz
      have hnext : FutureComplete N C b bs := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v (hab.trans hv)) with he | he
        · exact False.elim ((ne_of_gt hv) he)
        · exact he
      exact ih b hnext hbs.2 hbs.1 z hzphysical hdz

/-- Same actual singleton-tip initialization and complete original agenda as
the old source theorem; the conclusion now covers every raw location trace. -/
theorem initialized_calendar_trace_root (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) {d : Code N sample}
    (hd : programTrace N (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register) d) : AncestralRoot N d := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro h
    have hm := original_date_scheduled N C N.root
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have hfirst : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  have hordered := original_dates_strict N C
  rw [heq] at hordered
  have hp := List.pairwise_cons.mp hordered
  have hfuture : FutureComplete N C a dates := by
    intro v hv
    have hm := original_date_scheduled N C v
    rw [heq] at hm
    rcases List.mem_cons.mp hm with he | he
    · exact False.elim ((ne_of_gt hv) he)
    · exact he
  have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
    rw [hfirst]
    exact actual_initial_calendar_boundary N C sample register
  rw [compiledCalendarProgram,heq,programTrace_append] at hd
  obtain ⟨s,hs,hds⟩ := hd
  have hstart := boundary_trace_batch N C H gamma common a _ hready hs
  have hfinal := calendar_tail_trace N C H gamma common dates a hfuture hp.2 hp.1 s hstart hds
  intro x
  have hreadyFinal := hfinal.1.1.1 x
  cases hloc : copyLocation (state d) x with
  | node v => exact False.elim (not_lt_of_ge (hfinal.2 v) (hfinal.1.2 x v hloc))
  | edge e => exact False.elim (not_lt_of_ge (hfinal.2 (N.graph.source e)) (hfinal.1.1.2 x e hloc))
  | rootPopulation v =>
      rw [hloc] at hreadyFinal
      exact congrArg Location.rootPopulation hreadyFinal.1

/-- All raw naturally initialized coefficient rows of the actual generated
calendar word have original ancestral-root support, including polynomial-zero
rows. SameOrder retiming changes neither original IDs nor the shared register. -/
theorem natural_calendar_raw_root (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (row : Code N sample × Sparse (WordVariable N (IntervalOccurrence (calendarSchema N C))))
    (hrow : row ∈ naturalWordRows N sample H common (indexedSymbols (calendarSchema N C))) :
    AncestralRoot N row.1 := by
  change row ∈ bindRows (initialRows N sample Sum.inr)
    (wordRows N H common (indexedSymbols (calendarSchema N C))) at hrow
  rcases List.mem_flatMap.mp hrow with ⟨a,ha,hrow⟩
  rcases List.mem_map.mp hrow with ⟨b,hb,he⟩
  rw [← he]
  have ht := wordRows_trace N H (originalGamma p) common
    (duration N D (calendarSchema N C)) (indexedSymbols (calendarSchema N C)) a.1 b hb
  have hi : instantiateGamma N H (originalGamma p) common (duration N D (calendarSchema N C)) =
      instantiateSymbol N H p common (duration N D (calendarSchema N C)) := by
    funext op
    cases op <;> rfl
  rw [hi,indexedSymbols_instantiates,actual_calendar_schema N C D h H p common] at ht
  rcases List.mem_map.mp ha with ⟨coin,_,ha⟩
  rw [← ha,initialCodeEffective_eq] at ht
  exact initialized_calendar_trace_root N D sample (originalRegisterEffective N coin)
    H (originalGamma p) common ht

variable [Nonempty Copy]

/-- The previously explicit all-raw-root premise is discharged for the actual
complete natural calendar. This is an entire rational coefficient identity. -/
theorem polynomial_generated_completedRows (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (b : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ)
      (completedNaturalWordRows N sample H common (indexedSymbols (calendarSchema N C))) b) =
      completedPolynomial N (naturalWordPolynomial N sample H common
        (indexedSymbols (calendarSchema N C))) b :=
  polynomial_completedNaturalWordRows N sample H common (indexedSymbols (calendarSchema N C))
    (fun row hrow => natural_calendar_raw_root N C D h sample H p common row hrow) r b

#print axioms exit_trace_batch
#print axioms node_trace_batch
#print axioms calendar_tail_trace
#print axioms initialized_calendar_trace_root
#print axioms natural_calendar_raw_root
#print axioms polynomial_generated_completedRows
end GProgram.G7.RawCalendarRoot
