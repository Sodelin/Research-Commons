import ResearchCommons.MSCI.JC69CalendarOccupation
import ResearchCommons.MSCI.JC69Source

/-! Original full-calendar/root-clock occupation and labelled tree Fourier
composition. UNCOMPILED, 31 October 2026. Contributor: dot (OpenAI).
The original prefix endpoint fibres and original ancestral clock vectors are
retained. No arbitrary raw-trace horizon law or source likelihood expansion
is assumed. The exact initial forest potential is NOT silently zeroed. -/
noncomputable section
namespace ResearchCommons.MSCI.JC69CompleteClockComposition
set_option backward.isDefEq.respectTransparency false
open GProgram.G2.FaithfulPairAgeDecoration UnifiedLean.Source.SourceCalendarCompatibility
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceLiteralClockEndpoint UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.ActualCalendarTrace GProgram.G2.CalendarDecoration
open GProgram.G2.ChronologicalPathReadout GProgram.G2.CompleteCalendarAttachment
open GProgram.G2.CompleteDecoration GProgram.G2.FiniteAncestralTrace
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualDecorationFold
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open ResearchCommons.MSCI.JC69Occupation ResearchCommons.MSCI.JC69CalendarOccupation
open ResearchCommons.MSCI.JC69Source
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Original-copy labels and occurrence patterns are equivalent on a genuine
complete well-labelled tree; no leaf is removed or duplicated. -/
def fullPatternEquiv (tree : Genealogy Copy) (ht : tree.WellLabelled)
    (hfull : tree.leaves = Finset.univ) : (Copy → Base) ≃ Pattern tree where
  toFun := labelPattern tree
  invFun := patternLabels tree
  left_inv p := by
    funext x
    exact pattern_labels_label_pattern tree p x (by rw [hfull]; exact Finset.mem_univ x)
  right_inv p := label_pattern_pattern_labels tree ht p

/-- Fourier coefficient written on the SAME complete original-copy labels,
not a new scalar observation or an occurrence-only panel. -/
def labelledTreeFourier (L : ℕ) (q : Fin L → Copy → Base) (leafAge : Copy → ℝ)
    (tree : Genealogy Copy) (M : Copy → Copy → ℝ) : ℝ :=
  ∑ p : Fin L → Copy → Base,
    locusLikelihood L tree (clockSurvivals leafAge tree (decode M tree))
      (fun j => labelPattern tree (p j)) *
      ∏ j, ∏ x : Copy, character (q j x) (p j x)

theorem labelled_complete_locus_fourier (L : ℕ) (q : Fin L → Copy → Base)
    (leafAge : Copy → ℝ) (s : State V E Copy) (hs : Valid s)
    (hcard : s.live.card ≤ 1) (l : Copy) (hl : l ∈ s.live)
    (hbal : ∀ j, ∑ x : Copy, q j x = 0) (M : Copy → Copy → ℝ) (T : ℝ) :
    labelledTreeFourier L q leafAge (s.genealogy l) M =
      Real.exp (-((4/3:ℝ) * ∑ j, forestPotential (q j) leafAge s M T)) := by
  have hfull := actual_single_root_covers_original_copies s hs hcard l hl
  let e : (Fin L → Copy → Base) ≃ (Fin L → Pattern (s.genealogy l)) :=
    Equiv.piCongrRight (fun _ => fullPatternEquiv (s.genealogy l) (hs.wellLabelled l hl) hfull)
  unfold labelledTreeFourier
  calc
    _ = ∑ p : Fin L → Copy → Base,
        locusLikelihood L (s.genealogy l)
          (clockSurvivals leafAge (s.genealogy l) (decode M (s.genealogy l))) (e p) *
          ∏ j, patternCharacter (q j) (s.genealogy l) (e p j) := by
      apply Finset.sum_congr rfl
      intro p _
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      change (∏ x : Copy, character (q j x) (p j x)) =
        patternCharacter (q j) (s.genealogy l) (labelPattern (s.genealogy l) (p j))
      rw [label_pattern_character _ _ _ (hs.wellLabelled l hl),hfull]
    _ = ∑ p : Fin L → Pattern (s.genealogy l),
        locusLikelihood L (s.genealogy l)
          (clockSurvivals leafAge (s.genealogy l) (decode M (s.genealogy l))) p *
          ∏ j, patternCharacter (q j) (s.genealogy l) (p j) := by
      exact e.sum_comp (fun p => locusLikelihood L (s.genealogy l)
        (clockSurvivals leafAge (s.genealogy l) (decode M (s.genealogy l))) p *
        ∏ j, patternCharacter (q j) (s.genealogy l) (p j))
    _ = _ := balanced_complete_locus_fourier L q leafAge s hs hcard l hl hbal M T

lemma calendar_time_duration (N : RootedBinary V E X)
    (ops : List (ProgramStep N)) (offset : ℝ) :
    calendarTime N ops offset = offset+(programDuration N ops : ℝ) := by
  induction ops generalizing offset with
  | nil => simp [calendarTime,programDuration]
  | cons op ops ih =>
      cases op <;> simp [calendarTime,segmentOffset,programDuration,ih,add_assoc]

/-- This is the original complete record obtained from the actual ancestral
clock vector, using its existing measurable finite clockCover. -/
def completeClockRecord (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (d : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample) (c : Choice N d → ℝ) :
    CompleteCalendarRecord N sample ops := (d,past,completeAncestralTrace N d c)

/-- Prefix and root costs read the SAME original clocks/trace. The root
horizon is the existing source's clockCover, not a fitted deterministic cap. -/
def completeClockOccupation (N : RootedBinary V E X) {sample : Copy → X}
    (q : Copy → Base) (ops : List (ProgramStep N)) (s d : Code N sample)
    (past : Fin ops.length → SegmentRecord N sample) (c : Choice N d → ℝ) : ℝ :=
  calendarOccupation N q ops s past +
    literalOccupation N q (Fintype.card Copy) (clockCover N d c : ℝ) d c

/-- Exact original prefix-fibre and original-root-clock exposure identity.
No success/absorption assumption is needed for this algebraic identity; its
scientific terminal use below imports the actual existing root suppliers. -/
theorem actual_complete_clock_exposure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (q : Copy → Base) (leafAge : Copy → ℝ)
    (ops : List (ProgramStep N)) (s d : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    ∀ᵐ past ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d},
      ∀ c : Choice N d → ℝ,
        forestPotential q leafAge
          (state (completeEnd N ops (completeClockRecord N ops d past c)))
          (completeMatrix N ops s offset M (completeClockRecord N ops d past c))
          (offset+(programDuration N ops : ℝ)+(clockCover N d c : ℝ)) =
        forestPotential q leafAge (state s) M offset + completeClockOccupation N q ops s d past c := by
  filter_upwards [ae_restrict_of_ae (actual_calendar_exposure N r q leafAge ops s offset M),
    ae_restrict_mem (measurableSet_eq_fun (calendar_end_measurable N ops s) measurable_const)]
    with past hp he
  have he' : calendarEnd N ops s past = d := he
  rw [he',calendar_time_duration] at hp
  intro c
  change forestPotential q leafAge
    (state (traceEndpoint N (Fintype.card Copy) d
      (literalMarkedTrace N (Fintype.card Copy) (clockCover N d c : ℝ) d c).2))
    (foldMatrix N (Fintype.card Copy) d (offset+(programDuration N ops : ℝ))
      (calendarMatrix N ops s offset M past)
      (literalMarkedTrace N (Fintype.card Copy) (clockCover N d c : ℝ) d c).2)
    ((offset+(programDuration N ops : ℝ))+(clockCover N d c : ℝ)) = _
  rw [actual_literal_occupation_identity,hp]
  unfold completeClockOccupation
  ring

section Nonempty
variable [Nonempty Copy]

/-- Generic branch composition whose root-support premise is an EXISTING
source-program support property. The original-calendar theorem below
supplies it directly; no desired Fourier/quotient statement is assumed. -/
theorem complete_clock_fourier_from_root_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x : Copy, q j x = 0) (leafAge : Copy → ℝ)
    (ops : List (ProgramStep N)) (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ)
    (hroot : ∀ d, d ∈ (sourceProgram N r ops s).support → AncestralRoot N d)
    (d : Code N sample) :
    ∀ᵐ past ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d},
      ∀ᵐ c ∂currentPairClockMeasure N r d,
        labelledTreeFourier L q leafAge
          ((state (completeEnd N ops (completeClockRecord N ops d past c))).genealogy
            (selectedRoot N (completeEnd N ops (completeClockRecord N ops d past c))))
          (completeMatrix N ops s offset M (completeClockRecord N ops d past c)) =
        Real.exp (-((4/3:ℝ) * ∑ j,
          (forestPotential (q j) leafAge (state s) M offset +
            completeClockOccupation N (q j) ops s d past c))) := by
  by_cases hd : sourceProgram N r ops s d = 0
  · have hz : (actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d} = 0 :=
      Measure.restrict_eq_zero.mpr ((calendar_end_fibre_mass N r ops s d).trans hd)
    simp [hz]
  · have hr := hroot d ((PMF.mem_support_iff _ _).mpr hd)
    have hE := ae_all_iff.mpr (fun j : Fin L =>
      actual_complete_clock_exposure N r (q j) leafAge ops s d offset M)
    filter_upwards [hE] with past hp
    filter_upwards [actual_current_clock_regular_ae N r d] with c hc
    obtain ⟨e,he,_,hcard⟩ := complete_ancestral_trace_terminal N d c hr hc
    have hg := marked_trace_success_on_regular N (Fintype.card Copy) d (clockCover N d c : ℝ)
      c (Finset.card_le_univ d.val.live) hc
    have he' : traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2 = e := by
      simpa only [decodedEndpoint,completeAncestralTrace,hg,if_true,Option.some.injEq] using he
    let z := completeClockRecord N ops d past c
    let out := completeEnd N ops z
    have hcard' : (state out).live.card ≤ 1 := by
      change liveCard (traceEndpoint N (Fintype.card Copy) d (completeAncestralTrace N d c).2) ≤ 1
      rw [he']
      exact hcard
    rw [labelled_complete_locus_fourier L q leafAge (state out) out.property.forest
      hcard' (selectedRoot N out) (selected_root_live N out) hbal
      (completeMatrix N ops s offset M z)
      (offset+(programDuration N ops : ℝ)+(clockCover N d c : ℝ))]
    apply congrArg (fun value : ℝ => Real.exp (-((4/3:ℝ)*value)))
    exact Finset.sum_congr rfl (fun j _ => hp j c)

/-- Actual original-calendar/root-clock scientific composition on ALL
original copy labels. Its ancestral-root supplier is discharged by the
original initialized calendar, not passed as a new contract assumption.
The exact initial potential is retained, including nonzero leaf-age offsets. -/
theorem actual_original_complete_clock_fourier (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (hbal : ∀ j, ∑ x : Copy, q j x = 0)
    (d : Code N sample) :
    let ops := compiledCalendarProgram N C H gamma common
    let s := initialCode N sample register
    let leafAge := fun x : Copy => C.age (N.leaf (sample x))
    let M := fun x (_ : Copy) => leafAge x
    ∀ᵐ past ∂(actualCalendarTraceLaw N r ops s).restrict {past | calendarEnd N ops s past = d},
      ∀ᵐ c ∂currentPairClockMeasure N r d,
        labelledTreeFourier L q leafAge
          ((state (originalPoint N C sample register H gamma common
            (completeClockRecord N ops d past c)).1).genealogy
            (selectedRoot N (originalPoint N C sample register H gamma common
              (completeClockRecord N ops d past c)).1))
          (originalPoint N C sample register H gamma common
            (completeClockRecord N ops d past c)).2 =
        Real.exp (-((4/3:ℝ) * ∑ j,
          (forestPotential (q j) leafAge (state s) M (firstOriginalDate N C) +
            completeClockOccupation N (q j) ops s d past c))) := by
  apply complete_clock_fourier_from_root_support N r L q hbal
    (fun x => C.age (N.leaf (sample x))) (compiledCalendarProgram N C H gamma common)
    (initialCode N sample register) (firstOriginalDate N C)
    (fun x _ => C.age (N.leaf (sample x)))
  intro e he
  exact initialized_original_calendar_ancestral_support N C sample register H gamma common r he

end Nonempty
#print axioms labelled_complete_locus_fourier
#print axioms calendar_time_duration
#print axioms actual_complete_clock_exposure
#print axioms actual_original_complete_clock_fourier
end ResearchCommons.MSCI.JC69CompleteClockComposition
