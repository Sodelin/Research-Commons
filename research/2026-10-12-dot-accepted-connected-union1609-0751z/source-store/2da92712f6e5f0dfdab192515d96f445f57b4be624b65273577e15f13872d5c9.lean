import ActualObservationCutRefinement

/-! Concrete two-cut source refinement inside one actual original epoch.
Contributor: dot / OpenAI,9 October2026. Reuses the proved calendar law;
no new biological boundaries or register draws are introduced. -/
namespace GProgram.G5.TwoCutSourceWord
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.CalendarDecoration GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open scoped Classical NNReal
variable {V E X Tag : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

def taggedWord (N : RootedBinary V E X) (ops : List (ProgramStep N)) (tag : Tag) :=
  ops.map (fun op => (op,tag))

lemma physical_taggedWord (N : RootedBinary V E X) (ops : List (ProgramStep N)) (tag : Tag) :
    physicalOps N (taggedWord N ops tag) = ops := by
  simp [physicalOps,taggedWord,List.map_map,Function.comp_def]

lemma constant_bin_word (N : RootedBinary V E X) (ops : List (ProgramStep N))
    (bin : ℝ → Tag) (tag : Tag) (offset : ℝ)
    (hbin : ∀ a : ℝ, offset < a → a < offset + (programDuration N ops : ℝ) → bin a = tag) :
    wordBinContract N bin (taggedWord N ops tag) offset := by
  induction ops generalizing offset with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | boundary b =>
      change True ∧ wordBinContract N bin (taggedWord N ops tag) offset
      exact ⟨trivial,ih offset hbin⟩
    | interval h =>
      change (∀ a : ℝ, offset < a → a < offset + (h:ℝ) → bin a = tag) ∧
        wordBinContract N bin (taggedWord N ops tag) (offset + (h:ℝ))
      have hd : 0 ≤ (programDuration N ops : ℝ) := (programDuration N ops).coe_nonneg
      have hh : 0 ≤ (h:ℝ) := h.coe_nonneg
      have hb : ∀ a : ℝ, offset < a → a < offset + ((h:ℝ)+(programDuration N ops : ℝ)) → bin a = tag := by
        simpa [programDuration,NNReal.coe_add] using hbin
      constructor
      · intro a ha hz
        apply hb a ha
        linarith
      · apply ih
        intro a ha hz
        apply hb a (by linarith)
        linarith

lemma word_contract_append (N : RootedBinary V E X) (bin : ℝ → Tag)
    (a b : List (ProgramStep N × Tag)) (offset : ℝ)
    (ha : wordBinContract N bin a offset)
    (hb : wordBinContract N bin b (offset + (programDuration N (physicalOps N a) : ℝ))) :
    wordBinContract N bin (a++b) offset := by
  induction a generalizing offset with
  | nil => simpa [physicalOps,programDuration] using hb
  | cons q a ih =>
    rcases q with ⟨op,tag⟩
    change stepBinContract N bin offset op tag ∧ _ at ha ⊢
    refine ⟨ha.1,ih _ ha.2 ?_⟩
    cases op <;> simpa [physicalOps,programDuration,segmentOffset,NNReal.coe_add,add_assoc] using hb

/-- Pure analytical subdivision, preserving the original prefix, suffix,
all original boundary operations and the original parameter/register bank. -/
theorem actual_two_cut_refinement (N : RootedBinary V E X)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0) :
    CutRefines N (pre ++ .interval (a+(b+c)) :: post)
      (pre ++ .interval a :: .interval b :: .interval c :: post) := by
  apply CutRefines.trans (CutRefines.split pre post a (b+c))
  have h := CutRefines.split (pre ++ [.interval a]) post b c
  simpa [List.append_assoc] using h

#print axioms constant_bin_word
#print axioms word_contract_append
#print axioms actual_two_cut_refinement
end GProgram.G5.TwoCutSourceWord

namespace GProgram.G5.TwoCutSourceWord
open MeasureTheory Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open GProgram.G2.CalendarDecoration GProgram.G2.ChronologicalPathReadout
open CloudG3.ActualCalendarEndpointHistory CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCalendarCutContext
open scoped Classical NNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def twoCutBin (left right : ℝ) (x : ℝ) : Fin 3 :=
  if x ≤ left then 0 else if x ≤ right then 1 else 2

lemma two_cut_bin_measurable (left right : ℝ) : Measurable (twoCutBin left right) :=
  Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const)

noncomputable def twoCutWord (N : RootedBinary V E X)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0) : List (ProgramStep N × Fin 3) :=
  taggedWord N (pre ++ [.interval a]) 0 ++
    taggedWord N [.interval b] 1 ++ taggedWord N (.interval c :: post) 2

lemma physical_twoCutWord (N : RootedBinary V E X)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0) :
    physicalOps N (twoCutWord N pre post a b c) =
      pre ++ .interval a :: .interval b :: .interval c :: post := by
  simp [twoCutWord,physicalOps,taggedWord,List.map_append,List.map_map,List.append_assoc,Function.comp_def]

/-- Both legal cut metadata and the bin contract are constructed from the
literal original epoch decomposition; neither is an input law assumption. -/
theorem two_cut_word_contract (N : RootedBinary V E X)
    (pre post : List (ProgramStep N)) (a b c : ℝ≥0) (offset : ℝ) :
    wordBinContract N
      (twoCutBin (offset + (programDuration N pre : ℝ) + (a:ℝ))
        (offset + (programDuration N pre : ℝ) + (a:ℝ) + (b:ℝ)))
      (twoCutWord N pre post a b c) offset := by
  let left := offset + (programDuration N pre : ℝ) + (a:ℝ)
  let right := left + (b:ℝ)
  have h0 : wordBinContract N (twoCutBin left right)
      (taggedWord N (pre ++ [.interval a]) (0 : Fin 3)) offset := by
    apply constant_bin_word
    intro x _ hx
    have hx' : x ≤ left := by
      dsimp [left]
      simp only [program_duration_append,programDuration,add_zero,NNReal.coe_add] at hx
      linarith
    simp [twoCutBin,hx']
  have h1 : wordBinContract N (twoCutBin left right)
      (taggedWord N [.interval b] (1 : Fin 3)) left := by
    apply constant_bin_word
    intro x hx hz
    have hx' : ¬ x ≤ left := not_le_of_gt hx
    have hz' : x ≤ right := by
      dsimp [right]
      simpa only [programDuration,add_zero] using hz.le
    simp [twoCutBin,hx',hz']
  have h2 : wordBinContract N (twoCutBin left right)
      (taggedWord N (.interval c :: post) (2 : Fin 3)) right := by
    apply constant_bin_word
    intro x hx _
    have hr : left ≤ right := by dsimp [right]; exact le_add_of_nonneg_right b.coe_nonneg
    simp [twoCutBin,not_le_of_gt (lt_of_le_of_lt hr hx),not_le_of_gt hx]
  unfold twoCutWord
  rw [List.append_assoc]
  apply word_contract_append
  · exact h0
  · rw [physical_taggedWord,program_duration_append]
    simp only [programDuration,add_zero,NNReal.coe_add]
    rw [←add_assoc]
    change wordBinContract N (twoCutBin left right)
      (taggedWord N [.interval b] 1 ++ taggedWord N (.interval c :: post) 2) left
    apply word_contract_append N _ _ _ left h1
    simpa only [physical_taggedWord,programDuration,add_zero] using h2

variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]
open UnifiedLean.Source.NativePairClockLaw GProgram.G2.SourceFiniteHistory

/-- The constructed word feeds the inherited actual whole-calendar joint law.
The original ops, rates, old genealogy and register are preserved exactly. -/
theorem actual_two_cut_source_joint (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (s : Code N sample) (offset : ℝ) (M : Copy → Copy → ℝ) :
    let left := offset + (programDuration N pre : ℝ) + (a:ℝ)
    let right := left + (b:ℝ)
    CloudG3.CompleteCalendarJointLaw.calendarJointPMF N r (twoCutBin left right)
      (two_cut_bin_measurable left right) (pre ++ .interval (a+(b+c)) :: post) s offset M =
      (sourceHistoryLaw N r (physicalOps N (twoCutWord N pre post a b c)) s).map
        (endpointHistoryReadout N (twoCutWord N pre post a b c) s
          (fun x y => twoCutBin left right (M x y))) := by
  dsimp only
  apply original_gamma_refined_endpoint_history
  · rw [physical_twoCutWord]
    exact actual_two_cut_refinement N pre post a b c
  · exact two_cut_word_contract N pre post a b c offset

#print axioms actual_two_cut_source_joint
#print axioms physical_twoCutWord
#print axioms two_cut_word_contract
end GProgram.G5.TwoCutSourceWord
