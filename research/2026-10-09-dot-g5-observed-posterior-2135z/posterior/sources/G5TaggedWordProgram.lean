import G5ConstantTagSource
import G5TwoCutSourceWord

/-! Literal endpoint-history bookkeeping for the two-cut posterior use-site.
Contributor: dot / OpenAI,9 October2026. -/
namespace GProgram.G5.TaggedWordProgram
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.G6.BinHistory
open GProgram.G2.SourceFiniteHistory
open CloudG3.ActualCalendarEndpointHistory
open GProgram.G5.ConstantTagSource GProgram.G5.TwoCutSourceWord
open scoped Classical NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def wordProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N × Tag) → Code N sample →
      (Copy → Copy → Tag) → PMF (Code N sample × (Copy → Copy → Tag))
  | [],s,B => PMF.pure (s,B)
  | q::word,s,B => (sourceProgramStep N r q.1 s).bind (fun d =>
      wordProgram N r word d (endpointStepTags N q.1 q.2 s d B))

theorem actual_history_reader_is_wordProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (word : List (ProgramStep N × Tag))
    (s : Code N sample) (B : Copy → Copy → Tag) :
    (sourceHistoryLaw N r (physicalOps N word) s).map (endpointHistoryReadout N word s B) =
      wordProgram N r word s B := by
  induction word generalizing s B with
  | nil =>
    change (PMF.pure (fun i : Fin 0 => Fin.elim0 i)).map (fun _ => (s,B)) = PMF.pure (s,B)
    rw [PMF.pure_map]
  | cons q word ih =>
    change ((sourceProgramStep N r q.1 s).bind (fun d =>
      (sourceHistoryLaw N r (physicalOps N word) d).map (Fin.cons d))).map
        (endpointHistoryReadout N (q::word) s B) =
      (sourceProgramStep N r q.1 s).bind (fun d =>
        wordProgram N r word d (endpointStepTags N q.1 q.2 s d B))
    rw [PMF.map_bind]
    congr 1
    funext d
    rw [PMF.map_comp]
    exact ih d (endpointStepTags N q.1 q.2 s d B)

theorem wordProgram_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (a b : List (ProgramStep N × Tag))
    (s : Code N sample) (B : Copy → Copy → Tag) :
    wordProgram N r (a++b) s B =
      (wordProgram N r a s B).bind (fun q => wordProgram N r b q.1 q.2) := by
  induction a generalizing s B with
  | nil => simp only [List.nil_append,wordProgram,PMF.pure_bind]
  | cons q a ih =>
    simp only [List.cons_append,wordProgram,PMF.bind_bind]
    congr 1
    funext d
    exact ih d (endpointStepTags N q.1 q.2 s d B)

lemma tagged_wordProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (tag : Tag)
    (s : Code N sample) (B : Copy → Copy → Tag) :
    wordProgram N r (taggedWord N ops tag) s B = constantTagProgram N r tag ops s B := by
  induction ops generalizing s B with
  | nil => rfl
  | cons op ops ih =>
    simp only [taggedWord,List.map_cons,wordProgram,constantTagProgram]
    congr 1
    funext d
    exact ih d (endpointStepTags N op tag s d B)

/-- Every finite source block with one time-bin label collapses to its true
initial/final Code pair, including its original routing boundaries. -/
theorem actual_tagged_word_collapse (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (tag : Tag)
    (s : Code N sample) (B : Copy → Copy → Tag) :
    wordProgram N r (taggedWord N ops tag) s B =
      (sourceProgram N r ops s).map (fun d => (d,tagUpdate N s d tag B)) := by
  rw [tagged_wordProgram,actual_constant_tag_collapse]

/-- The constructed two-cut history is exactly three original source phases;
all internal constant-bin paths disappear without changing their Code laws. -/
theorem actual_two_cut_three_phase (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (pre post : List (ProgramStep N)) (a b c : ℝ≥0)
    (s : Code N sample) (B : Copy → Copy → Fin 3) :
    wordProgram N r (twoCutWord N pre post a b c) s B =
      (sourceProgram N r (pre ++ [.interval a]) s).bind (fun d =>
        (sourceProgram N r [.interval b] d).bind (fun e =>
          (sourceProgram N r (.interval c :: post) e).map (fun f =>
            (f, tagUpdate N e f (2 : Fin 3)
              (tagUpdate N d e (1 : Fin 3) (tagUpdate N s d (0 : Fin 3) B)))))) := by
  simp only [twoCutWord,wordProgram_append,actual_tagged_word_collapse,
    PMF.bind_map,PMF.map_bind,PMF.bind_bind]
  simp only [Function.comp_apply,PMF.bind_map]
  rfl

#print axioms actual_two_cut_three_phase
#print axioms actual_history_reader_is_wordProgram
#print axioms wordProgram_append
#print axioms actual_tagged_word_collapse
end GProgram.G5.TaggedWordProgram
