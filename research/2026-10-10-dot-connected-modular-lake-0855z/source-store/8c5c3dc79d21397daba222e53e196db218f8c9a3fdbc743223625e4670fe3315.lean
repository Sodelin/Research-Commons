import G5SourcePairPersistence
import ActualCalendarEndpointHistory

/-! Exact constant-bin collapse of the original source endpoint history.
Contributor: dot / OpenAI,9 October2026. A posterior-use-site proof, not a new source law. -/
namespace GProgram.G5.ConstantTagSource
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.BinHistory CloudG3.LiteralSameBinTrace
open GProgram.G5.SourcePairPersistence
open CloudG3.ActualCalendarEndpointHistory
open scoped Classical NNReal
variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma bind_eq_of_support {A B : Type*} (p : PMF A) (f g : A → PMF B)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ((PMF.mem_support_iff _ _).mpr ha)]

lemma map_eq_of_support {A B : Type*} (p : PMF A) (f g : A → B)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g := by
  change p.bind (fun a => PMF.pure (f a)) = p.bind (fun a => PMF.pure (g a))
  apply bind_eq_of_support
  intro a ha
  rw [h a ha]

lemma actual_step_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s d : Code N sample)
    (hd : d ∈ (sourceProgramStep N r op s).support) : RelationMonotone N s d := by
  cases op with
  | interval t => exact source_epoch_relation N r t s d hd
  | boundary op =>
    intro x y hxy
    rw [boundary_ancestor_eq N op s d hd]
    exact hxy

lemma actual_step_tags (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (tag : Tag) (s d : Code N sample)
    (B : Copy → Copy → Tag) (hd : d ∈ (sourceProgramStep N r op s).support) :
    endpointStepTags N op tag s d B = tagUpdate N s d tag B := by
  cases op with
  | interval t => rfl
  | boundary op =>
    unfold endpointStepTags tagUpdate
    rw [boundary_ancestor_eq N op s d hd]
    simp

noncomputable def constantTagProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) :
    List (ProgramStep N) → Code N sample → (Copy → Copy → Tag) →
      PMF (Code N sample × (Copy → Copy → Tag))
  | [],s,B => PMF.pure (s,B)
  | op::ops,s,B => (sourceProgramStep N r op s).bind (fun d =>
      constantTagProgram N r tag ops d (endpointStepTags N op tag s d B))

/-- Old pair relations are derived from the actual source support. Thus a
whole constant-bin program writes each newly merged pair's tag exactly once. -/
theorem actual_constant_tag_collapse (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (tag : Tag) (ops : List (ProgramStep N))
    (s : Code N sample) (B : Copy → Copy → Tag) :
    constantTagProgram N r tag ops s B =
      (sourceProgram N r ops s).map (fun d => (d,tagUpdate N s d tag B)) := by
  induction ops generalizing s B with
  | nil => simp [constantTagProgram,sourceProgram,PMF.pure_map,tag_update_self]
  | cons op ops ih =>
    simp only [constantTagProgram,sourceProgram,PMF.map_bind]
    apply bind_eq_of_support
    intro d hd
    rw [ih,actual_step_tags N r op tag s d B hd]
    apply map_eq_of_support
    intro e he
    congr 1
    exact same_bin_update_comp N s d e tag B
      (actual_step_relation N r op s d hd) (source_program_relation N r ops d e he)

#print axioms actual_constant_tag_collapse
end GProgram.G5.ConstantTagSource
