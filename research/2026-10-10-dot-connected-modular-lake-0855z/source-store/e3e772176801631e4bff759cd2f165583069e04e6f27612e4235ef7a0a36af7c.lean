import G5ActualRoutingSupport
import LiteralSameBinTrace

/-! Actual-source pair-relation persistence needed for the posterior use-site.
Contributor: dot / OpenAI,9 October2026. Uses existing actual merger and boundary laws. -/
namespace GProgram.G5.SourcePairPersistence
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.G6.BinHistory CloudG3.LiteralSameBinTrace
open GProgram.G5.ActualRoutingSupport
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma source_step_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample)
    (hd : d ∈ (sourceStep N r s).support) : RelationMonotone N s d := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  subst d
  cases p with
  | none => exact relation_monotone_refl N s
  | some p => exact actual_destination_relation_monotone N s p

lemma source_iteration_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : ℕ) (s d : Code N sample)
    (hd : d ∈ (sourceIteration N r k s).support) : RelationMonotone N s d := by
  induction k generalizing s with
  | zero =>
    have h : d = s := by simpa [sourceIteration] using hd
    subst d
    exact relation_monotone_refl N s
  | succ k ih =>
    obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    exact relation_monotone_trans N s m d (source_step_relation N r s m hm) (ih m hdm)

lemma source_epoch_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample)
    (hd : d ∈ (sourceTimeKernel N r t s).support) : RelationMonotone N s d := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact source_iteration_relation N r k s d hk

lemma boundary_ancestor_eq (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s d : Code N sample)
    (hd : d ∈ (boundaryKernel N op s).support) : (state d).ancestor = (state s).ancestor := by
  cases op with
  | exit e =>
    have h : d = exitCode N s e := by simpa [boundaryKernel] using hd
    subst d
    rfl
  | ordinary e degree =>
    have h : d = ordinaryCode N s e := by simpa [boundaryKernel] using hd
    subst d
    rfl
  | root =>
    have h : d = rootCode N s := by simpa [boundaryKernel] using hd
    subst d
    rfl
  | common H =>
    have h : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by simpa [boundaryKernel] using hd
    subst d
    rfl
  | independent H gamma =>
    obtain ⟨coin,_,h⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
    subst d
    rfl

lemma source_program_relation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hd : d ∈ (sourceProgram N r ops s).support) : RelationMonotone N s d := by
  induction ops generalizing s with
  | nil =>
    have h : d = s := by simpa [sourceProgram] using hd
    subst d
    exact relation_monotone_refl N s
  | cons op ops ih =>
    obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    apply relation_monotone_trans N s m d _ (ih m hdm)
    cases op with
    | interval t => exact source_epoch_relation N r t s m hm
    | boundary op =>
      intro x y hxy
      rw [boundary_ancestor_eq N op s m hm]
      exact hxy

/-- Off-diagonal pair tags after three monotone phases depend only on the
first two cut partitions once the final pair is joined. The supplied old
book disappears by the actual first-birth update rule. -/
theorem three_phase_pair_tag (N : RootedBinary V E X) {sample : Copy → X}
    (s d e f : Code N sample) (M : Copy → Copy → Fin 3) (x y : Copy)
    (hstart : (state s).ancestor x ≠ (state s).ancestor y)
    (hde : RelationMonotone N d e)
    (hfinal : (state f).ancestor x = (state f).ancestor y) :
    tagUpdate N e f (2 : Fin 3)
      (tagUpdate N d e (1 : Fin 3) (tagUpdate N s d (0 : Fin 3) M)) x y =
      if (state d).ancestor x = (state d).ancestor y then 0
      else if (state e).ancestor x = (state e).ancestor y then 1 else 2 := by
  have hp := hde x y
  by_cases hd : (state d).ancestor x = (state d).ancestor y <;>
    by_cases he : (state e).ancestor x = (state e).ancestor y <;>
    simp_all [tagUpdate]

#print axioms three_phase_pair_tag
#print axioms source_program_relation
#print axioms boundary_ancestor_eq
end GProgram.G5.SourcePairPersistence
