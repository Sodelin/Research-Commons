import G1ActualJointBoundary

/-!
# Joint actual-source laws through finite separated original agendas

Contributor: dot, 2026-10-03. The agenda hypothesis concerns only physical
population separation before original operations on actual reachable states.
It contains no desired kernel, independence or forest output equality. A final
output may meet an exterior population: separation is required before the next
operation, so arbitrary later interaction is allowed after the interface.
-/
namespace G1ActualJointProgram
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open G1JointSeparatedSourceGeometry G1ActualJointGenerator G1ActualJointEpoch G1ActualJointBoundary
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma bind_eq_of_eq_on_support {A B : Type*} (p : PMF A) (f g : A → PMF B)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  rw [PMF.bind_apply,PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : p a = 0
  · simp [ha]
  · rw [h a ha]

lemma independentProduct_bind {A B C D : Type*} (p : PMF A) (q : PMF B)
    (f : A → PMF C) (g : B → PMF D) :
    (independentProduct p q).bind (fun v => independentProduct (f v.1) (g v.2)) =
      independentProduct (p.bind f) (q.bind g) := by
  simp only [independentProduct,PMF.bind_map,PMF.bind_bind,PMF.map_bind,Function.comp_def]
  congr 1
  funext a
  exact PMF.bind_comm q (f a) (fun b c => (g b).map (fun d => (c,d)))

noncomputable def SeparatedAgenda (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) :
    List (ProgramStep N) → Code N sample → Prop
  | [], _ => True
  | op :: ops, s => PopulationSeparated (state s) inside outside ∧
      ∀ d ∈ (sourceProgramStep N r op s).support, SeparatedAgenda N r inside outside ops d

theorem actual_separated_joint_step_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (op : ProgramStep N)
    (s : Code N sample) (hsep : PopulationSeparated (state s) inside outside) :
    (sourceProgramStep N r op s).map (jointProjection N inside outside) =
      independentProduct (selectedProgramStep N r inside op (projection N inside s))
        (selectedProgramStep N r outside op (projection N outside s)) := by
  cases op with
  | interval t =>
      rw [sourceProgramStep,actual_separated_joint_epoch_law N r inside outside t s hsep,
        constructed_source_time_kernel_projection,constructed_source_time_kernel_projection]
      rfl
  | boundary b =>
      rw [sourceProgramStep,actual_separated_joint_boundary_law N inside outside b s hsep]
      change independentProduct (projectedBoundary N inside b s) (projectedBoundary N outside b s) = _
      rw [actual_boundary_projection,actual_boundary_projection]
      rfl

/-- The complete JOINT genealogy/population/SAME-register law equals the
product of the two actual selected original-source programs. The physical
separator is the only agenda-specific assumption. -/
theorem actual_separated_joint_program_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (hagenda : SeparatedAgenda N r inside outside ops s) :
    (sourceProgram N r ops s).map (jointProjection N inside outside) =
      independentProduct (selectedProgram N r inside ops (projection N inside s))
        (selectedProgram N r outside ops (projection N outside s)) := by
  induction ops generalizing s with
  | nil => simp [sourceProgram,selectedProgram,PMF.pure_map,jointProjection,independentProduct_pure]
  | cons op ops ih =>
      obtain ⟨hsep,htail⟩ := hagenda
      rw [sourceProgram,PMF.map_bind]
      calc
        _ = (sourceProgramStep N r op s).bind (fun d =>
            independentProduct (selectedProgram N r inside ops (projection N inside d))
              (selectedProgram N r outside ops (projection N outside d))) :=
          bind_eq_of_eq_on_support _ _ _ (fun d hd => ih d (htail d hd))
        _ = ((sourceProgramStep N r op s).map (jointProjection N inside outside)).bind
            (fun v => independentProduct (selectedProgram N r inside ops v.1)
              (selectedProgram N r outside ops v.2)) := by
          rw [PMF.bind_map]
          rfl
        _ = (independentProduct (selectedProgramStep N r inside op (projection N inside s))
            (selectedProgramStep N r outside op (projection N outside s))).bind
              (fun v => independentProduct (selectedProgram N r inside ops v.1)
                (selectedProgram N r outside ops v.2)) := by
          rw [actual_separated_joint_step_law N r inside outside op s hsep]
        _ = _ := by
          rw [independentProduct_bind]
          rfl

#print axioms actual_separated_joint_program_law
end G1ActualJointProgram
