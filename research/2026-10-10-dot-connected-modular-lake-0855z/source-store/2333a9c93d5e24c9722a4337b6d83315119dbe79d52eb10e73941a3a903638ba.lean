import G7OriginalBoundaryPolynomial

/-! Polynomial transition tables on the inherited finite full-forest interface.
Rows use the existing source representative only after source projectivity has
proved representative independence. One table precedes all physical parameters. -/
namespace GProgram.G7.SelectedKernelPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection UnifiedLean.Source.SourceCalendarCompiler
open GProgram.G7.FullEpochPolynomial GProgram.G7.OriginalBoundaryPolynomial
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma projection_representative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (a : SelectedIndex N sample keep) :
    projection N keep (representative N keep a) = a :=
  Subtype.ext (representative_view N keep a)

noncomputable def epochTable (N : RootedBinary V E X) {sample : Copy → X}
    (a b : SelectedIndex N sample Finset.univ) : MvPolynomial (Option E) ℚ :=
  (Classical.choose (actual_full_epoch_polynomial N (representative N Finset.univ a))) b

theorem actual_selected_epoch_table (N : RootedBinary V E X) {sample : Copy → X}
    (a b : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (t : ℝ≥0) :
    evaluate r t (epochTable N a b) = (selectedTimeKernel N r Finset.univ t a b).toReal := by
  have h := Classical.choose_spec (actual_full_epoch_polynomial N (representative N Finset.univ a)) r t b
  dsimp only at h
  rw [constructed_source_time_kernel_projection,projection_representative] at h
  exact h

noncomputable def nodeTable (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (a b : SelectedIndex N sample Finset.univ) : MvPolynomial (Hybrid N) ℚ :=
  nodePolynomial N H common v (representative N Finset.univ a) b

theorem actual_selected_node_table (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (a b : SelectedIndex N sample Finset.univ) (gamma : Hybrid N → unitInterval) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (fun h => (gamma h:ℝ)) (nodeTable N H common v a b) =
      (selectedBoundary N Finset.univ (originalNodeOperation N H gamma common v) a b).toReal :=
  actual_original_node_polynomial N H common v (representative N Finset.univ a) b gamma

noncomputable def exitTable (N : RootedBinary V E X) {sample : Copy → X} {I : Type*}
    (e : E) (a b : SelectedIndex N sample Finset.univ) : MvPolynomial I ℚ :=
  constantPolynomial (projection N Finset.univ) (exitCode N (representative N Finset.univ a) e) b

theorem actual_selected_exit_table (N : RootedBinary V E X) {sample : Copy → X} {I : Type*}
    (x : I → ℝ) (e : E) (a b : SelectedIndex N sample Finset.univ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) x (exitTable N e a b) =
      (selectedBoundary N Finset.univ (.exit e) a b).toReal :=
  constantPolynomial_eval x _ _ _

end GProgram.G7.SelectedKernelPolynomial
