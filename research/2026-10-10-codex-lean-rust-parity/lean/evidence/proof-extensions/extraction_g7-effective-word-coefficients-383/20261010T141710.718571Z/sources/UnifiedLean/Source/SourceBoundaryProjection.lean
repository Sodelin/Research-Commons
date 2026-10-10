import UnifiedLean.Source.SourceBoundaryKernels

/-!
# Whole-law finite original boundary projection

Contributor: dot, 2026-10-02. Each actual original boundary kernel factors
through the same intrinsic pruned genealogy/population/register view. The
representative-independent row is derived from actual deterministic source
transport and current-owner Bernoulli measure transport, not stipulated. This
connects original node operations to the finite-state epoch projectivity gate.
-/
namespace UnifiedLean.Source.SourceBoundaryProjection
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

lemma pmf_map_injective {A B : Type*} (f : A → B) (hf : Function.Injective f)
    {p q : PMF A} (h : p.map f = q.map f) : p = q := by
  apply PMF.ext
  intro a
  have ha := congrArg (fun z : PMF B => z (f a)) h
  simpa only [PMF.map_apply,hf.eq_iff,tsum_ite_eq'] using ha

/-- Whole original boundary PMF output depends only on the actual selected
internal view, including the original register needed by COMMON operations. -/
theorem boundary_kernel_view_eq_of_same_view (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N)
    (s t : Code N sample) (h : selectedView (state s) keep = selectedView (state t) keep) :
    (boundaryKernel N op s).map (fun d => selectedView (state d) keep) =
      (boundaryKernel N op t).map (fun d => selectedView (state d) keep) := by
  cases op with
  | exit e => simp only [boundaryKernel,PMF.pure_map,exitCode_view,h]
  | ordinary e degree => simp only [boundaryKernel,PMF.pure_map,ordinaryCode_view,h]
  | root => simp only [boundaryKernel,PMF.pure_map,rootCode_view,h]
  | common H => rw [common_boundary_kernel_view,common_boundary_kernel_view,h]
  | independent H gamma =>
      apply PMF.toMeasure_injective
      change ((independentPulseKernel H gamma s).map _).toMeasure =
        ((independentPulseKernel H gamma t).map _).toMeasure
      rw [independent_pulse_kernel_view_measure,independent_pulse_kernel_view_measure,h]

noncomputable def projectedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s : Code N sample) :
    PMF (SelectedIndex N sample keep) :=
  (boundaryKernel N op s).map (projection N keep)

/-- Exact row independence of hidden original representatives, derived from
all actual boundary source laws. -/
theorem projected_boundary_eq_of_same_view (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N)
    (s t : Code N sample) (h : selectedView (state s) keep = selectedView (state t) keep) :
    projectedBoundary N keep op s = projectedBoundary N keep op t := by
  apply pmf_map_injective Subtype.val Subtype.val_injective
  simp only [projectedBoundary,PMF.map_comp]
  exact boundary_kernel_view_eq_of_same_view N keep op s t h

noncomputable def selectedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (v : SelectedIndex N sample keep) :
    PMF (SelectedIndex N sample keep) :=
  projectedBoundary N keep op (representative N keep v)

/-- Actual original-node kernel projects to a genuine normalized selected row. -/
theorem actual_boundary_projection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s : Code N sample) :
    projectedBoundary N keep op s = selectedBoundary N keep op (projection N keep s) := by
  apply projected_boundary_eq_of_same_view
  exact (representative_view N keep (projection N keep s)).symm

#print axioms boundary_kernel_view_eq_of_same_view
#print axioms projected_boundary_eq_of_same_view
#print axioms actual_boundary_projection
end UnifiedLean.Source.SourceBoundaryProjection
