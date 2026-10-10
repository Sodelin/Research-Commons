import G7EffectiveInitializationCoefficients
import G7SelectedKernelPolynomial
import GraphSwitching
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Order.Interval.Set.Infinite

/-!
# Concrete original-node rows and inherited selected boundary tables

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The finite incoming-edge resolver is used only at actual indegree-one nodes.
Existing source boundary projection supplies representative independence;
Mathlib polynomial extensionality identifies its entire rational coefficient
table on the original gamma box. No boundary law is stipulated or reproved.
Original current owners, stored COMMON bits, parent orientation, edge IDs and
full entering register are retained. Draft pending sole-scheduler audit.
-/
namespace GProgram.G7.EffectiveNodeCoefficients
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourceCalendarCompiler
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.SparseRowProducts GProgram.G7.EffectiveBoundaryCoefficients
open GProgram.G7.EffectiveInitializationCoefficients
open GProgram.G7.OriginalBoundaryPolynomial GProgram.G7.SelectedKernelPolynomial

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def incomingEdges (N : RootedBinary V E X) (v : V) : List E :=
  (FinEnum.toList E).filter (fun e => decide (N.graph.target e = v))

lemma incomingEdges_nonempty (N : RootedBinary V E X) (v : V) (hr : v ≠ N.root) :
    incomingEdges N v ≠ [] := by
  have hm : (defaultSelector N).edge ⟨v,hr⟩ ∈ incomingEdges N v := by
    apply List.mem_filter.mpr
    exact ⟨FinEnum.mem_toList _,by simp [(defaultSelector N).target]⟩
  exact List.ne_nil_of_mem hm

/-- A finite original-edge search. The proof argument is erased at execution. -/
def incomingEdgeEffective (N : RootedBinary V E X) (v : V) (hr : v ≠ N.root) : E :=
  (incomingEdges N v).head (incomingEdges_nonempty N v hr)

lemma incomingEdgeEffective_target (N : RootedBinary V E X) (v : V) (hr : v ≠ N.root) :
    N.graph.target (incomingEdgeEffective N v hr) = v := by
  have hm := List.head_mem (incomingEdges_nonempty N v hr)
  have hb := (List.mem_filter.mp hm).2
  exact of_decide_eq_true hb

/-- The inherited selector's arbitrary choice is immaterial exactly where the
original rooted-binary source proves indegree one. -/
lemma incomingEdgeEffective_eq (N : RootedBinary V E X) (v : V) (hr : v ≠ N.root)
    (hh : ¬ N.graph.IsHybrid v) :
    incomingEdgeEffective N v hr = (defaultSelector N).edge ⟨v,hr⟩ := by
  obtain ⟨e,_,hu⟩ := N.incoming_unique_of_indegree_one
    (nonhybrid_nonroot_indegree_one N v hr hh)
  exact (hu _ (incomingEdgeEffective_target N v hr)).trans
    (hu _ ((defaultSelector N).target ⟨v,hr⟩)).symm

def nodeRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (s : Code N sample) : Rows (Hybrid N) (Code N sample) :=
  letI : DecidablePred N.graph.IsHybrid := hybridDecidable N
  if hr : v = N.root then pureRows (rootCodeEffective N s)
  else if hh : N.graph.IsHybrid v then
    if common ⟨v,hh⟩ then commonRows (H.parents ⟨v,hh⟩) s
    else pulseRows ⟨v,hh⟩ (H.parents ⟨v,hh⟩) s
  else pureRows (ordinaryCodeEffective N s (incomingEdgeEffective N v hr))

theorem polynomial_nodeRows (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (nodeRows N H common v s) a) =
      nodePolynomial N H common v s a := by
  classical
  have hp : (project N Finset.univ : Code N sample → SelectedIndex N sample Finset.univ) =
      projection N Finset.univ := funext (project_eq N Finset.univ)
  by_cases hr : v = N.root
  · simp only [nodeRows,dif_pos hr,nodePolynomial,polynomial_pureRows,
      rootCodeEffective_eq,hp]
  · by_cases hh : N.graph.IsHybrid v
    · by_cases hc : common ⟨v,hh⟩ = true
      · simp only [nodeRows,dif_neg hr,dif_pos hh,if_pos hc,
          nodePolynomial,polynomial_commonRows,hp]
      · simp only [nodeRows,dif_neg hr,dif_pos hh,if_neg hc,
          nodePolynomial,polynomial_pulseRows,hp]
    · simp only [nodeRows,dif_neg hr,dif_neg hh,nodePolynomial,
        polynomial_pureRows,ordinaryCodeEffective_eq,incomingEdgeEffective_eq N v hr hh,hp]

/-- Every point of the open original-gamma box is an actual source bank.
Its polynomial identification is independent of physical epoch coordinates. -/
theorem polynomial_eq_of_gamma_evaluations (N : RootedBinary V E X)
    (p q : MvPolynomial (Hybrid N) ℚ)
    (h : ∀ gamma : Hybrid N → unitInterval,
      MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => (gamma v : ℝ)) p =
        MvPolynomial.eval₂ (Rat.castHom ℝ) (fun v => (gamma v : ℝ)) q) : p = q := by
  apply MvPolynomial.map_injective (Rat.castHom ℝ) Rat.cast_injective
  apply MvPolynomial.funext_set (fun _ => Set.Ioo (0 : ℝ) 1)
    (fun _ => Set.Ioo_infinite (show (0 : ℝ) < 1 from zero_lt_one))
  intro x hx
  have hbox : ∀ v, 0 < x v ∧ x v < 1 := fun v => hx v (Set.mem_univ v)
  let gamma : Hybrid N → unitInterval := fun v =>
    ⟨x v,le_of_lt (hbox v).1,le_of_lt (hbox v).2⟩
  have physical := h gamma
  simpa only [gamma,MvPolynomial.eval₂_eq_eval_map] using physical

/-- Bind the sparse complete literal fibre to the inherited selected table,
including its noncomputable representative, at arbitrary rational coefficients. -/
theorem polynomial_nodeRows_eq_nodeTable (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (nodeRows N H common v s) a) =
      nodeTable N H common v (project N Finset.univ s) a := by
  rw [polynomial_nodeRows]
  apply polynomial_eq_of_gamma_evaluations N
  intro gamma
  rw [actual_original_node_polynomial]
  have hp := congrArg (fun law : PMF (SelectedIndex N sample Finset.univ) => (law a).toReal)
    (actual_boundary_projection N Finset.univ (originalNodeOperation N H gamma common v) s)
  change (((boundaryKernel N (originalNodeOperation N H gamma common v) s).map
      (projection N Finset.univ)) a).toReal = _ at hp
  rw [project_eq]
  exact hp.trans (actual_selected_node_table N H common v
    (projection N Finset.univ s) a gamma).symm

def exitRows {I : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Rows I (Code N sample) :=
  pureRows (exitCodeEffective N s e)

theorem polynomial_exitRows_eq_exitTable {I : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (e : E)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (exitRows (I := I) N s e) a) =
      exitTable N e (project N Finset.univ s) a := by
  rw [exitRows,polynomial_pureRows,exitCodeEffective_eq]
  rw [show (project N Finset.univ : Code N sample → SelectedIndex N sample Finset.univ) =
      projection N Finset.univ from funext (project_eq N Finset.univ)]
  apply MvPolynomial.map_injective (Rat.castHom ℝ) Rat.cast_injective
  apply MvPolynomial.funext
  intro x
  have hp := congrArg (fun law : PMF (SelectedIndex N sample Finset.univ) => (law a).toReal)
    (actual_boundary_projection N Finset.univ (.exit e) s)
  change (((PMF.pure (exitCode N s e)).map (projection N Finset.univ)) a).toReal = _ at hp
  have h := (constantPolynomial_eval x (projection N Finset.univ) (exitCode N s e) a).trans
    (hp.trans (actual_selected_exit_table N x e (projection N Finset.univ s) a).symm)
  simpa only [MvPolynomial.eval₂_eq_eval_map] using h

#print axioms incomingEdgeEffective_eq
#print axioms polynomial_nodeRows
#print axioms polynomial_eq_of_gamma_evaluations
#print axioms polynomial_nodeRows_eq_nodeTable
#print axioms polynomial_exitRows_eq_exitTable
end GProgram.G7.EffectiveNodeCoefficients
