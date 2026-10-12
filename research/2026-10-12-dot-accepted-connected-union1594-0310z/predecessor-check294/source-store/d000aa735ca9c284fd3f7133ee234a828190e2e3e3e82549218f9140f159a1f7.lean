import G1ExtractedComponentProgram
import G1BigonFootprint
import G1BigonSpliceGraph
import G1JointSeparatedSourceGeometry

/-! Original descendant-interface closure for the extracted actual component.
Contributor: dot, 2026-10-03. These graph facts discharge part of physical
separator admission; they assume no calendar/frontier or stochastic law. -/
namespace G1ComponentDescendantClosure
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint
open G1BigonSpliceGraph G1ExtractedComponentProgram GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep G1JointSeparatedSourceGeometry
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

lemma actual_hybrid_descendant_closure (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (x : X) :
    N.graph.DReach A.fragment.parents.hybrid (N.leaf x) ↔
      N.graph.DReach (N.graph.target A.child) (N.leaf x) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨v,⟨e,hs,ht⟩,hrest⟩
    · exact False.elim ((actual_taxon_vertices_retained N b A x).2 heq.symm)
    · have he := actual_child_unique N b A e hs
      subst e
      rw [ht]
      exact hrest
  · intro h
    exact (Relation.ReflTransGen.single ⟨A.child,A.child_source,rfl⟩).trans h

lemma actual_upper_descendant_closure (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (x : X) :
    N.graph.DReach A.fragment.upper (N.leaf x) ↔
      N.graph.DReach (N.graph.target A.child) (N.leaf x) := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with heq | ⟨v,⟨e,hs,ht⟩,hrest⟩
    · exact False.elim ((actual_taxon_vertices_retained N b A x).1 heq.symm)
    · have he := actual_upper_children_exhaustive N hc b A e hs
      have hev : v = A.fragment.parents.hybrid := by
        rcases he with rfl | rfl
        · exact ht.symm.trans A.fragment.parents.target0
        · exact ht.symm.trans A.fragment.parents.target1
      rw [hev] at hrest
      exact (actual_hybrid_descendant_closure N b A x).mp hrest
  · intro h
    exact (Relation.ReflTransGen.single
      ⟨A.fragment.parents.parent0,A.fragment.arm_sources false,A.fragment.parents.target0⟩).trans
        ((actual_hybrid_descendant_closure N b A x).mpr h)

/-- The actual component's physical populations, including both original
interface-node endpoints before entry/after exit where appropriate. The
rootward endpoint is excluded: exterior interaction can resume there. -/
def ComponentLocation (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : Location V E → Prop
  | .node v => v = N.graph.target A.child ∨ v = A.fragment.parents.hybrid ∨ v = A.fragment.upper
  | .edge e => e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 ∨ e = A.entry
  | .rootPopulation _ => False

lemma actual_component_location_descends (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (p : Location V E) (x : X)
    (hp : ComponentLocation N b A p) (hd : DescendsTo N p x) :
    N.graph.DReach (N.graph.target A.child) (N.leaf x) := by
  cases p with
  | rootPopulation v => exact False.elim hp
  | node v =>
      rcases hp with rfl | rfl | rfl
      · exact hd
      · exact (actual_hybrid_descendant_closure N b A x).mp hd
      · exact (actual_upper_descendant_closure N hc b A x).mp hd
  | edge e =>
      rcases hp with rfl | rfl | rfl | rfl
      · exact hd
      · change N.graph.DReach (N.graph.target A.fragment.parents.parent0) (N.leaf x) at hd
        rw [A.fragment.parents.target0] at hd
        exact (actual_hybrid_descendant_closure N b A x).mp hd
      · change N.graph.DReach (N.graph.target A.fragment.parents.parent1) (N.leaf x) at hd
        rw [A.fragment.parents.target1] at hd
        exact (actual_hybrid_descendant_closure N b A x).mp hd
      · change N.graph.DReach (N.graph.target A.entry) (N.leaf x) at hd
        rw [A.entry_target] at hd
        exact (actual_upper_descendant_closure N hc b A x).mp hd

/-- The actual source's spatial admission already prohibits every exterior
sample from occupying ANY original component population. No calendar-ready
state is silently inferred from SourceValid. -/
theorem actual_exterior_cannot_occupy_component {Copy : Type*}
    [Fintype Copy] [DecidableEq Copy] (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {sample : Copy → X}
    (s : Code N sample) (x : Copy)
    (hx : ¬ N.graph.DReach (N.graph.target A.child) (N.leaf (sample x))) :
    ¬ ComponentLocation N b A (copyLocation (state s) x) := by
  intro hp
  exact hx (actual_component_location_descends N hc b A _ _ hp (s.property.original_descendant x))

/-- Graph-side physical separator for the actual joint-source theorem.
Only internal LOCATION support still needs natural-calendar induction. -/
theorem actual_component_population_separator {Copy : Type*}
    [Fintype Copy] [DecidableEq Copy] (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) {sample : Copy → X}
    (s : Code N sample) (inside outside : Finset Copy)
    (hi : ∀ x ∈ inside, ComponentLocation N b A (copyLocation (state s) x))
    (ho : ∀ y ∈ outside, ¬ N.graph.DReach (N.graph.target A.child) (N.leaf (sample y))) :
    PopulationSeparated (state s) inside outside := by
  intro x hx y hy heq
  exact actual_exterior_cannot_occupy_component N hc b A s y (ho y hy) (heq ▸ hi x hx)

end G1ComponentDescendantClosure
