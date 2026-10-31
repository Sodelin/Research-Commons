import G1OriginalRegistryBigon
import G1ActualJointProgram

/-! Derive the actual component/exterior separator through original agendas.
Contributor: dot, 2026-10-03. All original node operations retain inside
locations in the graph-derived component. All original exits except the
rootward closing entry exit also retain them. The closing exit is LAST in
the isolated phase; later original exterior interaction remains unrestricted. -/
namespace G1ActualComponentAgenda
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceProgramTransport
open G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1ExtractedComponentProgram
open G1ComponentDescendantClosure G1ActualJointProgram G1JointSeparatedSourceGeometry G1NonrootBigonKernel
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

lemma actual_component_node_movement_closed (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (v : V) {old new : Location V E}
    (hp : ComponentLocation N b A old) (hm : NodeMovement N v old new) :
    ComponentLocation N b A new := by
  unfold NodeMovement at hm
  by_cases hn : old = .node v
  · rw [if_pos hn] at hm
    rw [hn] at hp
    change v = N.graph.target A.child ∨ v = A.fragment.parents.hybrid ∨ v = A.fragment.upper at hp
    have hvr : v ≠ N.root := by
      rcases hp with rfl | rfl | rfl
      · exact N.edge_target_ne_root A.child
      · intro h
        have hd := A.fragment.parents.isHybrid.1
        rw [h,N.root_degrees.1] at hd
        cases hd
      · exact A.fragment.upper_nonroot
    rw [if_neg hvr] at hm
    obtain ⟨e,he,hnew⟩ := hm
    rw [hnew]
    change e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 ∨ e = A.entry
    rcases hp with hv | hv | hv
    · have ht : N.graph.target e = N.graph.target A.child := he.trans hv
      obtain ⟨f,hf,hu⟩ := N.incoming_unique_of_indegree_one (extracted_child_ordinary N b A)
      exact Or.inl ((hu e ht).trans (hu A.child rfl).symm)
    · exact Or.inr ((actual_hybrid_parents_exhaustive N b A e (he.trans hv)).imp id Or.inl)
    · exact Or.inr (Or.inr (Or.inr (actual_entry_unique N hc b A e (he.trans hv))))
  · rw [if_neg hn] at hm
    exact hm ▸ hp

lemma actual_component_exit_closed (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (e : E) (hne : e ≠ A.entry) {old : Location V E}
    (hp : ComponentLocation N b A old) : ComponentLocation N b A (exitLocation N e old) := by
  unfold exitLocation
  by_cases ho : old = .edge e
  · rw [if_pos ho]
    rw [ho] at hp
    change e = A.child ∨ e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 ∨ e = A.entry at hp
    change N.graph.source e = N.graph.target A.child ∨ N.graph.source e = A.fragment.parents.hybrid ∨
      N.graph.source e = A.fragment.upper
    rcases hp with rfl | rfl | rfl | h
    · exact Or.inr (Or.inl A.child_source)
    · exact Or.inr (Or.inr (A.fragment.arm_sources false))
    · exact Or.inr (Or.inr (A.fragment.arm_sources true))
    · exact False.elim (hne h)
  · rw [if_neg ho]; exact hp

/-- A purely syntactic ORIGINAL-operation scope. It contains no source law,
inside/output kernel, location equality, desired rank/scalar or cap field. -/
def SafeOriginalStep (N : RootedBinary V E X) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (op : ProgramStep N) : Prop :=
  (∃ t : ℝ≥0, op = .interval t) ∨ (∃ e : E, e ≠ A.entry ∧ op = .boundary (.exit e)) ∨
    (∃ v : V, op = .boundary (originalNodeOperation N H gamma common v))

lemma actual_component_safe_step_support (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (hsafe : SafeOriginalStep N b A H gamma common op)
    (s : Code N sample) (inside : Finset Copy)
    (hin : ∀ x ∈ inside, ComponentLocation N b A (copyLocation (state s) x))
    {d : Code N sample} (hd : d ∈ (sourceProgramStep N r op s).support) :
    ∀ x ∈ inside, ComponentLocation N b A (copyLocation (state d) x) := by
  rcases hsafe with ⟨t,rfl⟩ | ⟨e,hne,rfl⟩ | ⟨v,rfl⟩
  · intro x hx
    change d ∈ (sourceTimeKernel N r t s).support at hd
    rw [actual_time_copy_population N r t s hd x]
    exact hin x hx
  · have heq : d = exitCode N s e := by simpa [sourceProgramStep,boundaryKernel] using hd
    subst d
    intro x hx
    rw [exitCode_copyLocation]
    exact actual_component_exit_closed N b A e hne (hin x hx)
  · intro x hx
    exact actual_component_node_movement_closed N hc b A v (hin x hx)
      (actual_original_node_kernel_movement N H gamma common v s hd x)

/-- The complete separated agenda is DERIVED from graph component closure and
actual ORIGINAL operation syntax. After the final entry exit, separation need
not hold and the SAME original exterior/root process may interact again. -/
theorem actual_original_component_separated_agenda (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N))
    (hsafe : ∀ op ∈ ops, SafeOriginalStep N b A H gamma common op)
    (s : Code N sample) (inside outside : Finset Copy)
    (hin : ∀ x ∈ inside, ComponentLocation N b A (copyLocation (state s) x))
    (hout : ∀ y ∈ outside, ¬ N.graph.DReach (N.graph.target A.child) (N.leaf (sample y))) :
    SeparatedAgenda N r inside outside (ops ++ [.boundary (.exit A.entry)]) s := by
  induction ops generalizing s with
  | nil =>
      exact ⟨actual_component_population_separator N hc b A s inside outside hin hout,by simp [SeparatedAgenda]⟩
  | cons op ops ih =>
      refine ⟨actual_component_population_separator N hc b A s inside outside hin hout,?_⟩
      intro d hd
      exact ih (fun p hp => hsafe p (List.mem_cons_of_mem op hp)) d
        (actual_component_safe_step_support N hc b A H gamma common r op (hsafe op (by simp)) s inside hin hd)

end G1ActualComponentAgenda
