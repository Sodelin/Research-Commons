import UnifiedLean.Source.SourceInitializedCalendar

/-!
UNCHECKED physical upper-boundary absence ingredient, actual SAME graph.
CLOUD-PRIVATE-SUPPORT-SOL-2330Z, 7 October 2026. No register-erasure premise.
AfterNodes comes from the actual complete exit-before-node boundary batch;
the initialized native-prefix derivation is a separate draft. Outside165.
-/
namespace UnifiedLean.G6.PrivateCalendarBoundarySupport
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

theorem after_nodes_no_private_node (N : RootedBinary V E X)
    (C : Calendar N.graph) (guard : ℝ) (P : Finset V) (s : State V E Copy)
    (hs : AfterNodes N C guard s) (hP : ∀ v ∈ P, C.age v ≤ guard) :
    ∀ x : Copy, ∀ v ∈ P, copyLocation s x ≠ .node v := by
  intro x v hv hp
  exact not_lt_of_ge (hP v hv) (hs.2 x v hp)

theorem after_nodes_no_private_edge (N : RootedBinary V E X)
    (C : Calendar N.graph) (guard : ℝ) (Q : Finset E) (s : State V E Copy)
    (hs : AfterNodes N C guard s)
    (hQ : ∀ e ∈ Q, C.age (N.graph.source e) ≤ guard) :
    ∀ x : Copy, ∀ e ∈ Q, copyLocation s x ≠ .edge e := by
  intro x e he hp
  exact not_lt_of_ge (hQ e he) (hs.1.2 x e hp)

theorem after_nodes_no_private_root (N : RootedBinary V E X)
    (C : Calendar N.graph) (guard : ℝ) (P : Finset V) (s : State V E Copy)
    (hs : AfterNodes N C guard s) (hroot : N.root ∉ P) :
    ∀ x : Copy, ∀ v ∈ P, copyLocation s x ≠ .rootPopulation v := by
  intro x v hv hp
  have hready := hs.1.1 x
  rw [hp] at hready
  change v = N.root ∧ C.age N.root ≤ guard at hready
  exact hroot (hready.1 ▸ hv)

/-- Complete actual batch support, including all source-age ties and both
inheritance modes. BoundaryReady is only this local consumer's temporal input;
the natural initialized-prefix result must derive its initial admission. -/
theorem actual_boundary_batch_private_absence (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (guard : ℝ) (P : Finset V) (Q : Finset E)
    (hP : ∀ v ∈ P, C.age v ≤ guard)
    (hQ : ∀ e ∈ Q, C.age (N.graph.source e) ≤ guard) (hroot : N.root ∉ P)
    (s : Code N sample) (hs : BoundaryReady N C guard (state s))
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (boundaryOperations N C H gamma common guard) s).support) :
    AfterNodes N C guard (state d) ∧
      (∀ x : Copy, ∀ v ∈ P, copyLocation (state d) x ≠ .node v) ∧
      (∀ x : Copy, ∀ e ∈ Q, copyLocation (state d) x ≠ .edge e) ∧
      (∀ x : Copy, ∀ v ∈ P, copyLocation (state d) x ≠ .rootPopulation v) := by
  have hafter := actual_original_boundary_batch_support N C H gamma common
    r guard s hs hd
  exact ⟨hafter, after_nodes_no_private_node N C guard P (state d) hafter hP,
    after_nodes_no_private_edge N C guard Q (state d) hafter hQ,
    after_nodes_no_private_root N C guard P (state d) hafter hroot⟩

#print axioms after_nodes_no_private_node
#print axioms after_nodes_no_private_edge
#print axioms after_nodes_no_private_root
#print axioms actual_boundary_batch_private_absence

end UnifiedLean.G6.PrivateCalendarBoundarySupport
