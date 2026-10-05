import G1OriginalCalendarDecomposition
import G1InterleavedEpochCompression

/-! Actual original-calendar epoch silence for fixed component edge panels.
Contributor: dot, 2026-10-03. A panel may occupy BOTH original parallel arms;
all their older endpoints have the same original epoch end. Earlier original
exits and all original node operations are proved physically silent on that
complete panel, while the actual exterior program remains processed. -/
namespace G1OriginalEpochPanelSilence
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations UnifiedLean.Source.SourcePoissonKernel
open G1InitializedFrontierPrefix G1OriginalCalendarDecomposition G1ActualJointProgram
open G1ExteriorBoundarySilence G1InterleavedEpochCompression G1NonrootBigonKernel
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

def AtEdgePanel (s : State V E Copy) (keep : Finset Copy) (edges : Finset E) : Prop :=
  ∀ x ∈ keep, ∃ e ∈ edges, copyLocation s x = .edge e

lemma actual_time_edge_panel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (keep : Finset Copy) (edges : Finset E)
    (hs : AtEdgePanel (state s) keep edges) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : AtEdgePanel (state d) keep edges := by
  intro x hx
  obtain ⟨e,he,hpop⟩ := hs x hx
  exact ⟨e,he,(actual_time_copy_population N r t s hd x).trans hpop⟩

lemma actual_node_at_edge_absent (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (s : Code N sample) (keep : Finset Copy) (edges : Finset E)
    (hs : AtEdgePanel (state s) keep edges) :
    PanelAbsent N (originalNodeOperation N H gamma common v) (state s) keep := by
  intro x hx
  obtain ⟨e,_,hpop⟩ := hs x hx
  rw [hpop]
  unfold originalNodeOperation
  split_ifs <;> simp [touchedPlace]

lemma actual_node_preserves_edge_panel (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (s : Code N sample) (keep : Finset Copy) (edges : Finset E)
    (hs : AtEdgePanel (state s) keep edges) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    AtEdgePanel (state d) keep edges := by
  intro x hx
  obtain ⟨e,he,hpop⟩ := hs x hx
  have hm := actual_original_node_kernel_movement N H gamma common v s hd x
  unfold NodeMovement at hm
  have hn : copyLocation (state s) x ≠ .node v := by rw [hpop]; simp
  rw [if_neg hn] at hm
  exact ⟨e,he,hm.trans hpop⟩

lemma actual_other_exit_at_edge_absent (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (edges : Finset E) (f : E) (hf : f ∉ edges)
    (hs : AtEdgePanel (state s) keep edges) : PanelAbsent N (.exit f) (state s) keep := by
  intro x hx hpop
  obtain ⟨e,he,hepop⟩ := hs x hx
  have hef : e = f := Location.edge.inj (hepop.symm.trans hpop)
  exact hf (hef ▸ he)

lemma actual_other_exit_preserves_edge_panel (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (edges : Finset E) (f : E) (hf : f ∉ edges)
    (hs : AtEdgePanel (state s) keep edges) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (.exit f) s).support) : AtEdgePanel (state d) keep edges := by
  have hd' : d = exitCode N s f := by simpa [boundaryKernel] using hd
  subst d
  intro x hx
  obtain ⟨e,he,hpop⟩ := hs x hx
  refine ⟨e,he,?_⟩
  rw [exitCode_copyLocation]
  unfold exitLocation
  have hnot : copyLocation (state s) x ≠ .edge f := by
    simpa only [touchedPlace] using (actual_other_exit_at_edge_absent N s keep edges f hf hs x hx)
  rw [if_neg hnot]
  exact hpop

end G1OriginalEpochPanelSilence
