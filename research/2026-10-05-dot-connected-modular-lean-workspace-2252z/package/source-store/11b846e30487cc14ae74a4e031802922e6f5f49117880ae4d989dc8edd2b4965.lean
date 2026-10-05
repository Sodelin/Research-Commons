import G1ActualTwoPortBlob
import G1FiniteTwoPortChain

/-!
# Actual extracted two-port component with both original cut populations

Contributor: dot, 2026-10-03. The actual original component program includes
the hybrid-child cut population, the extracted parallel-arm bigon, and the
original entering cut population, each at its original positive calendar
duration/rate. The rootward endpoint is retained even when it is the original
root. Both internal vertices are proved outside the entire actual root blob.
The current-entering-root/graft/register/history law is derived from actual
source PMFs, with no literal component shape or desired output law assumed.
Whole graph splice and full larger-source exterior factorization are next.
-/
namespace G1ExtractedComponentProgram
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1CutChildPorts G1BlobDegreeBalance G1ActualTwoPortBlob
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open G1NonrootBigonKernel G1FiniteTwoPortChain
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

noncomputable def edgeDuration (N : RootedBinary V E X) (C : Calendar N.graph) (e : E) : ℝ≥0 :=
  Real.toNNReal (C.age (N.graph.source e) - C.age (N.graph.target e))

theorem actual_edge_duration_positive (N : RootedBinary V E X) (C : Calendar N.graph) (e : E) :
    0 < edgeDuration N C e := Real.toNNReal_pos.mpr (sub_pos.mpr (C.edge_older e))

noncomputable def edgeProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (e : E) (degree : N.graph.inDegree (N.graph.target e) = 1) : List (ProgramStep N) :=
  [.boundary (.ordinary e degree),.interval (edgeDuration N C e),.boundary (.exit e)]

lemma actual_original_edge_program (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) (s : Code N sample) :
    sourceProgram N r (edgeProgram N C e degree) s =
      (sourceTimeKernel N r (edgeDuration N C e) (ordinaryCode N s e)).map
        (fun d => exitCode N d e) := by
  simp only [edgeProgram,sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind]
  rfl

theorem actual_original_edge_exit_population (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (e : E)
    (degree : N.graph.inDegree (N.graph.target e) = 1) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node (N.graph.target e))
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (edgeProgram N C e degree) s).support) :
    ∀ l ∈ (state d).live, (state d).location l = .node (N.graph.source e) := by
  rw [actual_original_edge_program] at hd
  obtain ⟨z,hz,hzd⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  intro l hl
  have hsrc : copyLocation (state s) l = .node (N.graph.target e) :=
    hinput _ (s.property.forest.ancestor_live l)
  have hbefore : copyLocation (state (ordinaryCode N s e)) l = .edge e := by
    rw [actual_ordinary_copy_population,hsrc,if_pos rfl]
  have hduring := actual_time_copy_population N r (edgeDuration N C e) (ordinaryCode N s e) hz l
  have hout : copyLocation (state d) l = .node (N.graph.source e) := by
    rw [← hzd,actual_exit_copy_population,hduring,hbefore,if_pos rfl]
  have hrep : (state d).ancestor l = l := d.property.forest.representative l hl
  simpa only [copyLocation,hrep] using hout

theorem extracted_child_ordinary (N : RootedBinary V E X) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : N.graph.inDegree (N.graph.target A.child) = 1 := by
  apply N.indegree_one_of_nonroot_nonhybrid (N.edge_target_ne_root A.child)
  intro hh
  exact actual_hybrid_parent_nonbridge N A.child hh A.child_bridge

theorem extracted_entry_ordinary (N : RootedBinary V E X) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) : N.graph.inDegree (N.graph.target A.entry) = 1 := by
  rw [A.entry_target]
  apply N.indegree_one_of_nonroot_nonhybrid A.fragment.upper_nonroot
  intro hh
  have hparent : N.graph.IsBridge A.fragment.parents.parent0 := by
    apply hc
    rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from A.fragment.arm_sources false]
    exact hh
  exact actual_hybrid_parent_nonbridge N A.fragment.parents.parent0
    (A.fragment.parents.target0 ▸ A.fragment.parents.isHybrid) hparent

/-- Both incident original edge populations are included exactly once, with
their original calendars/rates. The output may be the retained original root;
the root's own population entry and root-containing blob remain exterior. -/
noncomputable def componentProgram (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (gamma : unitInterval) (common : Bool) : List (ProgramStep N) :=
  edgeProgram N C A.child (extracted_child_ordinary N b A) ++
    (bigonProgram N C A.fragment gamma common ++
    edgeProgram N C A.entry (extracted_entry_ordinary N hc b A))

/-- Every actual component realization exits at its unchanged ORIGINAL
rootward cut endpoint. No exit-population identity is supplied as an input. -/
theorem actual_extracted_component_exit_population (N : RootedBinary V E X) {sample : Copy → X}
    (hc : CutChild N) (C : Calendar N.graph) (r : PositivePairRates E) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node (N.graph.target A.child))
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (componentProgram N hc C b A gamma common) s).support) :
    ∀ l ∈ (state d).live, (state d).location l = .node (N.graph.source A.entry) := by
  rw [componentProgram,sourceProgram_append] at hd
  obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hchild := actual_original_edge_exit_population N C r A.child (extracted_child_ordinary N b A) s hinput hz
  rw [A.child_source] at hchild
  rw [sourceProgram_append] at hdz
  obtain ⟨w,hw,hdw⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdz
  have hbigon := actual_nonroot_bigon_exit_population N C r A.fragment gamma common z hchild hw
  have hentry : ∀ l ∈ (state w).live, (state w).location l = .node (N.graph.target A.entry) := by
    rw [A.entry_target]
    exact hbigon
  exact actual_original_edge_exit_population N C r A.entry (extracted_entry_ordinary N hc b A) w hentry hdw

/-- Entire actual root-blob vertex set is disjoint from the two extracted
vertices. This is stronger than merely saying the upper vertex is not root. -/
theorem actual_extracted_internal_vertices_exclude_root_blob (N : RootedBinary V E X)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b) :
    ∀ v, (v = A.fragment.upper ∨ v = A.fragment.parents.hybrid) →
      N.graph.blobOf v ≠ N.graph.blobOf N.root := by
  intro v hv
  have hvb := (A.vertices_exact v).mpr hv
  rw [hvb]
  exact hb

noncomputable def extractedComponentKernel (N : RootedBinary V E X) {sample : Copy → X}
    (hc : CutChild N) (C : Calendar N.graph) (r : PositivePairRates E) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node (N.graph.target A.child)) :=
  smallerCurrentRootKernel N r (componentProgram N hc C b A gamma common)
    s (.node (N.graph.target A.child)) hinput

/-- Local source gate instantiated by DERIVED canonical actual blob data,
with both positive original cut intervals, all prior subtrees, current-root
cap, shared register and retained exterior/root history. Full graph splice and
actual arbitrary larger-source exterior factorization remain separate gates. -/
theorem actual_extracted_cap_m_component_replacement
    (N : RootedBinary V E X) {sample : Copy → X} {History Obs : Type*}
    (hc : CutChild N) (C : Calendar N.graph) (r : PositivePairRates E) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (hp : Fintype.card (N.BlobPort b) = 2)
    (gamma : unitInterval) (common : Bool)
    (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node
      (N.graph.target (extractedBigon N hc b hb ((actual_quotient_port_card N b).symm.trans hp)).child))
    (m : Nat) (cap : (state s).live.card ≤ m) (history : History)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    let A := extractedBigon N hc b hb ((actual_quotient_port_card N b).symm.trans hp)
    Fintype.card (SelectedCopy (state s).live) ≤ m ∧
    (∀ v, (v = A.fragment.upper ∨ v = A.fragment.parents.hybrid) →
      N.graph.blobOf v ≠ N.graph.blobOf N.root) ∧
    (∀ d ∈ (sourceProgram N r (componentProgram N hc C b A gamma common) s).support,
      ∀ l ∈ (state d).live, (state d).location l = .node (N.graph.source A.entry)) ∧
    ((sourceProgram N r (componentProgram N hc C b A gamma common) s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
      (extractedComponentKernel N hc C r b A gamma common s hinput).bind
        (fun F => exterior (history,(state s).register,
          F.image (graftUnranked (fun l => (state s).genealogy l.val))))) := by
  dsimp only
  refine ⟨actual_kernel_carrier_cap N s m cap,
    actual_extracted_internal_vertices_exclude_root_blob N b hb _,?_,?_⟩
  · intro d hd
    exact actual_extracted_component_exit_population N hc C r b _ gamma common s hinput hd
  · exact actual_original_contextual_forest_replacement N r
      (componentProgram N hc C b _ gamma common) s (.node (N.graph.target _)) hinput history exterior

end G1ExtractedComponentProgram
