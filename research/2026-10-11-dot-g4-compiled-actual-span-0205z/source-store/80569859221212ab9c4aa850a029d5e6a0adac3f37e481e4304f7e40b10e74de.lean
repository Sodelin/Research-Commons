import G1NonrootBigonKernel

/-!
# Arbitrary finite original two-port words with opaque forests

Contributor: dot, 2026-10-03. Original nonroot parallel bigons and ordinary
positive-calendar connectors are composed with exact endpoint matching.
One original site-parameter/mode assignment is reused across the whole word.
The current-root kernel/context law and single original output population are
derived for every finite word and every already-formed input subtree forest.
This is source-word admission, not the canonical whole-graph blob/core map.
-/
namespace G1FiniteTwoPortChain
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open G1NonrootBigonKernel
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
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual original indegree-one population connector, with no root-blob
operation folded into the word. These are graph data, not stochastic premises. -/
structure NonrootConnector (N : RootedBinary V E X) where
  edge : E
  ordinary : N.graph.inDegree (N.graph.target edge) = 1
  source_nonroot : N.graph.source edge ≠ N.root
  target_nonroot : N.graph.target edge ≠ N.root

inductive SourcePiece (N : RootedBinary V E X)
  | bigon (original : NonrootBigon N)
  | connector (original : NonrootConnector N)

def SourcePiece.inputNode {N : RootedBinary V E X} : SourcePiece N → V
  | .bigon B => B.parents.hybrid
  | .connector e => N.graph.target e.edge

def SourcePiece.outputNode {N : RootedBinary V E X} : SourcePiece N → V
  | .bigon B => B.upper
  | .connector e => N.graph.source e.edge

noncomputable def connectorDuration (N : RootedBinary V E X) (C : Calendar N.graph)
    (e : NonrootConnector N) : ℝ≥0 :=
  Real.toNNReal (C.age (N.graph.source e.edge) - C.age (N.graph.target e.edge))

noncomputable def pieceProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (gamma : V → unitInterval) (common : V → Bool) : SourcePiece N → List (ProgramStep N)
  | .bigon B => bigonProgram N C B (gamma B.parents.hybrid) (common B.parents.hybrid)
  | .connector e => [.boundary (.ordinary e.edge e.ordinary),.interval (connectorDuration N C e),
      .boundary (.exit e.edge)]

/-- Endpoints match actual ORIGINAL nodes. No cap on word length/source size. -/
inductive TwoPortWord (N : RootedBinary V E X) : V → V → Type _
  | nil (node : V) : TwoPortWord N node node
  | cons (piece : SourcePiece N) {finish : V}
      (rest : TwoPortWord N piece.outputNode finish) : TwoPortWord N piece.inputNode finish

noncomputable def wordProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (gamma : V → unitInterval) (common : V → Bool) {a b : V} : TwoPortWord N a b → List (ProgramStep N)
  | .nil _ => []
  | .cons piece rest => pieceProgram N C gamma common piece ++ wordProgram N C gamma common rest

lemma actual_ordinary_copy_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (ordinaryCode N s e)) x =
      if copyLocation (state s) x = .node (N.graph.target e) then .edge e else copyLocation (state s) x := by
  rw [show copyLocation (state (ordinaryCode N s e)) x = copyLocation (enterEdge N (state s) e) x from
    decode_encode_copyLocation N.root _ (enterEdge_source_valid N sample _ s.property e).forest x]
  rfl

lemma actual_connector_program (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (e : NonrootConnector N) (s : Code N sample) :
    sourceProgram N r [.boundary (.ordinary e.edge e.ordinary),.interval (connectorDuration N C e),
      .boundary (.exit e.edge)] s =
    (sourceTimeKernel N r (connectorDuration N C e) (ordinaryCode N s e.edge)).map
      (fun d => exitCode N d e.edge) := by
  simp only [sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind]
  rfl

theorem actual_piece_exit_population (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    (piece : SourcePiece N) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node piece.inputNode)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (pieceProgram N C gamma common piece) s).support)
    (l : Copy) (hl : l ∈ (state d).live) : (state d).location l = .node piece.outputNode := by
  cases piece with
  | bigon B => exact actual_nonroot_bigon_exit_population N C r B _ _ s hinput hd l hl
  | connector e =>
      change d ∈ (sourceProgram N r [.boundary (.ordinary e.edge e.ordinary),
        .interval (connectorDuration N C e),.boundary (.exit e.edge)] s).support at hd
      rw [actual_connector_program] at hd
      obtain ⟨z,hz,hzd⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      have hsrc : copyLocation (state s) l = .node (N.graph.target e.edge) :=
        hinput _ (s.property.forest.ancestor_live l)
      have hbefore : copyLocation (state (ordinaryCode N s e.edge)) l = .edge e.edge := by
        rw [actual_ordinary_copy_population,hsrc,if_pos rfl]
      have hduring := actual_time_copy_population N r (connectorDuration N C e)
        (ordinaryCode N s e.edge) hz l
      have hout : copyLocation (state d) l = .node (N.graph.source e.edge) := by
        rw [← hzd,actual_exit_copy_population,hduring,hbefore,if_pos rfl]
      have hrep : (state d).ancestor l = l := d.property.forest.representative l hl
      simpa only [copyLocation,hrep,SourcePiece.outputNode] using hout

/-- The one rootward population is DERIVED for every finite chain, both
inheritance modes and every realization, including empty entering forests. -/
theorem actual_word_exit_population (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : TwoPortWord N a b) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node a)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (wordProgram N C gamma common word) s).support) :
    ∀ l ∈ (state d).live, (state d).location l = .node b := by
  induction word generalizing s with
  | nil node =>
      have he : d = s := by simpa only [wordProgram,sourceProgram,PMF.mem_support_pure_iff] using hd
      exact he ▸ hinput
  | cons piece rest ih =>
      rw [wordProgram,sourceProgram_append] at hd
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih z (actual_piece_exit_population N C r gamma common piece s hinput hz) hdz

omit [DecidableEq E] in
theorem actual_piece_calendar_older (N : RootedBinary V E X) (C : Calendar N.graph)
    (piece : SourcePiece N) : C.age piece.inputNode < C.age piece.outputNode := by
  cases piece with
  | connector e => exact C.edge_older e.edge
  | bigon B =>
      have h := C.edge_older B.parents.parent0
      rw [B.parents.target0,show N.graph.source B.parents.parent0 = B.upper from B.arm_sources false] at h
      exact h

theorem actual_word_calendar_ordered (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (word : TwoPortWord N a b) : C.age a ≤ C.age b := by
  induction word with
  | nil node => exact le_refl _
  | cons piece rest ih => exact (actual_piece_calendar_older N C piece).le.trans ih

omit [DecidableEq E] in
theorem actual_piece_retains_root_blob (N : RootedBinary V E X) (C : Calendar N.graph)
    (gamma : V → unitInterval) (common : V → Bool) (piece : SourcePiece N) :
    .boundary (.root : BoundaryOperation N) ∉ pieceProgram N C gamma common piece := by
  cases piece with
  | connector e => simp [pieceProgram]
  | bigon B => cases hmode : common B.parents.hybrid <;> simp [pieceProgram,bigonProgram,bigonPulse,hmode]

theorem actual_word_retains_root_blob (N : RootedBinary V E X) (C : Calendar N.graph)
    (gamma : V → unitInterval) (common : V → Bool) {a b : V} (word : TwoPortWord N a b) :
    .boundary (.root : BoundaryOperation N) ∉ wordProgram N C gamma common word := by
  induction word with
  | nil node => exact List.not_mem_nil
  | cons piece rest ih =>
      rw [wordProgram,List.mem_append,not_or]
      exact ⟨actual_piece_retains_root_blob N C gamma common piece,ih⟩

noncomputable def wordCurrentKernel (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : TwoPortWord N a b) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node a) :=
  smallerCurrentRootKernel N r (wordProgram N C gamma common word) s (.node a) hinput

/-- Arbitrary finite ORIGINAL nonroot two-port word: exact current-root cap,
single original output population, retained root blob, and whole contextual
UNRANKED law after grafting all prior subtrees with the SAME original register
and retained exterior/root history. K is constructed from original operations.
This theorem has no original-sampled-leaf-count bound. -/
theorem actual_cap_m_finite_two_port_g1
    (N : RootedBinary V E X) {sample : Copy → X} {History Obs : Type*}
    (C : Calendar N.graph) (r : PositivePairRates E) (gamma : V → unitInterval) (common : V → Bool)
    {a b : V} (word : TwoPortWord N a b) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node a)
    (m : Nat) (cap : (state s).live.card ≤ m) (history : History)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    Fintype.card (SelectedCopy (state s).live) ≤ m ∧
    (∀ d ∈ (sourceProgram N r (wordProgram N C gamma common word) s).support,
      ∀ l ∈ (state d).live, (state d).location l = .node b) ∧
    (.boundary (.root : BoundaryOperation N) ∉ wordProgram N C gamma common word) ∧
    ((sourceProgram N r (wordProgram N C gamma common word) s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
      (wordCurrentKernel N C r gamma common word s hinput).bind
        (fun F => exterior (history,(state s).register,
          F.image (graftUnranked (fun l => (state s).genealogy l.val))))) := by
  refine ⟨actual_kernel_carrier_cap N s m cap,?_,actual_word_retains_root_blob N C gamma common word,?_⟩
  · intro d hd
    exact actual_word_exit_population N C r gamma common word s hinput hd
  · exact actual_original_contextual_forest_replacement N r (wordProgram N C gamma common word)
      s (.node a) hinput history exterior

end G1FiniteTwoPortChain
