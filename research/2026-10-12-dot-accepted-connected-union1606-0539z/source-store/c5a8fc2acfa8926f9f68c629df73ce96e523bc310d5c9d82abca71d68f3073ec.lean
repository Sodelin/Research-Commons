import G1ActualCutDescendants
import UnifiedLean.Source.SourceInitializedCalendar

/-! Derived initialized-calendar node/edge entry invariants. Contributor: dot,
2026-10-03. Abstract SourceValid/epoch-ready codes can contain future INTERNAL
nodes or prematurely entered edges. The genuine initialized source is proved
to exclude both, using its actual original exits and node operations. -/
namespace G1NaturalCalendarNodes
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceProgramTransport
open G1NonrootBigonKernel UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

def NaturalNodes (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (a : ℝ) (s : State V E Copy) : Prop :=
  ∀ x : Copy, ∀ v : V, copyLocation s x = .node v →
    v = N.leaf (sample x) ∨ C.age v ≤ a

def EnteredEdges (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (s : State V E Copy) : Prop :=
  ∀ x : Copy, ∀ e : E, copyLocation s x = .edge e → C.age (N.graph.target e) ≤ a

def NaturalState (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (a : ℝ) (s : State V E Copy) : Prop := NaturalNodes N C sample a s ∧ EnteredEdges N C a s

lemma actual_initial_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (a : ℝ) :
    NaturalState N C sample a (state (initialCode N sample register)) := by
  have hpop (x : Copy) : copyLocation (state (initialCode N sample register)) x = .node (N.leaf (sample x)) := by
    exact decode_encode_copyLocation N.root _ (initial_source_valid N sample register).forest x
  constructor
  · intro x v hv
    rw [hpop] at hv
    exact Or.inl (Location.node.inj hv).symm
  · intro x e he
    rw [hpop] at he
    cases he

lemma natural_state_mono (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    {a b : ℝ} {s : State V E Copy} (hab : a ≤ b) (hs : NaturalState N C sample a s) :
    NaturalState N C sample b s := by
  exact ⟨fun x v hv => (hs.1 x v hv).imp id (fun h => h.trans hab),fun x e he => (hs.2 x e he).trans hab⟩

lemma actual_time_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (a : ℝ)
    (hs : NaturalState N C sample a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : NaturalState N C sample a (state d) := by
  constructor
  · intro x v hv
    rw [actual_time_copy_population N r t s hd x] at hv
    exact hs.1 x v hv
  · intro x e he
    rw [actual_time_copy_population N r t s hd x] at he
    exact hs.2 x e he

lemma actual_exit_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (s : Code N sample) (e : E) (a : ℝ)
    (ha : C.age (N.graph.source e) = a) (hs : NaturalState N C sample a (state s)) :
    NaturalState N C sample a (state (exitCode N s e)) := by
  constructor
  · intro x v hv
    rw [exitCode_copyLocation] at hv
    unfold exitLocation at hv
    by_cases hp : copyLocation (state s) x = .edge e
    · rw [if_pos hp] at hv
      have h := Location.node.inj hv
      exact Or.inr (by rw [← h,ha])
    · rw [if_neg hp] at hv
      exact hs.1 x v hv
  · intro x f hf
    rw [exitCode_copyLocation] at hf
    unfold exitLocation at hf
    by_cases hp : copyLocation (state s) x = .edge e
    · rw [if_pos hp] at hf
      cases hf
    · rw [if_neg hp] at hf
      exact hs.2 x f hf

lemma actual_node_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (a : ℝ) (ha : C.age v = a) (s : Code N sample)
    (hs : NaturalState N C sample a (state s)) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    NaturalState N C sample a (state d) := by
  constructor
  · intro x u hu
    have hm := actual_original_node_kernel_movement N H gamma common v s hd x
    have hold : copyLocation (state s) x = .node u := by
      by_contra hn
      exact node_move_never_creates_node N hm hn hu
    exact hs.1 x u hold
  · intro x e he
    have hm := actual_original_node_kernel_movement N H gamma common v s hd x
    unfold NodeMovement at hm
    by_cases hn : copyLocation (state s) x = .node v
    · rw [if_pos hn] at hm
      by_cases hr : v = N.root
      · rw [if_pos hr] at hm
        rw [hm] at he
        cases he
      · rw [if_neg hr] at hm
        obtain ⟨f,hf,hnew⟩ := hm
        have hfe : f = e := Location.edge.inj (hnew.symm.trans he)
        rw [← hfe,hf,ha]
    · rw [if_neg hn] at hm
      exact hs.2 x e (hm ▸ he)

lemma actual_exit_list_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (es : List E) (a : ℝ)
    (ha : ∀ e ∈ es, C.age (N.graph.source e) = a) (s : Code N sample)
    (hs : NaturalState N C sample a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    NaturalState N C sample a (state d) := by
  induction es generalizing s with
  | nil =>
      have h : d = s := by simpa [sourceProgram] using hd
      exact h ▸ hs
  | cons e es ih =>
      have hdest : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) (exitCode N s e)).support := by
        simpa [sourceProgram,sourceProgramStep,boundaryKernel] using hd
      exact ih (fun f hf => ha f (List.mem_cons_of_mem e hf)) (exitCode N s e)
        (actual_exit_natural N C s e a (ha e (by simp)) hs) hdest

lemma actual_node_list_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (vs : List V) (a : ℝ)
    (ha : ∀ v ∈ vs, C.age v = a) (s : Code N sample)
    (hs : NaturalState N C sample a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))) s).support) :
    NaturalState N C sample a (state d) := by
  induction vs generalizing s with
  | nil =>
      have h : d = s := by simpa [sourceProgram] using hd
      exact h ▸ hs
  | cons v vs ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih (fun u hu => ha u (List.mem_cons_of_mem v hu)) m
        (actual_node_natural N C H gamma common v a (ha v (by simp)) s hs hm) hdm

/-- Every actual generated boundary batch preserves the initialized-source
node/edge invariant. The derivation uses original-site movement formulas. -/
theorem actual_boundary_batch_natural (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : NaturalState N C sample a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    NaturalState N C sample a (state d) := by
  rw [boundaryOperations,sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hn := actual_exit_list_natural N C r _ a (by
    intro e he; exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) s hs hm
  exact actual_node_list_natural N C H gamma common r _ a (by
    intro v hv; exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2) m hn hdm

end G1NaturalCalendarNodes
