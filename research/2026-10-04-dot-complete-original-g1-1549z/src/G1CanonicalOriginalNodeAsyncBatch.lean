import G1CanonicalOriginalNodeAsyncStep

/-! The whole original same-date node batch is a genuine asyncProgram on the
canonical complete original actor/base coordinates. Partial-batch private
region support is propagated by actual source kernels, not assumed as a law. -/
namespace G1CanonicalOriginalNodeAsyncBatch
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1OriginalActorOperationOwnership G1CanonicalActorLifecycleCompiler G1CanonicalPendingActorSets
open G1CanonicalFiniteActiveEpochAdmission G1CanonicalOriginalActorOpening G1ActualOriginalPrivateAsyncStep
open G1TaggedOriginalCalendar G1PendingActorInterfaceCommutation G1OriginalSpanRegion
open G1CanonicalOriginalNodeAsyncStep G1NaturalActiveActorFrontier G1ContextualForestReplacement
open G1CanonicalComponentSegment G1InitializedFrontierPrefix G1ActiveCoreBridgeCohorts
open UnifiedLean.Source.SourceInitializedCalendar G1ActualJointProgram
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def canonicalDateProjection (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X} (date : ℝ) (s : Code O.network sample) :=
  originalAsyncProjection O (activeOriginalBase O D sample (canonicalDateActors T date))
    (originalPendingSlots O D sample (canonicalDateActors T date)) s

def DateActorRegion (O : Source.{u,v,w} X) {T : Source X} (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X} (date : ℝ) (s : Code O.network sample) : Prop :=
  ∀ actor ∈ canonicalDateActors T date, ∀ x ∈ originalInsideCopies O sample (actorInput O D actor),
    SpanLocation O (bridgeSpan O T D actor.val actor.property) (copyLocation (state s) x)

lemma actual_node_source_preserves_date_actor_region (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (node : O.Vertex) (s : Code O.network sample) (hin : DateActorRegion O D date s)
    {d : Code O.network sample} (hd : d ∈ (sourceProgramStep O.network r (eraseEvent O H gamma common (.node node)) s).support) :
    DateActorRegion O D date d := by
  intro actor hm
  have hsafe : ∀ op ∈ [eraseEvent O H gamma common (.node node)],
      G1OriginalEpochPanelCompression.EdgeSafeStep O.network H (fun h => gamma h.val) (fun h => common h.val)
        {actorCut O H D hD actor} op := by
    intro op hop
    have heq : op = eraseEvent O H gamma common (.node node) := by simpa using hop
    subst op
    exact Or.inr (Or.inr ⟨node,rfl⟩)
  exact actual_safe_program_actor_region O H D hD actor gamma common r
    [eraseEvent O H gamma common (.node node)] hsafe s _ (hin actor hm)
    (by simpa only [sourceProgram,PMF.bind_pure] using hd)

/-- A complete list of actual original nodes at the same original date maps
exactly to the concrete canonical asyncProgram. Region support is needed only
at its input and is derived for every subsequent source-supported state. -/
theorem actual_same_date_original_nodes_async_program (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy] {sample : Copy → X}
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (date : ℝ) (nodes : List O.Vertex) (hdate : ∀ node ∈ nodes, O.calendar.age node = date)
    (s : Code O.network sample) (hin : DateActorRegion O D date s) :
    (sourceProgram O.network r (nodes.map (fun node => eraseEvent O H gamma common (.node node))) s).map
      (canonicalDateProjection O D date) =
    asyncProgram (nodes.map (canonicalNodeAsyncOperation O H D hD sample gamma common r))
      (canonicalDateProjection O D date s) := by
  induction nodes generalizing s with
  | nil => simp [sourceProgram,asyncProgram,PMF.pure_map]
  | cons node nodes ih =>
    have ha := hdate node (List.mem_cons_self)
    have ht := fun n hn => hdate n (List.mem_cons_of_mem node hn)
    have hstep : (sourceProgramStep O.network r (eraseEvent O H gamma common (.node node)) s).map
        (canonicalDateProjection O D date) =
        asyncStep (canonicalNodeAsyncOperation O H D hD sample gamma common r node)
          (canonicalDateProjection O D date s) := by
      have he := actual_canonical_original_node_async_step O H D hD gamma common r node s
        (by simpa only [ha,DateActorRegion] using hin)
      unfold canonicalDateProjection
      simpa only [sourceProgram,PMF.bind_pure,ha] using he
    calc
      _ = (sourceProgramStep O.network r (eraseEvent O H gamma common (.node node)) s).bind
          (fun d => asyncProgram (nodes.map (canonicalNodeAsyncOperation O H D hD sample gamma common r))
            (canonicalDateProjection O D date d)) := by
        simp only [List.map_cons,sourceProgram,PMF.map_bind]
        apply bind_eq_of_eq_on_support
        intro d hd
        exact ih ht d (actual_node_source_preserves_date_actor_region O H D hD gamma common r date node s hin hd)
      _ = ((sourceProgramStep O.network r (eraseEvent O H gamma common (.node node)) s).map
          (canonicalDateProjection O D date)).bind
          (asyncProgram (nodes.map (canonicalNodeAsyncOperation O H D hD sample gamma common r))) := by
        rw [PMF.bind_map]; rfl
      _ = _ := by rw [hstep]; rfl

/-- Initialized canonical admission discharges the batch input region premise.
This is the full literal original nodeOperations batch, with complete old
labels, genealogy, population and SAME register in every runtime coordinate. -/
theorem actual_real_original_node_batch_async_program (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
    (sample : Copy → X) (register : O.Vertex → Bool)
    (gamma : O.Vertex → unitInterval) (common : O.Vertex → Bool) (r : PositivePairRates O.Edge)
    (node : O.Vertex) {s : Code O.network sample}
    (hs : s ∈ (sourceProgram O.network r
      (actualFrontierProgram O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node))
      (initialCode O.network sample register)).support) :
    (sourceProgram O.network r
      (nodeOperations O.network O.calendar H (fun h => gamma h.val) (fun h => common h.val) (O.calendar.age node)) s).map
      (canonicalDateProjection O D (O.calendar.age node)) =
    asyncProgram (((Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = O.calendar.age node)).toList).map
      (canonicalNodeAsyncOperation O H D hD sample gamma common r))
      (canonicalDateProjection O D (O.calendar.age node) s) := by
  apply actual_same_date_original_nodes_async_program O H D hD gamma common r
    (O.calendar.age node) ((Finset.univ.filter (fun v : O.Vertex => O.calendar.age v = O.calendar.age node)).toList)
  · intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2
  · intro actor hm
    exact actual_real_frontier_active_actor_region O H D hD actor node
      (Finset.mem_filter.mp (Finset.mem_toList.mp hm)).2 sample register gamma common r hs

#print axioms actual_real_original_node_batch_async_program
end G1CanonicalOriginalNodeAsyncBatch
