import G6FiniteHistoryEndpoint
import G4ActualBelowMeetingSupport
import G1OriginalExitBatchBinding

/-!
Naturally initialized one-child input for the original tied before-node word.
Contributor: Codex / lean_integration_successor, 11 October 2026.
UNCOMPILED SOURCE PROPOSAL. The checked cdaa one-child support lemmas are reused;
no two-child RouteMeetingGeometry is instantiated at a hybrid.
Source-only v2 opens the existing SourceNaturalInitialization namespace for
the originalRegister identifier; every declaration and proof is unchanged.

The original child edge is explicitly required to occur on EVERY root-to-sample
path for each supplied copy. Calendar/node splits are the actual literal lists.
All original exits and tied foreign node operations remain in their given order.
The endpoint reader is the accepted recordEnd, not a replacement process.
-/
namespace GProgram.G6.InitializedCommonInput

open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.G6.PrivateRegisterHistory
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open G1InitializedFrontierPrefix G1OriginalNodeBatchBinding G1OriginalExitBatchBinding
open DotG4.ActualBelowMeetingSupport
open GProgram.G6.OriginalCommonPrefix GProgram.G6.NaturalCommonForestFactorization
open GProgram.G6.FiniteHistoryEndpoint
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Literal list alignment only: stopBeforeTail includes the final interval and
none of the stop-date batch. Dates before the stop are kept in original order. -/
private lemma stop_tail_before_site (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre post : List ℝ) (stop a : ℝ)
    (hpre : ∀ b ∈ pre, b ≠ stop) :
    stopBeforeTail N C H gamma common stop a (pre ++ stop :: post) =
      calendarTail N C H gamma common a pre ++
        [.interval (Real.toNNReal (stop - finalDate a pre))] := by
  induction pre generalizing a with
  | nil => simp only [List.nil_append, stopBeforeTail, if_pos rfl,
      calendarTail, finalDate]
  | cons b pre ih =>
      have hb : b ≠ stop := hpre b List.mem_cons_self
      have ht := ih b (fun c hc => hpre c (List.mem_cons_of_mem b hc))
      simpa only [List.cons_append, stopBeforeTail, if_neg hb, calendarTail,
        finalDate, List.append_assoc] using congrArg
          (fun tail : List (ProgramStep N) =>
            ProgramStep.interval (Real.toNNReal (b - a)) ::
              (boundaryOperations N C H gamma common b ++ tail)) ht

/-- The accepted beforeNodeWord is exactly the natural frontier prefix followed
by the literal earlier members of this tied node batch. No permutation is used. -/
theorem beforeNodeWord_eq_frontier_nodes (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (v : V) (pre post : List ℝ) (nodesBefore : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age v :: post) :
    beforeNodeWord N C H gamma common v pre nodesBefore =
      actualFrontierProgram N C H gamma common (C.age v) ++
        nodesBefore.map (fun w => .boundary (originalNodeOperation N H gamma common w)) := by
  have ho : (pre ++ C.age v :: post).Pairwise (· < ·) := by
    rw [← hdates]
    exact original_dates_strict N C
  have hp : ∀ b ∈ pre, b ≠ C.age v := by
    intro b hb
    exact ne_of_lt ((List.pairwise_append.mp ho).2.2 b hb (C.age v) List.mem_cons_self)
  cases pre with
  | nil => simp [beforeNodeWord, actualFrontierProgram, beforeBoundaryProgram, hdates]
  | cons a dates =>
      have ha : a ≠ C.age v := hp a List.mem_cons_self
      have ht := stop_tail_before_site N C H gamma common dates post (C.age v) a
        (fun b hb => hp b (List.mem_cons_of_mem a hb))
      simp only [beforeNodeWord, actualFrontierProgram, beforeBoundaryProgram,
        hdates, List.cons_append, if_neg ha]
      rw [ht]
      simp only [List.append_assoc]

/-- The source-side mandatory child route gives a one-child incoming location.
This uses the checked support theorem and its ready/below lemma, not Geometry. -/
theorem actual_initialized_before_one_child (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (sample : Copy → X) (register : V → Bool) (r : PositivePairRates E)
    (v : V) (e : E) (he : N.graph.source e = v) (x : Copy)
    (hp : ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (beforeBoundaryProgram N C H gamma common (C.age v))
      (initialCode N sample register)).support) :
    copyLocation (state d) x = .edge e := by
  have hr := actual_initialized_before_boundary_support N C sample register H gamma common r
    (C.age v) (original_date_scheduled N C v) hd
  have hy := mandatory_child_tip_younger N C (sample x) v e he hp
  apply mandatory_child_of_ready_below N C d x v e he hp hr.1
  apply actual_initialized_take_below N C H gamma common v sample register r x hy
    (beforeBoundaryProgram N C H gamma common (C.age v)).length
  simpa only [List.take_length] using hd

/-- The complete unchanged exit batch hits that same child and leaves the copy
at its original source vertex. All other exits remain, in the literal list. -/
theorem actual_initialized_frontier_one_child (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (sample : Copy → X) (register : V → Bool) (r : PositivePairRates E)
    (v : V) (e : E) (he : N.graph.source e = v) (x : Copy)
    (hp : ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common (C.age v))
      (initialCode N sample register)).support) :
    copyLocation (state d) x = .node v := by
  rw [actualFrontierProgram, sourceProgram_append] at hd
  obtain ⟨z, hz, hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  rw [actual_exit_list_program] at hzd
  obtain rfl := (PMF.mem_support_pure_iff _ _).mp hzd
  have hem : e ∈ (Finset.univ.filter
      (fun f : E => C.age (N.graph.source f) = C.age v)).toList := by
    apply Finset.mem_toList.mpr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]⟩
  rw [actual_exit_list_copy_location,
    actual_initialized_before_one_child N C H gamma common sample register r v e he x hp hz,
    actual_exit_location_list_hit N _ e hem, he]

/-- Composition of the accepted foreign-node movement lemma. No tied node at an
other original vertex moves this already arrived full panel away from v. -/
private theorem foreign_node_list_support (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) {sample : Copy → X} (r : PositivePairRates E)
    (v : V) (vs : List V) :
    v ∉ vs → ∀ s : Code N sample, AtNodePanel (state s) Finset.univ v →
      ∀ d : Code N sample,
      d ∈ (sourceProgram N r
        (vs.map (fun w => .boundary (originalNodeOperation N H gamma common w))) s).support →
      AtNodePanel (state d) Finset.univ v := by
  induction vs with
  | nil =>
      intro _ s hs d hd
      have heq : d = s := by simpa only [List.map_nil, sourceProgram,
        PMF.mem_support_pure_iff] using hd
      simpa only [heq] using hs
  | cons w vs ih =>
      intro hn s hs d hd
      change d ∈ ((boundaryKernel N (originalNodeOperation N H gamma common w) s).bind
        (sourceProgram N r
          (vs.map (fun u => .boundary (originalNodeOperation N H gamma common u))))).support at hd
      obtain ⟨z, hz, hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hw : w ≠ v := by
        intro heq
        exact hn (List.mem_cons.mpr (Or.inl heq.symm))
      have ht : v ∉ vs := fun hv => hn (List.mem_cons_of_mem w hv)
      exact ih ht z (actual_foreign_node_preserves_panel N H gamma common s Finset.univ
        v w hw hs hz) d hzd

/-- The real tied node prefix excludes its own site because its original
Finset.toList is Nodup. All current source copies remain at the one site. -/
theorem actual_initialized_beforeNode_copy_input (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (sample : Copy → X) (register : V → Bool) (r : PositivePairRates E)
    (v : V) (e : E) (he : N.graph.source e = v)
    (hp : ∀ x : Copy, ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age v :: post)
    (hnodes : (Finset.univ.filter (fun w : V => C.age w = C.age v)).toList =
      nodesBefore ++ v :: nodesAfter)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (beforeNodeWord N C H gamma common v pre nodesBefore)
      (initialCode N sample register)).support) :
    ∀ x : Copy, copyLocation (state d) x = .node v := by
  have hn : (nodesBefore ++ v :: nodesAfter).Nodup := by
    rw [← hnodes]
    exact Finset.nodup_toList _
  have hnot : v ∉ nodesBefore := by
    have h := (List.nodup_cons.mp (List.nodup_middle.mp hn)).1
    intro hm
    exact h (List.mem_append.mpr (Or.inl hm))
  rw [beforeNodeWord_eq_frontier_nodes N C H gamma common v pre post nodesBefore hdates,
    sourceProgram_append] at hd
  obtain ⟨z, hz, hzd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hs : AtNodePanel (state z) Finset.univ v := by
    intro x _
    exact actual_initialized_frontier_one_child N C H gamma common sample register r
      v e he x (hp x) hz
  have hpanel := foreign_node_list_support N H gamma common r v nodesBefore hnot z hs d hzd
  intro x
  exact hpanel x (Finset.mem_univ x)

/-- This is the full live-owner input needed by the local original bigon
consumer, not merely a selected or erased copy-location observation. -/
theorem actual_initialized_beforeNode_live_input (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (sample : Copy → X) (register : V → Bool) (r : PositivePairRates E)
    (v : V) (e : E) (he : N.graph.source e = v)
    (hp : ∀ x : Copy, ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age v :: post)
    (hnodes : (Finset.univ.filter (fun w : V => C.age w = C.age v)).toList =
      nodesBefore ++ v :: nodesAfter)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (beforeNodeWord N C H gamma common v pre nodesBefore)
      (initialCode N sample register)).support) :
    ∀ l ∈ (state d).live, (state d).location l = .node v := by
  intro l hl
  have hc := actual_initialized_beforeNode_copy_input N C H gamma common sample register r
    v e he hp pre post nodesBefore nodesAfter hdates hnodes hd l
  change (state d).location ((state d).ancestor l) = .node v at hc
  rw [d.property.forest.representative l hl] at hc
  exact hc

/-- The exact natural initializer and its SAME Fin history now supply the local
before-node hinput, under the explicit mandatory-child/source and literal-list
premises. No Old conditioning or seed independence is added here. -/
theorem actual_natural_beforeNode_recordEnd_input (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (sample : Copy → X) (p : HybridProbabilities N) (P : Finset V) (r : PositivePairRates E)
    (v : V) (e : E) (he : N.graph.source e = v)
    (hp : ∀ x : Copy, ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age v :: post)
    (hnodes : (Finset.univ.filter (fun w : V => C.age w = C.age v)).toList =
      nodesBefore ++ v :: nodesAfter) :
    let pastOps := beforeNodeWord N C H gamma common v pre nodesBefore
    ∀ a ∈ (initializedSourceHistory N r pastOps (naturalInitialJoint N P sample p)).support,
      ∀ l ∈ (state (recordEnd pastOps.length a.2.1 a.2.2)).live,
        (state (recordEnd pastOps.length a.2.1 a.2.2)).location l = .node v := by
  dsimp only
  intro a ha
  apply actual_initialized_recordEnd_property N r
    (beforeNodeWord N C H gamma common v pre nodesBefore) (naturalInitialJoint N P sample p)
    (fun d => ∀ l ∈ (state d).live, (state d).location l = .node v) ?_ a ha
  intro q hq d hd
  unfold naturalInitialJoint at hq
  obtain ⟨coin, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
  exact actual_initialized_beforeNode_live_input N C H gamma common sample
    (originalRegister N coin) r v e he hp pre post nodesBefore nodesAfter hdates hnodes hd

#print axioms beforeNodeWord_eq_frontier_nodes
#print axioms actual_initialized_before_one_child
#print axioms actual_initialized_frontier_one_child
#print axioms actual_initialized_beforeNode_copy_input
#print axioms actual_initialized_beforeNode_live_input
#print axioms actual_natural_beforeNode_recordEnd_input
end GProgram.G6.InitializedCommonInput
