import G6ProtectedChildCarrier
import G6GuardedCommonSeedFibre
import G6OriginalSpanJointContext

/-!
Actual guarded boundary PHASE relation, not a physical scalar-spine cast.
Cloud Sol literature/organization structural lane, 8 October 2026, 06:16 UTC.
Original graph, initialization, forest and boundary providers: Dot.
Compiler UNCHECKED; outside the sole frozen179. No shared source is changed.

The original child occurrence maps to a DISTINCT spine occurrence only in a
boundary snapshot. Its original endpoint clocks/rate/span and full old Code
remain auxiliary. No future kernel or positive-word admission is inferred.
Old tagged/calendar history is an unchanged external receiver argument: Code
itself omits event history, as in the inherited snapshot representation.
-/

namespace UnifiedLean.G6.BoundaryPhaseRelation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1BigonSpliceGraph G1BigonFootprint G1SplicedSourceAdmission
open G1InitializedFrontierPrefix G1ExtractedComponentProgram
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.G6.OriginalSpliceAdapter UnifiedLean.G6.SpineBoundaryCarrier
open UnifiedLean.G6.ProtectedChildCarrier
open scoped Classical

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable (N : RootedBinary V E X)
variable (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
variable (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
variable (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)

/-- Retained occurrences retain their IDs. Only the distinguished child PHASE
uses the constructed graph's new occurrence, with no scalar rate assigned. -/
noncomputable def phaseEdge (e : ChildGuardedEdge N hcut b hb hp) :
    SplicedEdge N b (derivedBigon N hcut b hb hp) :=
  if hd : e.val = (derivedBigon N hcut b hb hp).child then Sum.inr ()
  else Sum.inl ⟨e.val, e.property.resolve_right hd⟩

noncomputable def intoBoundaryPhase : ChildGuardedLocation N hcut b hb hp →
    Location (SplicedVertex N b (derivedBigon N hcut b hb hp))
      (SplicedEdge N b (derivedBigon N hcut b hb hp))
  | .node v => .node v
  | .edge e => .edge (phaseEdge N hcut b hb hp e)
  | .rootPopulation v => .rootPopulation v

theorem phase_edge_injective : Function.Injective (phaseEdge N hcut b hb hp) := by
  intro a c he
  by_cases ha : a.val = (derivedBigon N hcut b hb hp).child
  · by_cases hc : c.val = (derivedBigon N hcut b hb hp).child
    · exact Subtype.ext (ha.trans hc.symm)
    · simp [phaseEdge, ha, hc] at he
  · by_cases hc : c.val = (derivedBigon N hcut b hb hp).child
    · simp [phaseEdge, ha, hc] at he
    · have hi : (⟨a.val, a.property.resolve_right ha⟩ :
          RetainedEdge N b (derivedBigon N hcut b hb hp)) =
          ⟨c.val, c.property.resolve_right hc⟩ := by
        apply Sum.inl.inj
        simpa [phaseEdge, ha, hc] using he
      exact Subtype.ext (congrArg Subtype.val hi)

theorem boundary_phase_injective : Function.Injective (intoBoundaryPhase N hcut b hb hp) :=
  (locationEmbedding (Function.Embedding.refl _)
    ⟨phaseEdge N hcut b hb hp, phase_edge_injective N hcut b hb hp⟩).injective

theorem protected_child_phase :
    intoBoundaryPhase N hcut b hb hp (.edge (protectedChild N hcut b hb hp)) =
      .edge (Sum.inr ()) := by
  simp [intoBoundaryPhase, phaseEdge, protectedChild]

theorem retained_edge_phase
    (e : RetainedEdge N b (derivedBigon N hcut b hb hp)) :
    intoBoundaryPhase N hcut b hb hp (.edge ⟨e.val, Or.inl e.property⟩) =
      .edge (Sum.inl e) := by
  have hd : e.val ≠ (derivedBigon N hcut b hb hp).child := by
    intro he
    apply e.property
    rw [he]
    simp [removedEdges]
  simp [intoBoundaryPhase, phaseEdge, hd]

/-- The actual younger node's entry advances a PHASE, not an edge-ID cast. -/
noncomputable def childEntryPhase (q : ChildGuardedLocation N hcut b hb hp) :
    ChildGuardedLocation N hcut b hb hp :=
  if q = .node (descendantInterface N b (derivedBigon N hcut b hb hp))
  then .edge (protectedChild N hcut b hb hp) else q

theorem original_child_entry_phase (q : ChildGuardedLocation N hcut b hb hp) :
    ordinaryLocation N (derivedBigon N hcut b hb hp).child
      (intoOriginalChildGuarded N hcut b hb hp q) =
      intoOriginalChildGuarded N hcut b hb hp (childEntryPhase N hcut b hb hp q) := by
  have hn : intoOriginalChildGuarded N hcut b hb hp q =
      .node (N.graph.target (derivedBigon N hcut b hb hp).child) ↔
      q = .node (descendantInterface N b (derivedBigon N hcut b hb hp)) := by
    constructor
    · intro he
      exact (intoOriginalChildGuarded N hcut b hb hp).injective he
    · rintro rfl
      rfl
  by_cases hq : q = .node (descendantInterface N b (derivedBigon N hcut b hb hp))
  · subst q
    simp [ordinaryLocation, childEntryPhase, intoOriginalChildGuarded,
      locationEmbedding, descendantInterface, protectedChild]
  · rw [ordinaryLocation, if_neg (hn.not.mpr hq), childEntryPhase, if_neg hq]

theorem constructed_child_entry_phase (q : ChildGuardedLocation N hcut b hb hp) :
    ordinaryLocation (suppressedNetwork N hcut b hb hp) (Sum.inr ())
      (intoBoundaryPhase N hcut b hb hp q) =
      intoBoundaryPhase N hcut b hb hp (childEntryPhase N hcut b hb hp q) := by
  have hn : intoBoundaryPhase N hcut b hb hp q =
      .node (descendantInterface N b (derivedBigon N hcut b hb hp)) ↔
      q = .node (descendantInterface N b (derivedBigon N hcut b hb hp)) := by
    cases q <;> simp [intoBoundaryPhase]
  by_cases hq : q = .node (descendantInterface N b (derivedBigon N hcut b hb hp))
  · subst q
    simp [ordinaryLocation, childEntryPhase, intoBoundaryPhase, phaseEdge,
      protectedChild, suppressedNetwork, splicedNetwork, spliceGraph]
  · change (if intoBoundaryPhase N hcut b hb hp q =
        .node (descendantInterface N b (derivedBigon N hcut b hb hp)) then
      .edge (Sum.inr ()) else intoBoundaryPhase N hcut b hb hp q) = _
    rw [if_neg (hn.not.mpr hq), childEntryPhase, if_neg hq]

/-- This uses only RETAINED starting vertices; collapseVertex sends removed
vertices rootward and is deliberately not used as an all-Code physical cast. -/
theorem retained_descendant (v : SplicedVertex N b (derivedBigon N hcut b hb hp))
    (x : X) (hd : N.graph.DReach v.val (N.leaf x)) :
    (suppressedNetwork N hcut b hb hp).graph.DReach v
      ((suppressedNetwork N hcut b hb hp).leaf x) := by
  have h := actual_original_reach_collapse N hcut b
    (derivedBigon N hcut b hb hp) hd
  rw [collapse_kept N b (derivedBigon N hcut b hb hp) v,
    collapse_kept N b (derivedBigon N hcut b hb hp)
      (retainedTaxa N b (derivedBigon N hcut b hb hp) x)] at h
  exact h

/-- At the child phase, the new edge has the SAME descendant endpoint v.
Its older endpoint/rate are not claimed equal to the original child edge. -/
theorem phase_descends (q : ChildGuardedLocation N hcut b hb hp) (x : X)
    (hd : DescendsTo N (intoOriginalChildGuarded N hcut b hb hp q) x) :
    DescendsTo (suppressedNetwork N hcut b hb hp)
      (intoBoundaryPhase N hcut b hb hp q) x := by
  cases q with
  | node v => exact retained_descendant N hcut b hb hp v x hd
  | edge e =>
      by_cases he : e.val = (derivedBigon N hcut b hb hp).child
      · change N.graph.DReach (N.graph.target e.val) (N.leaf x) at hd
        rw [he] at hd
        simpa [intoBoundaryPhase, phaseEdge, he, DescendsTo,
          suppressedNetwork, splicedNetwork, spliceGraph] using
          retained_descendant N hcut b hb hp
            (descendantInterface N b (derivedBigon N hcut b hb hp)) x hd
      · let er : RetainedEdge N b (derivedBigon N hcut b hb hp) :=
          ⟨e.val, e.property.resolve_right he⟩
        change N.graph.DReach (N.graph.target er.val) (N.leaf x) at hd
        simpa [intoBoundaryPhase, phaseEdge, he, DescendsTo,
          suppressedNetwork, splicedNetwork, spliceGraph, er] using
          retained_descendant N hcut b hb hp
            (retainedTarget N hcut b (derivedBigon N hcut b hb hp) er) x hd
  | rootPopulation v =>
      change v.val = N.root ∧ N.graph.DReach v.val (N.leaf x) at hd
      refine ⟨Subtype.ext hd.1, retained_descendant N hcut b hb hp v x hd.2⟩

/-- A pointwise population-support property. Its actual initialized-source
derivation is consumed below; it is not a desired distribution/law field. -/
def PhaseSupported {sample : Copy → X} (s : Code N sample) : Prop :=
  ∀ x : Copy, ∃ q : ChildGuardedLocation N hcut b hb hp,
    intoOriginalChildGuarded N hcut b hb hp q = copyLocation (state s) x

noncomputable def ownerPhase {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) (x : Copy) :
    ChildGuardedLocation N hcut b hb hp := Classical.choose (hs x)

theorem owner_phase_original {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) (x : Copy) :
    intoOriginalChildGuarded N hcut b hb hp (ownerPhase N hcut b hb hp s hs x) =
      copyLocation (state s) x := Classical.choose_spec (hs x)

theorem owner_phase_current_owner {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) (x : Copy) :
    ownerPhase N hcut b hb hp s hs ((state s).ancestor x) =
      ownerPhase N hcut b hb hp s hs x := by
  apply (intoOriginalChildGuarded N hcut b hb hp).injective
  rw [owner_phase_original, owner_phase_original]
  unfold copyLocation
  rw [s.property.forest.representative _ (s.property.forest.ancestor_live x)]

/-- A boundary-state constructor preserving the entire LIVE forest/current
owner partition and the retained full register. The old Code/register/history
is retained separately in the coupling; no old private register is re-coined. -/
noncomputable def phaseState {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) :
    State (SplicedVertex N b (derivedBigon N hcut b hb hp))
      (SplicedEdge N b (derivedBigon N hcut b hb hp)) Copy where
  live := (state s).live
  ancestor := (state s).ancestor
  genealogy := (state s).genealogy
  location l := intoBoundaryPhase N hcut b hb hp (ownerPhase N hcut b hb hp s hs l)
  register v := (state s).register v.val
  history := []

theorem phase_state_copy_location {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) (x : Copy) :
    copyLocation (phaseState N hcut b hb hp s hs) x =
      intoBoundaryPhase N hcut b hb hp (ownerPhase N hcut b hb hp s hs x) := by
  change intoBoundaryPhase N hcut b hb hp
    (ownerPhase N hcut b hb hp s hs ((state s).ancestor x)) = _
  rw [owner_phase_current_owner]

theorem phase_state_source_valid {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) :
    SourceValid (suppressedNetwork N hcut b hb hp) sample
      (phaseState N hcut b hb hp s hs) := by
  refine ⟨?_, ?_⟩
  · exact ⟨s.property.forest.ancestor_live, s.property.forest.representative,
      s.property.forest.leaf_fiber, s.property.forest.wellLabelled⟩
  · intro x
    rw [phase_state_copy_location]
    apply phase_descends N hcut b hb hp
    rw [owner_phase_original]
    exact s.property.original_descendant x

noncomputable def phaseCode {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) :
    Code (suppressedNetwork N hcut b hb hp) sample :=
  admittedCode _ sample (phaseState N hcut b hb hp s hs)
    (phase_state_source_valid N hcut b hb hp s hs)

/-- Explicit data relation: no sourceStep/kernel equality, no future law,
and no literal cross-graph Code equality occurs among these fields. -/
structure Related {sample : Copy → X} (s : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample) : Prop where
  live : (state t).live = (state s).live
  ancestor : (state t).ancestor = (state s).ancestor
  genealogy : ∀ l ∈ (state s).live, (state t).genealogy l = (state s).genealogy l
  outsideRegister : ∀ v, (state t).register v = (state s).register v.val
  location : ∀ x, ∃ q : ChildGuardedLocation N hcut b hb hp,
    intoOriginalChildGuarded N hcut b hb hp q = copyLocation (state s) x ∧
      intoBoundaryPhase N hcut b hb hp q = copyLocation (state t) x

/-- Matching phase locations retain exactly the SAME current-population
partition, rather than merely equal marginal copy locations. Current owners
and live forest equality are the separate fields of Related. -/
theorem related_current_population_iff {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (x y : Copy) :
    copyLocation (state s) x = copyLocation (state s) y ↔
      copyLocation (state t) x = copyLocation (state t) y := by
  obtain ⟨a, hao, han⟩ := h.location x
  obtain ⟨c, hco, hcn⟩ := h.location y
  rw [← hao, ← hco, ← han, ← hcn]
  constructor
  · intro he
    rw [(intoOriginalChildGuarded N hcut b hb hp).injective he]
  · intro he
    rw [boundary_phase_injective N hcut b hb hp he]

theorem phase_code_related {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) :
    Related N hcut b hb hp s (phaseCode N hcut b hb hp s hs) := by
  refine ⟨rfl, rfl, ?_, fun _ => rfl, ?_⟩
  · intro l hl
    exact decode_encode_live_genealogy _ _
      (phase_state_source_valid N hcut b hb hp s hs).forest hl
  · intro x
    refine ⟨ownerPhase N hcut b hb hp s hs x,
      owner_phase_original N hcut b hb hp s hs x, ?_⟩
    change _ = copyLocation (decodeSnapshot _ (encodeSnapshot _ _)) x
    rw [decode_encode_copyLocation, phase_state_copy_location]

/-- Both deterministic ACTUAL ordinary-entry updates satisfy the relation,
using their own child IDs. This is only their boundary PMF (pure) operation;
their succeeding epochs may have entirely different physical laws. -/
theorem actual_child_entry_related {sample : Copy → X} (s : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    Related N hcut b hb hp
      (ordinaryCode N s (derivedBigon N hcut b hb hp).child)
      (ordinaryCode (suppressedNetwork N hcut b hb hp) t (Sum.inr ())) := by
  refine ⟨h.live, h.ancestor, ?_, h.outsideRegister, ?_⟩
  · intro l hl
    have hlt : l ∈ (state t).live := by rw [h.live]; exact hl
    rw [show (state (ordinaryCode (suppressedNetwork N hcut b hb hp) t (Sum.inr ()))).genealogy l =
        (state t).genealogy l from decode_encode_live_genealogy _ _
          (enterEdge_source_valid _ _ _ t.property _).forest hlt,
      show (state (ordinaryCode N s (derivedBigon N hcut b hb hp).child)).genealogy l =
        (state s).genealogy l from decode_encode_live_genealogy _ _
          (enterEdge_source_valid _ _ _ s.property _).forest hl]
    exact h.genealogy l hl
  · intro x
    obtain ⟨q, ho, hn⟩ := h.location x
    refine ⟨childEntryPhase N hcut b hb hp q, ?_, ?_⟩
    · rw [ordinaryCode_copyLocation, ← ho, original_child_entry_phase]
    · rw [ordinaryCode_copyLocation, ← hn, constructed_child_entry_phase]

/-- Every actual initialized original FULL forest through the complete tied
child batch and a true guard gap supplies this admitted boundary relation.
The original entering register is arbitrary here; independence is not inferred.
Natural unused-private-bit independence is a SEPARATE causal product theorem. -/
theorem initialized_guard_has_related_boundary
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (guard : ℝ)
    (hlower : C.age (N.graph.target (derivedBigon N hcut b hb hp).child) ≤ guard)
    (hupper : guard < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (hgap : ∀ v : V, C.age (N.graph.target (derivedBigon N hcut b hb hp).child) < C.age v →
      guard ≤ C.age v)
    {d z w : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (actualFrontierProgram N C H gamma common
        (C.age (N.graph.target (derivedBigon N hcut b hb hp).child)))
      (initialCode N sample register)).support)
    (hz : z ∈ (sourceProgram N r
      ((Finset.univ.filter (fun v : V =>
        C.age v = C.age (N.graph.target (derivedBigon N hcut b hb hp).child))).toList.map
          (fun v => .boundary (originalNodeOperation N H gamma common v))) d).support)
    (hw : w ∈ (sourceTimeKernel N r
      (Real.toNNReal (guard - C.age (N.graph.target (derivedBigon N hcut b hb hp).child))) z).support) :
    ∃ t : Code (suppressedNetwork N hcut b hb hp) sample,
      Related N hcut b hb hp w t := by
  have hs := (actual_initialized_protected_child_phase N hcut b hb hp C sample register
    H gamma common r guard hlower hupper hgap hd hz hw).2.2.2
  exact ⟨phaseCode N hcut b hb hp w hs, phase_code_related N hcut b hb hp w hs⟩

/-- A total deterministic lift is defined outside the supported phase only by
initialization, to make a PMF.map well typed. Unsupported branches are excluded
by the preceding actual support theorem, never used as biological states. -/
noncomputable def phaseLift {sample : Copy → X} (s : Code N sample) :
    Code (suppressedNetwork N hcut b hb hp) sample :=
  if hs : PhaseSupported N hcut b hb hp s then phaseCode N hcut b hb hp s hs
  else initialCode _ sample (fun v => (state s).register v.val)

theorem supported_phase_lift_related {sample : Copy → X} (s : Code N sample)
    (hs : PhaseSupported N hcut b hb hp s) :
    Related N hcut b hb hp s (phaseLift N hcut b hb hp s) := by
  rw [phaseLift, dif_pos hs]
  exact phase_code_related N hcut b hb hp s hs

/-- Actual original prefix, all tied child-date nodes, then the true gap.
The gap ends BEFORE its guard-date batch; no exterior operation is deleted. -/
noncomputable def guardedPhaseProgram (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (guard : ℝ) : List (ProgramStep N) :=
  let a := C.age (N.graph.target (derivedBigon N hcut b hb hp).child)
  actualFrontierProgram N C H gamma common a ++
    ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
      (fun v => .boundary (originalNodeOperation N H gamma common v)) ++
      [.interval (Real.toNNReal (guard - a))])

theorem actual_guarded_program_phase_supported
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (guard : ℝ)
    (hlower : C.age (N.graph.target (derivedBigon N hcut b hb hp).child) ≤ guard)
    (hupper : guard < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (hgap : ∀ v : V, C.age (N.graph.target (derivedBigon N hcut b hb hp).child) < C.age v →
      guard ≤ C.age v)
    {w : Code N sample}
    (hw : w ∈ (sourceProgram N r (guardedPhaseProgram N hcut b hb hp C H gamma common guard)
      (initialCode N sample register)).support) : PhaseSupported N hcut b hb hp w := by
  rw [guardedPhaseProgram, sourceProgram_append] at hw
  obtain ⟨d, hd, htail⟩ := (PMF.mem_support_bind_iff _ _ _).mp hw
  rw [sourceProgram_append] at htail
  obtain ⟨z, hz, htime⟩ := (PMF.mem_support_bind_iff _ _ _).mp htail
  have ht : w ∈ (sourceTimeKernel N r
      (Real.toNNReal (guard - C.age (N.graph.target (derivedBigon N hcut b hb hp).child))) z).support := by
    simpa [sourceProgram, sourceProgramStep] using htime
  exact (actual_initialized_protected_child_phase N hcut b hb hp C sample register
    H gamma common r guard hlower hupper hgap hd hz ht).2.2.2

/-- At the older stop AFTER all its exits / BEFORE its node batch, no removed
private population remains occupied. This follows from physical ready/strict
exit support, not a desired compact-word endpoint field. -/
theorem after_original_entry_exits_phase_supported
    (C : Calendar N.graph) {sample : Copy → X} (s : Code N sample)
    (hs : AfterExits N C
      (C.age (N.graph.source (derivedBigon N hcut b hb hp).entry)) (state s)) :
    PhaseSupported N hcut b hb hp s := by
  let A := derivedBigon N hcut b hb hp
  have ha := boundary_original_private_age_order N hcut b hb hp C
  change C.age (N.graph.target A.child) < C.age A.fragment.parents.hybrid ∧
    C.age A.fragment.parents.hybrid < C.age A.fragment.upper ∧
    C.age A.fragment.upper < C.age (N.graph.source A.entry) at ha
  intro x
  have hr := hs.1 x
  cases hx : copyLocation (state s) x with
  | node v =>
      rw [hx] at hr
      change C.age (N.graph.source A.entry) ≤ C.age v at hr
      have hv : v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid := by
        constructor
        · intro he; rw [he] at hr
          exact (not_le_of_gt ha.2.2) hr
        · intro he; rw [he] at hr
          exact (not_le_of_gt (ha.2.1.trans ha.2.2)) hr
      exact ⟨.node ⟨v, hv⟩, rfl⟩
  | edge e =>
      have hu := hs.2 x e hx
      have he : e ∉ removedEdges N b A := by
        intro hm
        have hm : e = A.entry ∨ e = A.child ∨
            e = A.fragment.parents.parent0 ∨ e = A.fragment.parents.parent1 := by
          simpa only [removedEdges, Finset.mem_insert, Finset.mem_singleton] using hm
        rcases hm with rfl | rfl | rfl | rfl
        · exact (lt_irrefl _) hu
        · rw [A.child_source] at hu
          exact (not_lt_of_ge (ha.2.1.trans ha.2.2).le) hu
        · rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper
            from A.fragment.arm_sources false] at hu
          exact (not_lt_of_ge ha.2.2.le) hu
        · rw [show N.graph.source A.fragment.parents.parent1 = A.fragment.upper
            from A.fragment.arm_sources true] at hu
          exact (not_lt_of_ge ha.2.2.le) hu
      exact ⟨.edge ⟨e, Or.inl he⟩, rfl⟩
  | rootPopulation v =>
      rw [hx] at hr
      change v = N.root ∧ _ at hr
      have hv : v ≠ A.fragment.upper ∧ v ≠ A.fragment.parents.hybrid := by
        rw [hr.1]
        exact actual_root_vertex_retained N b hb A
      exact ⟨.rootPopulation ⟨v, hv⟩, rfl⟩

/-- Keep the ORIGINAL full Code, including private registers, as a coupled
auxiliary, and carry old tags/history literally. This is a derived boundary
pushforward of p, NOT a claim that its second marginal is a new physical law. -/
noncomputable def boundaryCoupling {sample : Copy → X} {History Tags : Type*}
    (p : PMF (Code N sample × History × Tags)) :
    PMF ((Code N sample × Code (suppressedNetwork N hcut b hb hp) sample) × History × Tags) :=
  p.map (fun q => ((q.1, phaseLift N hcut b hb hp q.1), q.2))

theorem boundary_coupling_original_marginal {sample : Copy → X} {History Tags : Type*}
    (p : PMF (Code N sample × History × Tags)) :
    (boundaryCoupling N hcut b hb hp p).map (fun q => (q.1.1, q.2)) = p := by
  rw [boundaryCoupling, PMF.map_comp]
  change p.map id = p
  exact PMF.map_id p

theorem boundary_coupling_related {sample : Copy → X} {History Tags : Type*}
    (p : PMF (Code N sample × History × Tags))
    (hs : ∀ q ∈ p.support, PhaseSupported N hcut b hb hp q.1)
    {q : (Code N sample × Code (suppressedNetwork N hcut b hb hp) sample) × History × Tags}
    (hq : q ∈ (boundaryCoupling N hcut b hb hp p).support) :
    Related N hcut b hb hp q.1.1 q.1.2 := by
  obtain ⟨a, ha, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hq
  subst q
  exact supported_phase_lift_related N hcut b hb hp a.1 (hs a ha)

open MeasureTheory UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.G6.PrivateRegisterErasure
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open CloudG6.NaturalCalendarPastAdmission
open CloudG3.ActualCutJointLaw CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCalendarEndpointHistory CloudG3.CompleteCalendarBinReadout
open UnifiedLean.G6.GuardedCommonSeedFibre

/-- Actual natural product initialization followed by the original guarded
program. This definition samples no new conditional private posterior. -/
noncomputable def naturalGuardPhaseLaw
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (guard : ℝ) : PMF (Code N sample) :=
  (naturalInitialCodeLaw N sample p).bind
    (sourceProgram N r (guardedPhaseProgram N hcut b hb hp C H (originalGamma p) common guard))

/-- The natural coupling is actually CONSTRUCTED from original biological
initialization and chronology. Its second component is a proved admitted
boundary snapshot; physical realization of a new positive word is separate. -/
theorem actual_natural_guard_phase_related
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (guard : ℝ)
    (hlower : C.age (N.graph.target (derivedBigon N hcut b hb hp).child) ≤ guard)
    (hupper : guard < C.age (derivedBigon N hcut b hb hp).fragment.parents.hybrid)
    (hgap : ∀ v : V, C.age (N.graph.target (derivedBigon N hcut b hb hp).child) < C.age v →
      guard ≤ C.age v)
    {w : Code N sample}
    (hw : w ∈ (naturalGuardPhaseLaw N hcut b hb hp C sample H p common r guard).support) :
    Related N hcut b hb hp w (phaseLift N hcut b hb hp w) := by
  obtain ⟨s, hs, hws⟩ := (PMF.mem_support_bind_iff _ _ _).mp hw
  obtain ⟨register, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
  subst s
  exact supported_phase_lift_related N hcut b hb hp w
    (actual_guarded_program_phase_supported N hcut b hb hp C sample register
      H (originalGamma p) common r guard hlower hupper hgap hws)

variable {Tag : Type*} [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

open UnifiedLean.G6.OriginalSpanJointContext
open GProgram.G2.ActualCalendarTrace GProgram.G2.CalendarDecoration

/-- A stopped endpoint/tag receiver with FIXED OLD history is pushed through
the SAME actual original calendar record. Its second Code remains the explicit
boundary lift. Newly generated outside absolute clock chronology is not an
input to this receiver and is still a separate joint-clock gate. G3's assembly
must identify the one-bin stopped row and the new physical positive-word law. -/
theorem actual_stopped_calendar_boundary_pushforward
    {History Obs : Type*} [MeasurableSpace Obs]
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : Code N sample) (M : Copy → Copy → ℝ) (history : History)
    (receive : History →
      (Code N sample × Code (suppressedNetwork N hcut b hb hp) sample) ×
        (Copy → Copy → Tag) → Obs)
    (hmeas : Measurable (fun q : Code N sample × (Copy → Copy → Tag) =>
      receive history ((q.1, phaseLift N hcut b hb hp q.1), q.2))) :
    (spanJointTaggedLaw N hcut b hb hp C H gamma common r bin s M).map
      (fun q => receive history ((q.1, phaseLift N hcut b hb hp q.1), q.2)) =
      (actualCalendarTraceLaw N r (spanWindowOps N hcut b hb hp C H gamma common) s).map
        (fun z => receive history
          ((calendarEnd N (spanWindowOps N hcut b hb hp C H gamma common) s z,
            phaseLift N hcut b hb hp
              (calendarEnd N (spanWindowOps N hcut b hb hp C H gamma common) s z)),
            calendarTags N bin (spanWindowOps N hcut b hb hp C H gamma common) s
              (C.age (N.graph.target (derivedBigon N hcut b hb hp).child))
              (fun x y => bin (M x y)) z)) := by
  exact span_whole_outside_context_readout N hcut b hb hp C H gamma common r bin
    hbin s M history (fun h q => receive h ((q.1, phaseLift N hcut b hb hp q.1), q.2)) hmeas

/-- Transport the DERIVED naturally initialized seed fibres to boundary data.
The seed stays the same copied original bit. The second component is a
deterministic boundary snapshot/tag readout; not a new physical prefix law.
At arbitrary correlated or private-bit-revealing pasts this product is absent. -/
theorem actual_causal_seed_boundary_product
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N (guardOps N C H p common guard pre) (physicalOps N word))
    (hword : wordBinContract N bin word
      (UnifiedLean.Source.SourceCalendarCompatibility.firstOriginalDate N C)) :
    (guardedSeedTaggedLaw N C P sample p r bin hbin
        (guardOps N C H p common guard pre)).map
      (fun a => (a.1, (phaseLift N hcut b hb hp a.2.1, a.2.2))) =
      independentPMF (privateSeedPMF N P p)
        ((outsideGuardLaw N C P sample p r bin hbin
          (guardOps N C H p common guard pre)).map
            (fun q => (phaseLift N hcut b hb hp q.1, q.2))) := by
  rw [actual_guarded_seed_tag_product N C P sample H p common r bin hbin
    guard pre post hprivate hsplit word href hword]
  simp only [independentPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]


#print axioms phase_descends
#print axioms related_current_population_iff
#print axioms actual_child_entry_related
#print axioms owner_phase_current_owner
#print axioms phase_state_source_valid
#print axioms phase_code_related
#print axioms initialized_guard_has_related_boundary
#print axioms actual_guarded_program_phase_supported
#print axioms actual_natural_guard_phase_related
#print axioms after_original_entry_exits_phase_supported
#print axioms boundary_coupling_original_marginal
#print axioms boundary_coupling_related
#print axioms actual_causal_seed_boundary_product
#print axioms actual_stopped_calendar_boundary_pushforward

end UnifiedLean.G6.BoundaryPhaseRelation
