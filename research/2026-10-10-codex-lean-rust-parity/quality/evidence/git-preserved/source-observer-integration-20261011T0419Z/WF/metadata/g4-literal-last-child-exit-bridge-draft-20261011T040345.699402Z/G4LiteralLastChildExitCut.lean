import G1OriginalCalendarDecomposition
import G1SeparatedAgendaSupportCuts
import G1OriginalExitBatchBinding

/-! SOURCE-ONLY UNCOMPILED DRAFT, lean_integration_successor, 2026-10-11.
No target process has checked these scripts. Calibration-to-geometry and the
physical all-prefix/child-input support premises remain explicit obligations. -/
namespace G4LiteralLastChildExitCutDraft
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open G1InitializedFrontierPrefix G1OriginalCalendarDecomposition
open G1CanonicalComponentSegment G1ActualJointProgram G1JointSeparatedSourceGeometry
open G1OriginalExitBatchBinding
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Graph-only witness; its calibration derivation is not supplied. -/
structure RouteMeetingGeometry (N : RootedBinary V E X) (i j : X) (v : V) (ei ej : E) : Prop where
  taxaDistinct : i ≠ j
  childDistinct : ei ≠ ej
  leftSource : N.graph.source ei = v
  rightSource : N.graph.source ej = v
  leftOnEveryPath : ∀ es, EdgePath N.graph N.root (N.leaf i) es → ei ∈ es
  rightOnEveryPath : ∀ es, EdgePath N.graph N.root (N.leaf j) es → ej ∈ es
  commonAncestorAbove : ∀ w, N.graph.DReach w (N.leaf i) →
    N.graph.DReach w (N.leaf j) → N.graph.DReach w v

def BelowMeeting (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) : Location V E → Prop
  | .node w => C.age w < C.age v
  | .edge e => C.age (N.graph.target e) < C.age v
  | .rootPopulation w => C.age w < C.age v

lemma descendant_locations_ne (N : RootedBinary V E X) (C : Calendar N.graph)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    {p q : Location V E} (hi : DescendsTo N p i) (hj : DescendsTo N q j)
    (hyoung : BelowMeeting N C v p) : p ≠ q := by
  intro hpq
  subst q
  cases p with
  | node w =>
      change N.graph.DReach w (N.leaf i) at hi
      change N.graph.DReach w (N.leaf j) at hj
      change C.age w < C.age v at hyoung
      exact (not_lt_of_ge (C.age_le_of_directed (hg.commonAncestorAbove w hi hj))) hyoung
  | edge e =>
      change N.graph.DReach (N.graph.target e) (N.leaf i) at hi
      change N.graph.DReach (N.graph.target e) (N.leaf j) at hj
      change C.age (N.graph.target e) < C.age v at hyoung
      exact (not_lt_of_ge (C.age_le_of_directed
        (hg.commonAncestorAbove (N.graph.target e) hi hj))) hyoung
  | rootPopulation w =>
      change w = N.root ∧ N.graph.DReach w (N.leaf i) at hi
      change w = N.root ∧ N.graph.DReach w (N.leaf j) at hj
      change C.age w < C.age v at hyoung
      exact (not_lt_of_ge (C.age_le_of_directed
        (hg.commonAncestorAbove w hi.2 hj.2))) hyoung

/-- Original-copy ancestry already holds through all legal current-root mergers. -/
lemma source_separated_of_below_meeting (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {i j : X} {v : V} {ei ej : E}
    (hg : RouteMeetingGeometry N i j v ei ej) (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i) (houtside : ∀ y ∈ outside, sample y = j)
    (s : Code N sample)
    (hyoung : ∀ x ∈ inside, BelowMeeting N C v (copyLocation (state s) x)) :
    PopulationSeparated (state s) inside outside := by
  intro x hx y hy
  apply descendant_locations_ne N C hg
  · simpa only [hinside x hx] using s.property.original_descendant x
  · simpa only [houtside y hy] using s.property.original_descendant y
  · exact hyoung x hx

/-- First indices in the compiler's unchanged original exit list. -/
noncomputable def lastChildCutLength (N : RootedBinary V E X) (C : Calendar N.graph)
    (v : V) (ei ej : E) : Nat :=
  max ((originalExits N C (C.age v)).idxOf ei)
      ((originalExits N C (C.age v)).idxOf ej) + 1

noncomputable def literalPrefix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (ei ej : E) : List (ProgramStep N) :=
  beforeBoundaryProgram N C H gamma common (C.age v) ++
    ((originalExits N C (C.age v)).take (lastChildCutLength N C v ei ej)).map
      (fun e => .boundary (.exit e))

noncomputable def literalSuffix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (ei ej : E) : List (ProgramStep N) :=
  ((originalExits N C (C.age v)).drop (lastChildCutLength N C v ei ej)).map
      (fun e => .boundary (.exit e)) ++
    nodeOperations N C H gamma common (C.age v) ++
    calendarTail N C H gamma common (C.age v)
      ((sortedOriginalDates N C).filter (fun a => decide (C.age v < a)))

/-- Pure list identity. Last-child interpretation additionally needs child membership. -/
theorem literal_calendar_cut (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (ei ej : E) :
    compiledCalendarProgram N C H gamma common =
      literalPrefix N C H gamma common v ei ej ++ literalSuffix N C H gamma common v ei ej := by
  let es := originalExits N C (C.age v)
  let k := lastChildCutLength N C v ei ej
  have hex : es.map (fun e => (ProgramStep.boundary (.exit e) : ProgramStep N)) =
      (es.take k).map (fun e => .boundary (.exit e)) ++
      (es.drop k).map (fun e => .boundary (.exit e)) := by
    simpa only [List.map_append] using
      (congrArg (fun l : List E => l.map (fun e =>
        (ProgramStep.boundary (.exit e) : ProgramStep N))) (List.take_append_drop k es)).symm
  rw [actual_compiled_calendar_date_cut N C H gamma common (C.age v)
    (original_date_scheduled N C v)]
  change (beforeBoundaryProgram N C H gamma common (C.age v) ++
    (es.map (fun e => .boundary (.exit e)) ++ nodeOperations N C H gamma common (C.age v))) ++
    calendarTail N C H gamma common (C.age v)
      ((sortedOriginalDates N C).filter (fun a => decide (C.age v < a))) = _
  rw [hex]
  simp only [literalPrefix, literalSuffix, List.append_assoc]

lemma child_mem_exits (N : RootedBinary V E X) (C : Calendar N.graph)
    (v : V) (e : E) (hsource : N.graph.source e = v) :
    e ∈ originalExits N C (C.age v) := by
  apply Finset.mem_toList.mpr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hsource]⟩

lemma member_take_of_idx_lt {es : List E} {e : E} {k : Nat}
    (he : e ∈ es) (hk : es.idxOf e < k) : e ∈ es.take k := by
  have hlen := List.idxOf_lt_length_of_mem he
  exact List.mem_take_iff_getElem.mpr ⟨es.idxOf e, lt_min hk hlen, List.getElem_idxOf hlen⟩

lemma last_child_cut_members (N : RootedBinary V E X) (C : Calendar N.graph)
    (v : V) (ei ej : E) (hi : N.graph.source ei = v) (hj : N.graph.source ej = v) :
    ei ∈ (originalExits N C (C.age v)).take (lastChildCutLength N C v ei ej) ∧
    ej ∈ (originalExits N C (C.age v)).take (lastChildCutLength N C v ei ej) := by
  constructor
  · apply member_take_of_idx_lt (child_mem_exits N C v ei hi)
    exact Nat.lt_succ_of_le (le_max_left _ _)
  · apply member_take_of_idx_lt (child_mem_exits N C v ej hj)
    exact Nat.lt_succ_of_le (le_max_right _ _)

lemma last_child_cut_le_length (N : RootedBinary V E X) (C : Calendar N.graph)
    (v : V) (ei ej : E) (hi : N.graph.source ei = v) (hj : N.graph.source ej = v) :
    lastChildCutLength N C v ei ej ≤ (originalExits N C (C.age v)).length := by
  apply Nat.succ_le_of_lt
  exact max_lt_iff.mpr ⟨List.idxOf_lt_length_of_mem (child_mem_exits N C v ei hi),
    List.idxOf_lt_length_of_mem (child_mem_exits N C v ej hj)⟩

/-- Only pre-operation states: the terminal state may already meet at v. -/
def SupportedSeparatedPrefixes (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample) : Prop :=
  ∀ k, k < ops.length → ∀ d ∈ (sourceProgram N r (ops.take k) s).support,
    PopulationSeparated (state d) inside outside

/-- Support bookkeeping; existing selected full-view factorization is reused. -/
theorem agenda_of_supported_prefixes (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (inside outside : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample)
    (h : SupportedSeparatedPrefixes N r inside outside ops s) :
    SeparatedAgenda N r inside outside ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
      refine ⟨h 0 (by simp) s (by simp [sourceProgram]), ?_⟩
      intro d hd
      apply ih
      intro k hk z hz
      have hfull : z ∈ (sourceProgram N r ((op :: ops).take (k + 1)) s).support := by
        change z ∈ ((sourceProgramStep N r op s).bind
          (sourceProgram N r (ops.take k))).support
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨d, hd, hz⟩
      exact h (k + 1) (Nat.succ_lt_succ hk) z hfull

/-- Conditional terminal location; physical child-input support is still explicit. -/
theorem last_child_exit_colocates (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (v : V) (ei ej : E)
    (hi : N.graph.source ei = v) (hj : N.graph.source ej = v)
    (inside outside : Finset Copy) (s d : Code N sample)
    (hleft : ∀ x ∈ inside, copyLocation (state s) x = .edge ei)
    (hright : ∀ y ∈ outside, copyLocation (state s) y = .edge ej)
    (hd : d ∈ (sourceProgram N r
      (((originalExits N C (C.age v)).take (lastChildCutLength N C v ei ej)).map
        (fun e => .boundary (.exit e))) s).support) :
    ∀ x ∈ inside ∪ outside, copyLocation (state d) x = .node v := by
  rw [actual_exit_list_program] at hd
  obtain rfl := PMF.mem_support_pure_iff.mp hd
  have hm := last_child_cut_members N C v ei ej hi hj
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rw [actual_exit_list_copy_location, hleft x hx,
      actual_exit_location_list_hit N _ ei hm.1, hi]
  · rw [actual_exit_list_copy_location, hright x hx,
      actual_exit_location_list_hit N _ ej hm.2, hj]
end G4LiteralLastChildExitCutDraft
