import G5StrictBoundaryRoutes
import G5SafeCommonGroupSelector
import G5OlderSideCutChart
import G1InitializedFrontierPrefix
import G5ActualProtectiveOccupancy

/-!
# Actual fixed-register prefix for the full G5 support consumer

Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. This is the source-routing part of the named full M3
consumer, not a new terminal identification claim. It keeps one initial
original register and realizes that same choice at every independent pulse
as a positive legal history. The same-selector path invariant and actual initialized physical prefix
are derived below. The terminal witness connects all safe simultaneous current
choices to positive actual posterior support. Compilation is still pending.
-/
namespace GProgram.G5.SafePrefixRouteBridge
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCrossCarrierEpoch
open GProgram.G5.StrictBoundaryRoutes GProgram.G5.ActualRoutingSupport
open GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.ActualActivatedPrefix GProgram.G5.ActivatedPosteriorPlacement
open GProgram.G5.OriginalEpochChart GProgram.G5.PhysicalCutChart
open GProgram.G5.OlderSideCutChart
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.NativeCurrentPortCompiler
open GProgram.G5.EnumeratedPosteriorGerm GProgram.G5.ActualProtectiveOccupancy
open GProgram.G5.OriginalCoinLaw
open UnifiedLean.Source.SourceForestSilentPruning
open G1InitializedFrontierPrefix GProgram.G5.NonbridgeRoutes
open UnifiedLean.Source.SourceBoundaryLocations
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- At an independent pulse, choose the existing original-register bit for
all CURRENT owners. This particular allowed coin assignment is not a claim
that independent routing has the COMMON probability law. -/
noncomputable def fixedRegisterBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) : Code N sample :=
  match b with
  | .exit e => exitCode N s e
  | .ordinary e _ => ordinaryCode N s e
  | .root => rootCode N s
  | .common H => pulseCode H s (fun _ => (state s).register H.hybrid)
  | .independent H _ => pulseCode H s (fun _ => (state s).register H.hybrid)

lemma fixedRegisterBoundary_legal (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) :
    LegalBoundaryRoute N b s (fixedRegisterBoundary N b s) := by
  cases b with
  | exit e => rfl
  | ordinary e degree => rfl
  | root => rfl
  | common H => rfl
  | independent H gamma => exact ⟨fun _ => (state s).register H.hybrid,rfl⟩

/-- The same actual source boundary operations, with no mergers during the
finite intervals. No new graph, fitted state, or stagewise register is used. -/
noncomputable def fixedRegisterPrefix (N : RootedBinary V E X) {sample : Copy → X} :
    List (ProgramStep N) → Code N sample → Code N sample
  | [],s => s
  | .interval _ :: ops,s => fixedRegisterPrefix N ops s
  | .boundary b :: ops,s => fixedRegisterPrefix N ops (fixedRegisterBoundary N b s)

lemma fixedRegisterPrefix_legal (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    LegalRoute N ops s (fixedRegisterPrefix N ops s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | interval duration => exact ih s
      | boundary b =>
          exact ⟨fixedRegisterBoundary N b s,fixedRegisterBoundary_legal N b s,
            ih (fixedRegisterBoundary N b s)⟩

/-- Every fixed original-register route through an ACTUAL compiled prefix has
positive no-selected-merger posterior support. The source itself supplies
strictness, finite survival and support equivalence. This applies to both
routing mechanisms, with the original bank unchanged. -/
theorem fixed_register_actual_prefix_posterior_support
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (past future : List (ProgramStep N))
    (hprefix : compiledCalendarProgram N C H (originalGamma p) common = past ++ future)
    (coin : Hybrid N → Bool) :
    joinedProjection N Finset.univ (.inl (fixedRegisterPrefix N past
      (initialCode N sample (originalRegister N coin)))) ∈
      (originalFullPosterior N sample p r Finset.univ past).support := by
  have hstrict : StrictWord N (past ++ future) := by
    rw [← hprefix]
    exact actual_compiled_calendar_strict N C H p common
  have hpast := ((strict_word_append N past future).mp hstrict).1
  exact (actual_posterior_support_iff_seeds N sample p r past hpast _).mpr
    ⟨coin, fixedRegisterPrefix N past (initialCode N sample (originalRegister N coin)),
      fixedRegisterPrefix_legal N past _,rfl⟩

noncomputable def fixedBoundaryLocation (N : RootedBinary V E X)
    (b : BoundaryOperation N) (reg : V → Bool) (p : Location V E) : Location V E :=
  match b with
  | .exit e => exitLocation N e p
  | .ordinary e _ => ordinaryLocation N e p
  | .root => rootLocation N p
  | .common H => if p = .node H.hybrid then .edge (H.parent (reg H.hybrid)) else p
  | .independent H _ => if p = .node H.hybrid then .edge (H.parent (reg H.hybrid)) else p

/-- Finite Code recoding preserves the actual copy's current owner and
location; the deterministic prefix follows exactly its original boundary. -/
lemma fixedRegisterBoundary_copyLocation
    (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) (x : Copy) :
    copyLocation (state (fixedRegisterBoundary N b s)) x =
      fixedBoundaryLocation N b (state s).register (copyLocation (state s) x) := by
  cases b with
  | exit e => exact exitCode_copyLocation N s e x
  | ordinary e degree => exact ordinaryCode_copyLocation N s e x
  | root => exact rootCode_copyLocation N s x
  | common H =>
      have hloc : copyLocation (state (pulseCode H s (fun _ => (state s).register H.hybrid))) x =
          copyLocation (pulse H (state s) (fun _ => (state s).register H.hybrid)) x := by
        apply Option.some.inj
        simpa only [UnifiedLean.Source.SourceForestSilentPruning.selectedView,
          UnifiedLean.Source.SourceForestSilentPruning.selectedLocation,Finset.mem_univ,if_true] using
          congrArg (fun v => v.population x)
            (pulseCode_view H s Finset.univ (fun _ => (state s).register H.hybrid))
      change copyLocation (state (pulseCode H s _)) x = _
      rw [hloc]
      have hxlive : (state s).ancestor x ∈ (state s).live :=
        s.property.forest.ancestor_live x
      simp only [fixedBoundaryLocation,pulse,transport,copyLocation]
      simp only [hxlive,true_and]
      by_cases hnode : (state s).location ((state s).ancestor x) = .node H.hybrid <;>
        simp [hnode]
  | independent H gamma =>
      have hloc : copyLocation (state (pulseCode H s (fun _ => (state s).register H.hybrid))) x =
          copyLocation (pulse H (state s) (fun _ => (state s).register H.hybrid)) x := by
        apply Option.some.inj
        simpa only [UnifiedLean.Source.SourceForestSilentPruning.selectedView,
          UnifiedLean.Source.SourceForestSilentPruning.selectedLocation,Finset.mem_univ,if_true] using
          congrArg (fun v => v.population x)
            (pulseCode_view H s Finset.univ (fun _ => (state s).register H.hybrid))
      change copyLocation (state (pulseCode H s _)) x = _
      rw [hloc]
      have hxlive : (state s).ancestor x ∈ (state s).live :=
        s.property.forest.ancestor_live x
      simp only [fixedBoundaryLocation,pulse,transport,copyLocation]
      simp only [hxlive,true_and]
      by_cases hnode : (state s).location ((state s).ancestor x) = .node H.hybrid <;>
        simp [hnode]

/-- Register retention is a deterministic property of the actual Code
operations, including the selected independent witness. -/
lemma fixedRegisterBoundary_register (N : RootedBinary V E X) {sample : Copy → X}
    (b : BoundaryOperation N) (s : Code N sample) :
    (state (fixedRegisterBoundary N b s)).register = (state s).register := by
  cases b <;> rfl

lemma fixedRegisterPrefix_register (N : RootedBinary V E X) {sample : Copy → X}
    (ops : List (ProgramStep N)) (s : Code N sample) :
    (state (fixedRegisterPrefix N ops s)).register = (state s).register := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | interval duration => exact ih s
      | boundary b =>
          exact (ih (fixedRegisterBoundary N b s)).trans
            (fixedRegisterBoundary_register N b s)

/-- A younger route suffix remembers the SAME selector, rather than only
ordinary reachability. This is the intended invariant at pending nodes. -/
def SelectedSuffix (N : RootedBinary V E X) (P : IncomingSelector N)
    (x : X) (v : V) : Prop :=
  ∃ es : List E, EdgePath N.graph v (N.leaf x) es ∧ RespectsSelector N P es

/-- Edge positions additionally record that this exact incoming occurrence
is selected. Parallel original edges remain distinct. -/
def SelectorLocation (N : RootedBinary V E X) (P : IncomingSelector N)
    (x : X) : Location V E → Prop
  | .node v => SelectedSuffix N P x v
  | .edge e =>
      (∃ h : N.graph.target e ≠ N.root, P.edge ⟨N.graph.target e,h⟩ = e) ∧
        SelectedSuffix N P x (N.graph.target e)
  | .rootPopulation v => v = N.root

lemma selected_suffix_tip (N : RootedBinary V E X) (P : IncomingSelector N) (x : X) :
    SelectedSuffix N P x (N.leaf x) := by
  refine ⟨[],EdgePath.nil _,?_⟩
  intro e he
  exact False.elim (List.not_mem_nil he)

lemma selected_suffix_prepend (N : RootedBinary V E X) (P : IncomingSelector N)
    (x : X) (e : E)
    (he : ∃ h : N.graph.target e ≠ N.root, P.edge ⟨N.graph.target e,h⟩ = e)
    (hs : SelectedSuffix N P x (N.graph.target e)) :
    SelectedSuffix N P x (N.graph.source e) := by
  obtain ⟨es,hpath,hrespect⟩ := hs
  refine ⟨e :: es,EdgePath.cons rfl hpath,?_⟩
  intro f hf
  rcases List.mem_cons.mp hf with hf | hf
  · subst f; exact he
  · exact hrespect f hf

lemma selectorLocation_exit (N : RootedBinary V E X) (P : IncomingSelector N)
    (x : X) (e : E) (p : Location V E) (hp : SelectorLocation N P x p) :
    SelectorLocation N P x (exitLocation N e p) := by
  by_cases he : p = .edge e
  · subst p
    simp only [exitLocation,if_pos rfl]
    exact selected_suffix_prepend N P x e hp.1 hp.2
  · simpa only [exitLocation,if_neg he] using hp

lemma selectorLocation_entry (N : RootedBinary V E X) (P : IncomingSelector N)
    (x : X) (e : E) (p : Location V E)
    (he : ∃ h : N.graph.target e ≠ N.root, P.edge ⟨N.graph.target e,h⟩ = e)
    (hp : SelectorLocation N P x p) :
    SelectorLocation N P x (ordinaryLocation N e p) := by
  by_cases ht : p = .node (N.graph.target e)
  · subst p
    simp only [ordinaryLocation,if_pos rfl]
    exact ⟨he,hp⟩
  · simpa only [ordinaryLocation,if_neg ht] using hp

lemma selectorLocation_root (N : RootedBinary V E X) (P : IncomingSelector N)
    (x : X) (p : Location V E) (hp : SelectorLocation N P x p) :
    SelectorLocation N P x (rootLocation N p) := by
  by_cases hr : p = .node N.root
  · simp only [rootLocation,if_pos hr]
    rfl
  · simpa only [rootLocation,if_neg hr] using hp

/-- A selected younger suffix extends through the source's actual compiled
older path. Uniqueness for the SAME incoming selector identifies the result
with compiledRoute, without a caller-supplied route-coverage assumption. -/
theorem selectorLocation_edge_mem_compiled
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (P : IncomingSelector N) (x : X) (e : E)
    (hp : SelectorLocation N P x (.edge e)) :
    e ∈ compiledRoute N C P (N.leaf x) := by
  obtain ⟨hes,es,hpath,hrespect⟩ := hp
  let pre := compiledRoute N C P (N.graph.source e)
  have hpre := compiledRoute_source_spec N C P (N.graph.source e)
  have hfull : EdgePath N.graph N.root (N.leaf x) (pre ++ e :: es) :=
    hpre.1.append (EdgePath.cons rfl hpath)
  have hsel : RespectsSelector N P (pre ++ e :: es) := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hpre.2 f hf
    · rcases List.mem_cons.mp hf with hf | hf
      · subst f; exact hes
      · exact hrespect f hf
  have hc := compiledRoute_source_spec N C P (N.leaf x)
  have heq : compiledRoute N C P (N.leaf x) = pre ++ e :: es := by
    apply List.reverse_inj.mp
    exact GProgram.G5.AttainedChronology.UpPath.eq_of_same_selector N P
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hc.1 (fun _ _ => trivial))
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hfull (fun _ _ => trivial))
      (GProgram.G5.AttainedChronology.respectsSelector_reverse N P hc.2)
      (GProgram.G5.AttainedChronology.respectsSelector_reverse N P hsel)
  rw [heq]
  exact List.mem_append.mpr (Or.inr List.mem_cons_self)

def BoundaryAgrees (N : RootedBinary V E X) (P : IncomingSelector N)
    (reg : V → Bool) : BoundaryOperation N → Prop
  | .exit _ => True
  | .ordinary e _ => ∃ h : N.graph.target e ≠ N.root, P.edge ⟨N.graph.target e,h⟩ = e
  | .root => True
  | .common H => ∃ h : N.graph.target (H.parent (reg H.hybrid)) ≠ N.root,
      P.edge ⟨N.graph.target (H.parent (reg H.hybrid)),h⟩ = H.parent (reg H.hybrid)
  | .independent H _ => ∃ h : N.graph.target (H.parent (reg H.hybrid)) ≠ N.root,
      P.edge ⟨N.graph.target (H.parent (reg H.hybrid)),h⟩ = H.parent (reg H.hybrid)

lemma fixedBoundaryLocation_preserves_selector
    (N : RootedBinary V E X) (P : IncomingSelector N) (reg : V → Bool)
    (b : BoundaryOperation N) (hb : BoundaryAgrees N P reg b)
    (x : X) (loc : Location V E) (hl : SelectorLocation N P x loc) :
    SelectorLocation N P x (fixedBoundaryLocation N b reg loc) := by
  cases b with
  | exit e => exact selectorLocation_exit N P x e loc hl
  | ordinary e degree => exact selectorLocation_entry N P x e loc hb hl
  | root => exact selectorLocation_root N P x loc hl
  | common H =>
      have ht : N.graph.target (H.parent (reg H.hybrid)) = H.hybrid := by
        cases reg H.hybrid <;> simp [GProgram.G2.OriginalHybridParents.parent,H.target0,H.target1]
      simpa only [fixedBoundaryLocation,ordinaryLocation,ht] using
        selectorLocation_entry N P x (H.parent (reg H.hybrid)) loc hb hl
  | independent H gamma =>
      have ht : N.graph.target (H.parent (reg H.hybrid)) = H.hybrid := by
        cases reg H.hybrid <;> simp [GProgram.G2.OriginalHybridParents.parent,H.target0,H.target1]
      simpa only [fixedBoundaryLocation,ordinaryLocation,ht] using
        selectorLocation_entry N P x (H.parent (reg H.hybrid)) loc hb hl

def WordAgrees (N : RootedBinary V E X) (P : IncomingSelector N) (reg : V → Bool) :
    List (ProgramStep N) → Prop
  | [] => True
  | .interval _ :: ops => WordAgrees N P reg ops
  | .boundary b :: ops => BoundaryAgrees N P reg b ∧ WordAgrees N P reg ops

lemma wordAgrees_append (N : RootedBinary V E X) (P : IncomingSelector N)
    (reg : V → Bool) (xs ys : List (ProgramStep N)) :
    WordAgrees N P reg (xs ++ ys) ↔ WordAgrees N P reg xs ∧ WordAgrees N P reg ys := by
  induction xs with
  | nil => simp [WordAgrees]
  | cons x xs ih => cases x <;> simp [WordAgrees,ih,and_assoc]

/-- One invariant for the whole actual prefix. The selector and register are
fixed before the induction; neither is reselected at a stage or a pulse. -/
theorem fixedRegisterPrefix_preserves_selector
    (N : RootedBinary V E X) {sample : Copy → X} (P : IncomingSelector N)
    (reg : V → Bool) (ops : List (ProgramStep N))
    (hops : WordAgrees N P reg ops) (s : Code N sample)
    (hreg : (state s).register = reg)
    (hloc : ∀ x, SelectorLocation N P (sample x) (copyLocation (state s) x)) :
    ∀ x, SelectorLocation N P (sample x)
      (copyLocation (state (fixedRegisterPrefix N ops s)) x) := by
  induction ops generalizing s with
  | nil => exact hloc
  | cons op ops ih =>
      cases op with
      | interval duration => exact ih hops s hreg hloc
      | boundary b =>
          apply ih hops.2 (fixedRegisterBoundary N b s)
          · exact (fixedRegisterBoundary_register N b s).trans hreg
          · intro x
            rw [fixedRegisterBoundary_copyLocation,hreg]
            exact fixedBoundaryLocation_preserves_selector N P reg b hops.1 (sample x) _ (hloc x)

lemma original_parent_agrees (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (coin : Hybrid N → Bool) (hy : Hybrid N) :
    ∃ h : N.graph.target ((H.parents hy).parent (coin hy)) ≠ N.root,
      (coinSelector N H coin).edge ⟨N.graph.target ((H.parents hy).parent (coin hy)),h⟩ =
        (H.parents hy).parent (coin hy) := by
  have hn := GProgram.G5.AttainedChronology.original_edge_target_not_root N
    ((H.parents hy).parent (coin hy))
  have hv : hy.val ≠ N.root := by
    simpa only [registry_parent_target] using hn
  have he : (coinSelector N H coin).edge ⟨hy.val,hv⟩ =
      (H.parents hy).parent (coin hy) := by simp [coinSelector,hy.property]
  have hs := selector_edge_respects N (coinSelector N H coin) ⟨hy.val,hv⟩
    ((coinSelector N H coin).edge ⟨hy.val,hv⟩) List.mem_cons_self
  simpa only [he] using hs

lemma actual_node_agrees (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (coin : Hybrid N → Bool) (v : V) :
    BoundaryAgrees N (coinSelector N H coin) (originalRegister N coin)
      (originalNodeOperation N H gamma common v) := by
  rcases original_node_is_actual_operation N H gamma common v with hr | hh | ho
  · rw [hr.1]; trivial
  · obtain ⟨hy,hv,hsite,hcommon | hindependent⟩ := hh
    · rw [hcommon]
      change ∃ h : N.graph.target ((H.parents hy).parent
        (originalRegister N coin (H.parents hy).hybrid)) ≠ N.root, _
      simpa [originalRegister,H.original_site,hy.property] using original_parent_agrees N H coin hy
    · rw [hindependent]
      change ∃ h : N.graph.target ((H.parents hy).parent
        (originalRegister N coin (H.parents hy).hybrid)) ≠ N.root, _
      simpa [originalRegister,H.original_site,hy.property] using original_parent_agrees N H coin hy
  · obtain ⟨e,ht,hd,he⟩ := ho
    rw [he]
    let hn := GProgram.G5.AttainedChronology.original_edge_target_not_root N e
    refine ⟨hn,?_⟩
    exact incoming_equal_of_indegree_le_one N (by rw [hd])
      ((coinSelector N H coin).target ⟨N.graph.target e,hn⟩) rfl

lemma wordAgrees_boundary_map (N : RootedBinary V E X) (P : IncomingSelector N)
    (reg : V → Bool) {A : Type*} (f : A → BoundaryOperation N)
    (hf : ∀ a, BoundaryAgrees N P reg (f a)) (xs : List A) :
    WordAgrees N P reg (xs.map (fun a => ProgramStep.boundary (f a))) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨hf x,ih⟩

lemma actual_batch_agrees (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (coin : Hybrid N → Bool) (a : ℝ) :
    WordAgrees N (coinSelector N H coin) (originalRegister N coin)
      (boundaryOperations N C H gamma common a) := by
  unfold boundaryOperations
  apply (wordAgrees_append N _ _ _ _).mpr
  exact ⟨wordAgrees_boundary_map N _ _ (fun e => .exit e) (fun _ => trivial) _,
    wordAgrees_boundary_map N _ _ _ (actual_node_agrees N H gamma common coin) _⟩

lemma actual_calendar_tail_agrees (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (coin : Hybrid N → Bool) (a : ℝ) (dates : List ℝ) :
    WordAgrees N (coinSelector N H coin) (originalRegister N coin)
      (calendarTail N C H gamma common a dates) := by
  induction dates generalizing a with
  | nil => trivial
  | cons b dates ih =>
      change WordAgrees N _ _ (boundaryOperations N C H gamma common b ++
        calendarTail N C H gamma common b dates)
      exact (wordAgrees_append N _ _ _ _).mpr ⟨actual_batch_agrees N C H gamma common coin b,ih b⟩

lemma actual_compiled_word_agrees (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (coin : Hybrid N → Bool) :
    WordAgrees N (coinSelector N H coin) (originalRegister N coin)
      (compiledCalendarProgram N C H gamma common) := by
  unfold compiledCalendarProgram
  cases sortedOriginalDates N C with
  | nil => trivial
  | cons a dates =>
      exact (wordAgrees_append N _ _ _ _).mpr
        ⟨actual_batch_agrees N C H gamma common coin a,
          actual_calendar_tail_agrees N C H gamma common coin a dates⟩

/-- Source-native path invariant for the actual compiled prefix. At this
stage no probability law or desired geometric readout is an input premise. -/
theorem actual_prefix_follows_same_original_selector
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (coin : Hybrid N → Bool)
    (past future : List (ProgramStep N))
    (hprefix : compiledCalendarProgram N C H gamma common = past ++ future) :
    ∀ x, SelectorLocation N (coinSelector N H coin) (sample x)
      (copyLocation (state (fixedRegisterPrefix N past
        (initialCode N sample (originalRegister N coin)))) x) := by
  have hword : WordAgrees N (coinSelector N H coin) (originalRegister N coin) (past ++ future) := by
    rw [← hprefix]
    exact actual_compiled_word_agrees N C H gamma common coin
  apply fixedRegisterPrefix_preserves_selector N (coinSelector N H coin) (originalRegister N coin)
    past ((wordAgrees_append N _ _ past future).mp hword).1 _ rfl
  intro x
  have hloc : copyLocation (state (initialCode N sample (originalRegister N coin))) x =
      .node (N.leaf (sample x)) := by
    exact UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_copyLocation N.root
      (initial N sample (originalRegister N coin))
      (initial_source_valid N sample (originalRegister N coin)).forest x
  rw [hloc]
  exact selected_suffix_tip N (coinSelector N H coin) (sample x)


lemma fixedRegisterPrefix_append (N : RootedBinary V E X) {sample : Copy → X}
    (xs ys : List (ProgramStep N)) (s : Code N sample) :
    fixedRegisterPrefix N (xs ++ ys) s =
      fixedRegisterPrefix N ys (fixedRegisterPrefix N xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons op xs ih => cases op <;> exact ih _

lemma stopped_tail_through (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (pre post : List ℝ) (guard a : ℝ)
    (hpre : ∀ b ∈ pre, b ≠ guard) :
    stopBeforeTail N C H gamma common guard a (pre ++ guard :: post) ++
      boundaryOperations N C H gamma common guard =
        calendarTail N C H gamma common a (pre ++ [guard]) := by
  induction pre generalizing a with
  | nil => simp [stopBeforeTail,calendarTail]
  | cons b pre ih =>
      have hb := hpre b (by simp)
      have ht := ih b (fun c hc => hpre c (by simp [hc]))
      simpa only [List.cons_append,stopBeforeTail,if_neg hb,calendarTail,
        List.append_assoc] using congrArg
          (fun tail => ProgramStep.interval (Real.toNNReal (b-a)) ::
            (boundaryOperations N C H gamma common b ++ tail)) ht

/-- The G5 chart's after-batch prefix is literally the earlier accepted G1
naturally initialized before-batch prefix followed by the entire tied batch. -/
lemma prefixThrough_eq_before_batch (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (pre post : List ℝ) (guard : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    prefixThrough N C H gamma common pre guard =
      beforeBoundaryProgram N C H gamma common guard ++
        boundaryOperations N C H gamma common guard := by
  have ho : (pre ++ guard :: post).Pairwise (· < ·) := by
    rw [← hsplit]; exact original_dates_strict N C
  have hb : ∀ b ∈ pre, b < guard := fun b h =>
    (List.pairwise_append.mp ho).2.2 b h guard (by simp)
  cases pre with
  | nil => simp [prefixThrough,beforeBoundaryProgram,hsplit,calendarTail]
  | cons a pre =>
      have ha : a ≠ guard := ne_of_lt (hb a (by simp))
      have ht := stopped_tail_through N C H gamma common pre post guard a
        (fun b h => ne_of_lt (hb b (by simp [h])))
      simpa only [prefixThrough,List.cons_append,beforeBoundaryProgram,hsplit,
        if_neg ha,List.append_assoc] using
        (congrArg (fun tail => boundaryOperations N C H gamma common a ++ tail) ht).symm

lemma original_adjacent_gap (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    ∀ v : V, guard < C.age v → next ≤ C.age v := by
  have ho : (pre ++ guard :: next :: post).Pairwise (· < ·) := by
    rw [← hsplit]; exact original_dates_strict N C
  have hb : ∀ b ∈ pre, b < guard := fun b h =>
    (List.pairwise_append.mp ho).2.2 b h guard (by simp)
  have hn := List.pairwise_cons.mp (List.pairwise_cons.mp (List.pairwise_append.mp ho).2.1).2
  intro v hv
  have hm := original_date_scheduled N C v
  rw [hsplit] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact False.elim (lt_asymm hv (hb _ hm))
  · rcases List.mem_cons.mp hm with he | hm
    · exact False.elim ((ne_of_gt hv) he)
    · rcases List.mem_cons.mp hm with he | hm
      · exact he.ge
      · exact (hn.1 _ hm).le

/-- Physical epoch compatibility is DERIVED from the same actual initialized
prefix and source support. It is not an admission field of the consumer. -/
theorem actual_prefix_epoch_compatible (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List ℝ) (guard next : ℝ) (elapsed : ℝ≥0)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (d : Code N sample)
    (hd : d ∈ (sourceProgram N r
      (prefixThrough N C H gamma common pre guard ++ [.interval elapsed])
        (initialCode N sample register)).support) :
    EpochCompatible N C guard next (state d) := by
  rw [prefixThrough_eq_before_batch N C H gamma common pre (next :: post) guard hsplit,
    List.append_assoc,sourceProgram_append] at hd
  obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hg : guard ∈ sortedOriginalDates N C := by rw [hsplit]; simp
  have hzready := actual_initialized_before_boundary_support N C sample register H gamma common r guard hg hz
  rw [sourceProgram_append] at hdz
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdz
  have hmphysical := actual_original_boundary_batch_support N C H gamma common r guard z hzready.1 hm
  have hmepoch := after_nodes_to_epoch N C hmphysical (original_adjacent_gap N C pre post guard next hsplit)
  apply actual_source_time_epoch_support N C r elapsed m hmepoch
  simpa only [sourceProgram,sourceProgramStep,PMF.bind_pure] using hdm

/-- The physical chart splits a real interval. Its past is deliberately not
misidentified with a literal list prefix of the unsplit compiler word. -/
lemma actual_cut_word_strict (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (pre post : List ℝ) (guard next : ℝ) (elapsed : ℝ≥0)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    StrictWord N (prefixThrough N C H (originalGamma p) common pre guard ++ [.interval elapsed]) := by
  have hw := actual_original_epoch_word N C H (originalGamma p) common pre guard next post hsplit
  have hs := actual_compiled_calendar_strict N C H p common
  rw [hw] at hs
  exact (strict_word_append N _ _).mpr
    ⟨((strict_word_append N _ _).mp hs).1,by trivial⟩

/-- Actual initialized positive support of the chosen register's no-merger
Code endpoint, with physical compatibility and path membership discharged. -/
theorem actual_fixed_cut_source_geometry (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List ℝ) (guard next : ℝ) (elapsed : ℝ≥0)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (coin : Hybrid N → Bool) :
    let past := prefixThrough N C H (originalGamma p) common pre guard ++ [.interval elapsed]
    let d := fixedRegisterPrefix N past (initialCode N sample (originalRegister N coin))
    d ∈ (sourceProgram N r past (initialCode N sample (originalRegister N coin))).support ∧
      EpochCompatible N C guard next (state d) ∧
      ∀ x, SelectorLocation N (coinSelector N H coin) (sample x) (copyLocation (state d) x) := by
  dsimp only
  let past := prefixThrough N C H (originalGamma p) common pre guard ++ [.interval elapsed]
  let d := fixedRegisterPrefix N past (initialCode N sample (originalRegister N coin))
  have hs := actual_cut_word_strict N C H p common pre post guard next elapsed hsplit
  have hr := (route_support_iff_legal N past hs _ d).mpr (fixedRegisterPrefix_legal N past _)
  have hd := route_in_source_support N r past _ d hr
  refine ⟨hd,actual_prefix_epoch_compatible N C sample (originalRegister N coin) H
    (originalGamma p) common r pre post guard next elapsed hsplit d hd,?_⟩
  have hw := actual_original_epoch_word N C H (originalGamma p) common pre guard next post hsplit
  have hloc := actual_prefix_follows_same_original_selector N C sample H (originalGamma p)
    common coin _ _ hw
  simpa only [d,past,fixedRegisterPrefix_append,fixedRegisterPrefix] using hloc

/-- The actual Code endpoint reads exactly the prior geometric current-port
reader, on the same original register and same older-side physical cut. -/
theorem actual_fixed_cut_description_read (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (D : ∀ x, NativeCurrentDescription N C H (sample x) t) (coin : Hybrid N → Bool) :
    let past := prefixThrough N C H (originalGamma p) common pre guard ++
      [.interval (Real.toNNReal (t-guard))]
    let d := fixedRegisterPrefix N past (initialCode N sample (originalRegister N coin))
    ∀ x, copyLocation (state d) x = .edge (descriptionRead N C hcut H (D x) coin) := by
  dsimp only
  let elapsed := Real.toNNReal (t-guard)
  let past := prefixThrough N C H (originalGamma p) common pre guard ++ [.interval elapsed]
  let d := fixedRegisterPrefix N past (initialCode N sample (originalRegister N coin))
  obtain ⟨hd,hphysical,hselector⟩ := actual_fixed_cut_source_geometry N C sample H p common r
    pre post guard next elapsed hsplit coin
  obtain ⟨dates,hshape⟩ := prefix_activation_shape N C H (originalGamma p) common pre guard next post hsplit
  have hfirst := first_date_of_contemporaneous_tips N C a0 htips
  have hsample : ∀ x : Copy, C.age (N.leaf (sample x)) = firstOriginalDate N C := by
    intro x; rw [hfirst,htips]
  have hno : NoPendingNodes N d := by
    apply actual_activated_prefix_no_pending N C sample (originalRegister N coin) H
      (originalGamma p) common r (firstOriginalDate N C) dates elapsed hsample d
    simpa only [←hshape] using hd
  intro x
  cases hx : copyLocation (state d) x with
  | node v => exact False.elim (hno x v hx)
  | rootPopulation v =>
      have h := hphysical x
      rw [hx] at h
      exact False.elim (not_lt_of_ge (h.2.trans hleft) hroot)
  | edge e =>
      have hactive := epoch_edge_active N C hphysical hx hleft hright
      have hmember := selectorLocation_edge_mem_compiled N C (coinSelector N H coin) (sample x) e
        (hx ▸ hselector x)
      have hread := description_read_native_source_spec N C hcut H (D x) (fun _ => coin)
      have heq : e = descriptionRead N C hcut H (D x) coin :=
        (compiledRoute_source_spec N C (coinSelector N H coin) (N.leaf (sample x))).1.active_unique
          C hmember hread.1 hactive hread.2
      exact congrArg Location.edge heq

/-- Named full-consumer bridge: every simultaneous safe current-position
choice has positive actual no-selected-merger posterior support, using ONE
original register for all retained original representatives. No fair weight,
hidden-law equality, or independent stage registers occur in this statement. -/
theorem safe_choices_have_actual_cut_support {G : Type*} [Fintype G] [DecidableEq G]
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : G ↪ X) (htip : ∀ g, tip g ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) (ht : a0 ≤ t)
    (hroot : t < C.age N.root) (hsafe : GProgram.G5.SafePast.SafeAt N C B t)
    (D : ∀ g, NativeCurrentDescription N C H (tip g) t) (choice : G → Fin 2) :
    ∃ (pre post : List ℝ) (guard next : ℝ),
      sortedOriginalDates N C = pre ++ guard :: next :: post ∧ guard ≤ t ∧ t < next ∧
      ∃ (coin : Hybrid N → Bool) (d : Code N tip),
        let past := prefixThrough N C H (originalGamma p) common pre guard ++
          [.interval (Real.toNNReal (t-guard))]
        joinedProjection N Finset.univ (.inl d) ∈
          (originalFullPosterior N tip p r Finset.univ past).support ∧
        (state d).register = originalRegister N coin ∧
        ∀ g, copyLocation (state d) g = .edge
          (GProgram.G5.OriginalCoinLaw.binaryPositions
            (descriptionPositions N C hcut H (D g)) (choice g)) := by
  have hfirst := first_date_of_contemporaneous_tips N C a0 htips
  obtain ⟨pre,guard,next,post,hsplit,hleft,hright⟩ := original_older_gap_exists N C t
    (by simpa only [hfirst] using ht) hroot
  obtain ⟨coin,hcoin⟩ := GProgram.G5.AttainedChronology.safe_common_register_realizes_group_choices
    N C hcut H B tip htip hsafe D choice
  let past := prefixThrough N C H (originalGamma p) common pre guard ++
    [.interval (Real.toNNReal (t-guard))]
  let d := fixedRegisterPrefix N past (initialCode N tip (originalRegister N coin))
  refine ⟨pre,post,guard,next,hsplit,hleft,hright,coin,d,?_⟩
  dsimp only
  refine ⟨(actual_posterior_support_iff_seeds N tip p r past
    (actual_cut_word_strict N C H p common pre post guard next _ hsplit) _).mpr
    ⟨coin,d,fixedRegisterPrefix_legal N past _,rfl⟩,?_,?_⟩
  · exact fixedRegisterPrefix_register N past _
  · intro g
    have hread := actual_fixed_cut_description_read N C tip hcut H p common r a0 t htips
      pre post guard next hsplit hleft hright hroot D coin g
    simpa only [hcoin g] using hread


/-- Every actual supported endpoint at this physical cut has an active
original edge. This also rules out the artificial `none` branch of the finite
population reader below the root. -/
theorem actual_cut_supported_locations_active (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (d : Code N sample)
    (hd : d ∈ (sourceProgram N r
      (prefixThrough N C H (originalGamma p) common pre guard ++
        [.interval (Real.toNNReal (t-guard))]) (initialCode N sample register)).support) :
    ∀ x, ∃ e : E, copyLocation (state d) x = .edge e ∧ C.Active t e := by
  have hp := actual_prefix_epoch_compatible N C sample register H (originalGamma p) common r
    pre post guard next _ hsplit d hd
  obtain ⟨dates,hshape⟩ := prefix_activation_shape N C H (originalGamma p) common pre guard next post hsplit
  have hfirst := first_date_of_contemporaneous_tips N C a0 htips
  have hsample : ∀ x : Copy, C.age (N.leaf (sample x)) = firstOriginalDate N C := by
    intro x; rw [hfirst,htips]
  have hn : NoPendingNodes N d := by
    apply actual_activated_prefix_no_pending N C sample register H (originalGamma p) common r
      (firstOriginalDate N C) dates (Real.toNNReal (t-guard)) hsample d
    simpa only [←hshape] using hd
  intro x
  cases hx : copyLocation (state d) x with
  | node v => exact False.elim (hn x v hx)
  | edge e => exact ⟨e,by simp only [hx],epoch_edge_active N C hp hx hleft hright⟩
  | rootPopulation v =>
      have hr := hp x
      rw [hx] at hr
      exact False.elim (not_lt_of_ge (hr.2.trans hleft) hroot)

/-- Classification of an actual active original edge by the existing native
current description. Per-copy path witnesses here classify an already existing
state; they do not assert independence or replace its COMMON register. -/
theorem actual_active_location_is_description_position {G : Type*} [Fintype G] [DecidableEq G]
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (tip : G ↪ X) (t : ℝ)
    (D : ∀ g, NativeCurrentDescription N C H (tip g) t)
    (d : Code N tip) (g : G) (e : E)
    (he : copyLocation (state d) g = .edge e) (ha : C.Active t e) :
    ∃ k : Fin 2, e = binaryPositions (descriptionPositions N C hcut H (D g)) k := by
  obtain ⟨es,hpath,hem⟩ := actual_edge_on_original_route N d g e he
  obtain ⟨coin,hcoin⟩ := GProgram.G5.AttainedChronology.compiledRoute_covers_original_path N C H hpath
  have hread := description_read_native_source_spec N C hcut H (D g) (fun _ => coin)
  have hreadmem : descriptionRead N C hcut H (D g) coin ∈ es := by
    simpa only [compiledRouteFamily,hcoin] using hread.1
  have heq : e = descriptionRead N C hcut H (D g) coin :=
    hpath.active_unique C hem hreadmem ha hread.2
  obtain ⟨choice,hchoice⟩ := GProgram.G5.AttainedChronology.common_group_reads_are_coupled_choices
    N C hcut H tip D coin
  exact ⟨choice g,heq.trans (hchoice g)⟩

/-- All current-position choices at a FIXED actual chart have positive actual
code-posterior support. The witnesses retain one original register. -/
theorem safe_choices_supported_at_chart {G : Type*} [Fintype G] [DecidableEq G]
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : G ↪ X) (htip : ∀ g, tip g ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (hsafe : GProgram.G5.SafePast.SafeAt N C B t)
    (D : ∀ g, NativeCurrentDescription N C H (tip g) t) (choice : G → Fin 2) :
    let past := prefixThrough N C H (originalGamma p) common pre guard ++
      [.interval (Real.toNNReal (t-guard))]
    ∃ (coin : Hybrid N → Bool) (d : Code N tip),
      d ∈ (originalTripleCodePosterior N tip p r past).support ∧
      (state d).register = originalRegister N coin ∧
      ∀ g, codePopulation N d g = some (binaryPositions (descriptionPositions N C hcut H (D g)) (choice g)) := by
  dsimp only
  obtain ⟨coin,hcoin⟩ := GProgram.G5.AttainedChronology.safe_common_register_realizes_group_choices
    N C hcut H B tip htip hsafe D choice
  let past := prefixThrough N C H (originalGamma p) common pre guard ++
    [.interval (Real.toNNReal (t-guard))]
  let d := fixedRegisterPrefix N past (initialCode N tip (originalRegister N coin))
  have hs := actual_cut_word_strict N C H p common pre post guard next
    (Real.toNNReal (t-guard)) hsplit
  have hroute : d ∈ (originalRouteLaw N tip p past).support :=
    (actual_original_route_support_iff_seeds N tip p past hs d).mpr
      ⟨coin,fixedRegisterPrefix_legal N past _⟩
  obtain ⟨hd,hstart⟩ := (actual_original_singleton_iff_route N tip p r past d).mpr hroute
  refine ⟨coin,d,(PMF.mem_support_filter_iff
    (actual_full_code_event_witness N tip p r Finset.univ past)).mpr ⟨hstart,hd⟩,
    fixedRegisterPrefix_register N past _,?_⟩
  intro g
  have hloc := actual_fixed_cut_description_read N C tip hcut H p common r a0 t htips
    pre post guard next hsplit hleft hright hroot D coin g
  have hloc' : copyLocation (state d) g = .edge (descriptionRead N C hcut H (D g) coin) := hloc
  simp [codePopulation,hloc',hcoin g]

/-- Exact stochastic/geometric support equality needed by the full M3 safe
block consumer. The left side is the actual finite source posterior, obtained
from the original register law and the actual no-selected-merger event. The
right side is the already proved at-most-two-position support geometry. Its
Cartesian form says nothing about factorization of posterior probabilities. -/
theorem actual_safe_cut_population_support_iff {G : Type*} [Fintype G] [DecidableEq G]
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : G ↪ X) (htip : ∀ g, tip g ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (hsafe : GProgram.G5.SafePast.SafeAt N C B t)
    (D : ∀ g, NativeCurrentDescription N C H (tip g) t) (place : G → Option E) :
    let past := prefixThrough N C H (originalGamma p) common pre guard ++
      [.interval (Real.toNNReal (t-guard))]
    place ∈ ((originalTripleCodePosterior N tip p r past).map (codePopulation N)).support ↔
      ∃ choice : G → Fin 2, ∀ g,
        place g = some (binaryPositions (descriptionPositions N C hcut H (D g)) (choice g)) := by
  dsimp only
  let past := prefixThrough N C H (originalGamma p) common pre guard ++
    [.interval (Real.toNNReal (t-guard))]
  constructor
  · intro hp
    obtain ⟨d,hd,hdplace⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
    have hdsource := ((PMF.mem_support_filter_iff
      (actual_full_code_event_witness N tip p r Finset.univ past)).mp hd).2
    obtain ⟨reg,hreg,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdsource
    have hactive := actual_cut_supported_locations_active N C tip reg H p common r a0 t htips
      pre post guard next hsplit hleft hright hroot d hdr
    have hchoice : ∀ g, ∃ k : Fin 2,
        place g = some (binaryPositions (descriptionPositions N C hcut H (D g)) k) := by
      intro g
      obtain ⟨e,he,ha⟩ := hactive g
      obtain ⟨k,hk⟩ := actual_active_location_is_description_position N C hcut H tip t D d g e he ha
      refine ⟨k,?_⟩
      rw [←hdplace]
      simp only [codePopulation,he,hk]
    choose choice hchoice using hchoice
    exact ⟨choice,hchoice⟩
  · rintro ⟨choice,hchoice⟩
    obtain ⟨coin,d,hd,hreg,hdloc⟩ := safe_choices_supported_at_chart N C hcut H p common r
      B tip htip a0 t htips pre post guard next hsplit hleft hright hroot hsafe D choice
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨d,hd,funext (fun g => (hdloc g).trans (hchoice g).symm)⟩

#print axioms fixedRegisterPrefix_legal
#print axioms actual_prefix_follows_same_original_selector
#print axioms actual_prefix_epoch_compatible
#print axioms actual_fixed_cut_description_read
#print axioms safe_choices_have_actual_cut_support
#print axioms safe_choices_supported_at_chart
#print axioms actual_safe_cut_population_support_iff
end GProgram.G5.SafePrefixRouteBridge
