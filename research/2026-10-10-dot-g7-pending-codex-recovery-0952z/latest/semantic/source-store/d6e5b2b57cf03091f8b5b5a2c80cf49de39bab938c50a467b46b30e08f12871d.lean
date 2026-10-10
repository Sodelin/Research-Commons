import G2LiveLineageRouting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Lean.Elab.Tactic.Omega

/-!
# Original-source labelled forest transition semantics

Attributed contribution: dot's shared G1/G2 formal lane, 2026-10-02.
This module CONSTRUCTS finite original-copy ancestry and genealogy state and
proves preservation under explicit source transitions. An ancestral token is
represented by a surviving original copy ID. A merger grafts the two existing
binary genealogies; no earlier merge or copy label is erased. Child order is
an encoding detail here, not yet an unranked-tree quotient theorem.

Original population edges have type E, and the root population retains the
original root vertex. One independent coin is drawn for each CURRENT token at
the named original hybrid; a common pulse reuses the stored original-hybrid
register. Concrete finite product weights are normalized below.

This is a finite transition compiler component, not construction/uniqueness
of the continuous-time stochastic source law, full selected-label projectivity,
G1 context-kernel extraction, core compression, or source realizability.
-/

namespace GProgram.SourceForest

open Nanuq.Source
open scoped BigOperators

inductive Genealogy (Copy : Type*)
  | leaf (copy : Copy)
  | graft (left right : Genealogy Copy)
  deriving DecidableEq

variable {Copy V E X : Type*}
variable [Fintype Copy] [DecidableEq Copy]

/-- Every original sample label carried by this recorded merger subtree. -/
def Genealogy.leaves : Genealogy Copy → Finset Copy
  | .leaf x => {x}
  | .graft a b => a.leaves ∪ b.leaves

/-- A recorded genealogy never repeats an original copy label. -/
def Genealogy.WellLabelled : Genealogy Copy → Prop
  | .leaf _ => True
  | .graft a b => a.WellLabelled ∧ b.WellLabelled ∧ Disjoint a.leaves b.leaves

inductive Location (V E : Type*)
  | node (originalVertex : V)
  | edge (originalEdge : E)
  | rootPopulation (originalRoot : V)
  deriving DecidableEq

inductive SourceEvent (V E Copy : Type*)
  | merger (survivor removed : Copy) (population : Location V E)
  | parentPulse (originalHybrid : V) (coins : Copy → Option Bool)
  | edgeExit (originalEdge : E)
  | ordinaryEntry (originalEdge : E)
  | rootEntry (originalRoot : V)

/-- Full joint state: all sampled copies share this single ancestry/forest,
population assignment, original-hybrid register and complete event history. -/
structure State (V E Copy : Type*) [DecidableEq Copy] where
  live : Finset Copy
  ancestor : Copy → Copy
  genealogy : Copy → Genealogy Copy
  location : Copy → Location V E
  register : V → Bool
  history : List (SourceEvent V E Copy)

/-- Exact, non-assumed compiler invariant. Its preservation is proved below. -/
structure Valid (s : State V E Copy) : Prop where
  ancestor_live : ∀ x, s.ancestor x ∈ s.live
  representative : ∀ l ∈ s.live, s.ancestor l = l
  leaf_fiber : ∀ l ∈ s.live, ∀ x, x ∈ (s.genealogy l).leaves ↔ s.ancestor x = l
  wellLabelled : ∀ l ∈ s.live, (s.genealogy l).WellLabelled

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Initial state from the original source's own labelled tips. Multiplicities
are encoded by sample : Copy → X; Copy is the TOTAL gene-copy cap. -/
def initial (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    State V E Copy where
  live := Finset.univ
  ancestor := id
  genealogy := Genealogy.leaf
  location := fun x => .node (N.leaf (sample x))
  register := register
  history := []

theorem initial_valid (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) : Valid (initial N sample register) := by
  constructor
  · intro x; exact Finset.mem_univ x
  · intro l hl; rfl
  · intro l hl x; simp [initial, Genealogy.leaves, eq_comm]
  · intro l hl; trivial

/-- Recorded output population of an ORIGINAL sample label. -/
def copyLocation (s : State V E Copy) (x : Copy) : Location V E :=
  s.location (s.ancestor x)

theorem merged_copies_same_population (s : State V E Copy) {x y : Copy}
    (h : s.ancestor x = s.ancestor y) : copyLocation s x = copyLocation s y := by
  simp only [copyLocation, h]

theorem distinct_live_genealogies_disjoint (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (ha : a ∈ s.live) (hb : b ∈ s.live) (hab : a ≠ b) :
    Disjoint (s.genealogy a).leaves (s.genealogy b).leaves := by
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  exact hab ((hs.leaf_fiber a ha x).mp hxa |>.symm.trans ((hs.leaf_fiber b hb x).mp hxb))

/-- Grafting preserves complete earlier subtrees. The removed representative
ID is no longer live; all its original-copy descendants now use a. -/
def merge (s : State V E Copy) (a b : Copy) : State V E Copy where
  live := s.live.erase b
  ancestor := fun x => if s.ancestor x = b then a else s.ancestor x
  genealogy := fun l => if l = a then .graft (s.genealogy a) (s.genealogy b)
    else s.genealogy l
  location := s.location
  register := s.register
  history := s.history ++ [.merger a b (s.location a)]

/-- Legal source merger: distinct CURRENT ancestors, occupying one actual
original-edge/root population. Node boundary states cannot coalesce. -/
structure LegalMerge (s : State V E Copy) (a b : Copy) : Prop where
  first_live : a ∈ s.live
  second_live : b ∈ s.live
  different : a ≠ b
  same_population : s.location a = s.location b
  population_not_node : ∀ v, s.location a ≠ .node v

theorem merge_valid (s : State V E Copy) (hs : Valid s) {a b : Copy}
    (hm : LegalMerge s a b) : Valid (merge s a b) := by
  constructor
  · intro x
    by_cases hx : s.ancestor x = b
    · simp only [merge, if_pos hx]
      exact Finset.mem_erase.mpr ⟨hm.different, hm.first_live⟩
    · simp only [merge, if_neg hx]
      exact Finset.mem_erase.mpr ⟨hx, hs.ancestor_live x⟩
  · intro l hl
    have h := Finset.mem_erase.mp hl
    simp only [merge]
    rw [hs.representative l h.2, if_neg h.1]
  · intro l hl x
    obtain ⟨hlb, hll⟩ := Finset.mem_erase.mp hl
    by_cases hla : l = a
    · subst l
      simp only [merge, ite_true, Genealogy.leaves, Finset.mem_union]
      rw [hs.leaf_fiber a hm.first_live x, hs.leaf_fiber b hm.second_live x]
      by_cases hx : s.ancestor x = b
      · simp [hx]
      · simp [hx]
    · simp only [merge, if_neg hla]
      rw [hs.leaf_fiber l hll x]
      by_cases hx : s.ancestor x = b
      · simp [hx, Ne.symm hla, Ne.symm hlb]
      · simp [hx]
  · intro l hl
    obtain ⟨hlb, hll⟩ := Finset.mem_erase.mp hl
    by_cases hla : l = a
    · subst l
      simp only [merge, ite_true, Genealogy.WellLabelled]
      exact ⟨hs.wellLabelled a hm.first_live, hs.wellLabelled b hm.second_live,
        distinct_live_genealogies_disjoint s hs hm.first_live hm.second_live hm.different⟩
    · simpa only [merge, if_neg hla] using hs.wellLabelled l hll

theorem merge_coalesces_exact_fibers (s : State V E Copy) {a b x : Copy} :
    (merge s a b).ancestor x = a ↔ s.ancestor x = a ∨ s.ancestor x = b := by
  by_cases h : s.ancestor x = b <;> simp [merge, h]

theorem merge_never_splits (s : State V E Copy) (a b : Copy) {x y : Copy}
    (h : s.ancestor x = s.ancestor y) :
    (merge s a b).ancestor x = (merge s a b).ancestor y := by
  simp only [merge, h]

theorem merge_population_preserved (s : State V E Copy) {a b : Copy}
    (hm : LegalMerge s a b) (x : Copy) :
    copyLocation (merge s a b) x = copyLocation s x := by
  by_cases hx : s.ancestor x = b
  · simp only [copyLocation, merge, if_pos hx]
    simpa only [hx] using hm.same_population
  · simp only [copyLocation, merge, if_neg hx]

theorem merge_live_card (s : State V E Copy) {a b : Copy}
    (hm : LegalMerge s a b) : (merge s a b).live.card + 1 = s.live.card := by
  exact Finset.card_erase_add_one hm.second_live

theorem original_copy_cap (s : State V E Copy) : s.live.card ≤ Fintype.card Copy :=
  Finset.card_le_univ _

/-- Population transport touches neither the joint genealogy nor ancestry. -/
def transport (s : State V E Copy) (location : Copy → Location V E)
    (event : SourceEvent V E Copy) : State V E Copy :=
  { s with location := location, history := s.history ++ [event] }

theorem transport_valid (s : State V E Copy) (hs : Valid s)
    (location : Copy → Location V E) (event : SourceEvent V E Copy) :
    Valid (transport s location event) :=
  ⟨hs.ancestor_live, hs.representative, hs.leaf_fiber, hs.wellLabelled⟩

variable [DecidableEq E]
variable {N : RootedBinary V E X}

/-- Only tokens at the original edge are moved to its original older endpoint. -/
def exitEdge (N : RootedBinary V E X) (s : State V E Copy) (e : E) : State V E Copy :=
  transport s (fun l => if s.location l = .edge e then .node (N.graph.source e)
    else s.location l) (.edgeExit e)

/-- Original edge occurrence remains distinguishable even with parallel arcs. -/
def enterEdge (N : RootedBinary V E X) (s : State V E Copy) (e : E) : State V E Copy :=
  transport s (fun l => if s.location l = .node (N.graph.target e) then .edge e
    else s.location l) (.ordinaryEntry e)

/-- The root component is retained. It is never replaced by an empty exterior. -/
def enterRoot (N : RootedBinary V E X) (s : State V E Copy) : State V E Copy :=
  transport s (fun l => if s.location l = .node N.root then .rootPopulation N.root
    else s.location l) (.rootEntry N.root)

theorem enterRoot_retains_original_root (N : RootedBinary V E X) (s : State V E Copy)
    (l : Copy) (hl : s.location l = .node N.root) :
    (enterRoot N s).location l = .rootPopulation N.root := by
  simp [enterRoot, transport, hl]

/-- The finite coin index is exactly the CURRENT ancestral forest tokens at v. -/
def AtNode (s : State V E Copy) (v : V) :=
  { l : Copy // l ∈ s.live ∧ s.location l = .node v }

instance atNodeDecidableEq (s : State V E Copy) (v : V) : DecidableEq (AtNode s v) := by
  unfold AtNode
  infer_instance

noncomputable instance atNodeFintype (s : State V E Copy) (v : V) : Fintype (AtNode s v) := by
  classical
  unfold AtNode
  infer_instance

noncomputable def pulse (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) : State V E Copy := by
  classical
  let coins : Copy → Option Bool := fun l =>
    if h : l ∈ s.live ∧ s.location l = .node H.hybrid then some (coin ⟨l, h⟩) else none
  exact transport s (fun l =>
    if h : l ∈ s.live ∧ s.location l = .node H.hybrid then .edge (H.parent (coin ⟨l,h⟩))
    else s.location l) (.parentPulse H.hybrid coins)

noncomputable def commonPulse (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) : State V E Copy :=
  pulse H s (fun _ => s.register H.hybrid)

theorem pulse_valid (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (hs : Valid s) (coin : AtNode s H.hybrid → Bool) :
    Valid (pulse H s coin) :=
  ⟨hs.ancestor_live, hs.representative, hs.leaf_fiber, hs.wellLabelled⟩

theorem pulse_ancestor_unchanged (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) :
    (pulse H s coin).ancestor = s.ancestor := rfl

theorem pulse_genealogy_unchanged (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) :
    (pulse H s coin).genealogy = s.genealogy := rfl

theorem pulse_register_retained (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) :
    (pulse H s coin).register = s.register := rfl

theorem pulse_routes_current_ancestor (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) (l : AtNode s H.hybrid) :
    (pulse H s coin).location l.val = .edge (H.parent (coin l)) := by
  simp only [pulse, transport, dif_pos l.property]
  rfl

theorem pulse_cannot_split_copies (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) {x y : Copy}
    (hxy : s.ancestor x = s.ancestor y) :
    copyLocation (pulse H s coin) x = copyLocation (pulse H s coin) y := by
  apply merged_copies_same_population
  exact hxy

/-- Concrete per-live-ancestor finite Bernoulli weights. -/
def bitWeight (p : ℚ) (b : Bool) : ℚ := if b then 1 - p else p

noncomputable def independentWeight {A : Type*} [Fintype A]
    (p : ℚ) (coin : A → Bool) : ℚ := ∏ l, bitWeight p (coin l)

theorem independentWeight_normalized (A : Type*) [Fintype A] [DecidableEq A] (p : ℚ) :
    (∑ coin : A → Bool, independentWeight p coin) = 1 := by
  classical
  simp only [independentWeight]
  rw [← Fintype.prod_sum]
  simp [Fintype.sum_bool, bitWeight]

theorem independentWeight_nonnegative {A : Type*} [Fintype A] {p : ℚ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (coin : A → Bool) :
    0 ≤ independentWeight p coin := by
  apply Finset.prod_nonneg
  intro l _
  cases coin l <;> simp only [bitWeight, Bool.false_eq_true, if_false, if_true]
  · exact hp
  · exact sub_nonneg.mpr hp1

/-- A source population can contain only genealogies below its actual original
node/edge, and its ancestral population retains the supplied original root. -/
def DescendsTo (N : RootedBinary V E X) (location : Location V E) (x : X) : Prop :=
  match location with
  | .node v => N.graph.DReach v (N.leaf x)
  | .edge e => N.graph.DReach (N.graph.target e) (N.leaf x)
  | .rootPopulation r => r = N.root ∧ N.graph.DReach r (N.leaf x)

structure SourceValid (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) : Prop where
  forest : Valid s
  original_descendant : ∀ x, DescendsTo N (copyLocation s x) (sample x)

theorem initial_source_valid (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) : SourceValid N sample (initial N sample register) := by
  exact ⟨initial_valid N sample register, fun _ => Relation.ReflTransGen.refl⟩

theorem merge_source_valid (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) {a b : Copy}
    (hm : LegalMerge s a b) : SourceValid N sample (merge s a b) := by
  refine ⟨merge_valid s hs.forest hm, ?_⟩
  intro x
  rw [merge_population_preserved s hm]
  exact hs.original_descendant x

theorem exitEdge_source_valid (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) (e : E) :
    SourceValid N sample (exitEdge N s e) := by
  refine ⟨transport_valid s hs.forest _ _, ?_⟩
  intro x
  have hd := hs.original_descendant x
  by_cases h : s.location (s.ancestor x) = .edge e
  · simp only [exitEdge, transport, copyLocation, if_pos h, DescendsTo]
    simp only [copyLocation, h, DescendsTo] at hd
    exact (Relation.ReflTransGen.single ⟨e, rfl, rfl⟩).trans hd
  · simpa only [exitEdge, transport, copyLocation, if_neg h] using hd

theorem enterEdge_source_valid (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) (e : E) :
    SourceValid N sample (enterEdge N s e) := by
  refine ⟨transport_valid s hs.forest _ _, ?_⟩
  intro x
  have hd := hs.original_descendant x
  by_cases h : s.location (s.ancestor x) = .node (N.graph.target e)
  · simpa only [enterEdge, transport, copyLocation, if_pos h, h, ite_true, DescendsTo] using hd
  · simpa only [enterEdge, transport, copyLocation, if_neg h] using hd

theorem enterRoot_source_valid (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) :
    SourceValid N sample (enterRoot N s) := by
  refine ⟨transport_valid s hs.forest _ _, ?_⟩
  intro x
  have hd := hs.original_descendant x
  by_cases h : s.location (s.ancestor x) = .node N.root
  · simp only [enterRoot, transport, copyLocation, if_pos h, DescendsTo]
    exact ⟨trivial, by simpa only [copyLocation, h, DescendsTo] using hd⟩
  · simpa only [enterRoot, transport, copyLocation, if_neg h] using hd

theorem original_parent_targets_hybrid (H : GProgram.G2.OriginalHybridParents N)
    (b : Bool) : N.graph.target (H.parent b) = H.hybrid := by
  cases b <;> simp [GProgram.G2.OriginalHybridParents.parent, H.target0, H.target1]

theorem pulse_source_valid (H : GProgram.G2.OriginalHybridParents N)
    (sample : Copy → X) (s : State V E Copy) (hs : SourceValid N sample s)
    (coin : AtNode s H.hybrid → Bool) : SourceValid N sample (pulse H s coin) := by
  classical
  refine ⟨pulse_valid H s hs.forest coin, ?_⟩
  intro x
  have hd := hs.original_descendant x
  by_cases h : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid
  · simp only [pulse, transport, copyLocation, dif_pos h, DescendsTo,
      original_parent_targets_hybrid]
    simpa only [copyLocation, h.2, DescendsTo] using hd
  · simpa only [pulse, transport, copyLocation, dif_neg h] using hd

/-- Typed legal source steps. Parent choices are attached to original hybrids;
ordinary entries have original indegree one. There is no abstract kernel field. -/
inductive Step (N : RootedBinary V E X) : State V E Copy → State V E Copy → Prop
  | merger (s a b) (legal : LegalMerge s a b) : Step N s (merge s a b)
  | exit (s e) : Step N s (exitEdge N s e)
  | ordinary (s e) (degree : N.graph.inDegree (N.graph.target e) = 1) :
      Step N s (enterEdge N s e)
  | root (s) : Step N s (enterRoot N s)
  | independent (s) (H : GProgram.G2.OriginalHybridParents N)
      (coin : AtNode s H.hybrid → Bool) : Step N s (pulse H s coin)
  | common (s) (H : GProgram.G2.OriginalHybridParents N) : Step N s (commonPulse H s)

theorem step_source_valid (sample : Copy → X) {s t : State V E Copy}
    (hs : SourceValid N sample s) (hstep : Step N s t) : SourceValid N sample t := by
  cases hstep with
  | merger a b hm => exact merge_source_valid N sample _ hs hm
  | exit e => exact exitEdge_source_valid N sample _ hs e
  | ordinary e hd => exact enterEdge_source_valid N sample _ hs e
  | root => exact enterRoot_source_valid N sample _ hs
  | independent H coin => exact pulse_source_valid H sample _ hs coin
  | common H => exact pulse_source_valid H sample _ hs _

theorem step_register_retained {s t : State V E Copy} (hstep : Step N s t) :
    t.register = s.register := by
  cases hstep <;> rfl

theorem step_history_extends {s t : State V E Copy} (hstep : Step N s t) :
    ∃ event, t.history = s.history ++ [event] := by
  cases hstep <;> exact ⟨_, rfl⟩

/-- Actual finite programs are chains of legal source transitions; their source
and forest validity follows from initialization and induction, not a premise. -/
theorem source_trace_valid (sample : Copy → X) (register : V → Bool)
    {s : State V E Copy}
    (trace : Relation.ReflTransGen (Step N) (initial N sample register) s) :
    SourceValid N sample s := by
  induction trace with
  | refl => exact initial_source_valid N sample register
  | tail _ hstep ih => exact step_source_valid sample ih hstep

theorem source_trace_register (sample : Copy → X) (register : V → Bool)
    {s : State V E Copy}
    (trace : Relation.ReflTransGen (Step N) (initial N sample register) s) :
    s.register = register := by
  induction trace with
  | refl => rfl
  | tail _ hstep ih => exact (step_register_retained hstep).trans ih

/-- The source pulse has an explicit finite stochastic pushforward. Multiple
coin allocations producing the same forest are summed, never refitted. -/
noncomputable def pulseExpectation (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (p : ℚ) (readout : State V E Copy → ℚ) : ℚ := by
  classical
  exact ∑ coin : AtNode s H.hybrid → Bool, independentWeight p coin * readout (pulse H s coin)

theorem pulseExpectation_one (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (p : ℚ) : pulseExpectation H s p (fun _ => 1) = 1 := by
  classical
  simp only [pulseExpectation, mul_one]
  exact independentWeight_normalized _ p

theorem pulseExpectation_nonnegative (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (readout : State V E Copy → ℚ) (hf : ∀ t, 0 ≤ readout t) :
    0 ≤ pulseExpectation H s p readout := by
  classical
  apply Finset.sum_nonneg
  intro coin _
  exact mul_nonneg (independentWeight_nonnegative hp hp1 coin) (hf _)

/-- Join restricted subtrees, suppressing empty children/unary vertices. -/
def Genealogy.joinPruned : Option (Genealogy Copy) → Option (Genealogy Copy) →
    Option (Genealogy Copy)
  | none, b => b
  | a, none => a
  | some a, some b => some (.graft a b)

/-- Deterministic selected-label restriction retains complete earlier selected
subtrees and suppresses the mergers involving only one selected child. -/
def Genealogy.prune (keep : Finset Copy) : Genealogy Copy → Option (Genealogy Copy)
  | .leaf x => if x ∈ keep then some (.leaf x) else none
  | .graft a b => joinPruned (a.prune keep) (b.prune keep)

def Genealogy.optionLeaves : Option (Genealogy Copy) → Finset Copy
  | none => ∅
  | some a => a.leaves

theorem Genealogy.joinPruned_leaves (a b : Option (Genealogy Copy)) :
    optionLeaves (joinPruned a b) = optionLeaves a ∪ optionLeaves b := by
  cases a <;> cases b <;> simp [joinPruned, optionLeaves, leaves]

theorem Genealogy.prune_leaves (keep : Finset Copy) (t : Genealogy Copy) :
    optionLeaves (t.prune keep) = t.leaves ∩ keep := by
  induction t with
  | leaf x =>
      by_cases hx : x ∈ keep
      · simp [prune, optionLeaves, leaves, hx]
      · simp [prune, optionLeaves, leaves, hx]
  | graft a b iha ihb =>
      simp only [prune, joinPruned_leaves, iha, ihb, leaves,
        Finset.union_inter_distrib_right]

/-- A selected forest root is its retained labelled clade, not a refitted source
population nor necessarily an original representative lying in keep. -/
def selectedBlock (s : State V E Copy) (keep : Finset Copy) (l : Copy) : Finset Copy :=
  (s.genealogy l).leaves ∩ keep

noncomputable def visibleAncestors (s : State V E Copy) (keep : Finset Copy) : Finset Copy := by
  classical
  exact s.live.filter (fun l => (selectedBlock s keep l).Nonempty)

theorem mem_visibleAncestors (s : State V E Copy) (keep : Finset Copy) (l : Copy) :
    l ∈ visibleAncestors s keep ↔ l ∈ s.live ∧ (selectedBlock s keep l).Nonempty := by
  classical
  exact Finset.mem_filter

theorem selectedBlock_eq_fiber (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {l : Copy} (hl : l ∈ s.live) (x : Copy) :
    x ∈ selectedBlock s keep l ↔ x ∈ keep ∧ s.ancestor x = l := by
  simp only [selectedBlock, Finset.mem_inter, hs.leaf_fiber l hl x, and_comm]

theorem visibleAncestors_eq_selected_fibers (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (l : Copy) :
    l ∈ visibleAncestors s keep ↔ ∃ x ∈ keep, s.ancestor x = l := by
  rw [mem_visibleAncestors]
  constructor
  · rintro ⟨hl, x, hx⟩
    exact ⟨x, (selectedBlock_eq_fiber s hs keep hl x).mp hx⟩
  · rintro ⟨x, hx, hxl⟩
    have hl : l ∈ s.live := hxl ▸ hs.ancestor_live x
    exact ⟨hl, x, (selectedBlock_eq_fiber s hs keep hl x).mpr ⟨hx, hxl⟩⟩

theorem selectedBlock_injective_on_visible (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (ha : a ∈ visibleAncestors s keep)
    (hb : b ∈ visibleAncestors s keep)
    (heq : selectedBlock s keep a = selectedBlock s keep b) : a = b := by
  obtain ⟨halive, x, hx⟩ := (mem_visibleAncestors s keep a).mp ha
  obtain ⟨hblive, _⟩ := (mem_visibleAncestors s keep b).mp hb
  have hxa := ((selectedBlock_eq_fiber s hs keep halive x).mp hx).2
  have hxb := ((selectedBlock_eq_fiber s hs keep hblive x).mp (heq ▸ hx)).2
  exact hxa.symm.trans hxb

theorem selectedBlock_merge_survivor (s : State V E Copy) (keep : Finset Copy)
    (a b : Copy) : selectedBlock (merge s a b) keep a =
    selectedBlock s keep a ∪ selectedBlock s keep b := by
  simp [selectedBlock, merge, Genealogy.leaves, Finset.union_inter_distrib_right]

theorem selectedBlock_merge_other (s : State V E Copy) (keep : Finset Copy)
    (a b l : Copy) (hla : l ≠ a) : selectedBlock (merge s a b) keep l =
    selectedBlock s keep l := by
  simp only [selectedBlock, merge, if_neg hla]

theorem prune_merge_survivor (s : State V E Copy) (keep : Finset Copy) (a b : Copy) :
    ((merge s a b).genealogy a).prune keep =
    Genealogy.joinPruned ((s.genealogy a).prune keep) ((s.genealogy b).prune keep) := by
  simp [merge, Genealogy.prune]

theorem pulse_selected_genealogy_unchanged (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool)
    (keep : Finset Copy) (l : Copy) :
    ((pulse H s coin).genealogy l).prune keep = (s.genealogy l).prune keep := rfl

def Genealogy.optionWellLabelled : Option (Genealogy Copy) → Prop
  | none => True
  | some t => t.WellLabelled

theorem Genealogy.joinPruned_wellLabelled (a b : Option (Genealogy Copy))
    (ha : optionWellLabelled a) (hb : optionWellLabelled b)
    (hd : Disjoint (optionLeaves a) (optionLeaves b)) :
    optionWellLabelled (joinPruned a b) := by
  cases a <;> cases b <;> simp_all [optionWellLabelled, joinPruned, optionLeaves, WellLabelled]

theorem Genealogy.prune_wellLabelled (keep : Finset Copy) (t : Genealogy Copy)
    (ht : t.WellLabelled) : optionWellLabelled (t.prune keep) := by
  induction t with
  | leaf x =>
      by_cases hx : x ∈ keep <;> simp [prune, optionWellLabelled, WellLabelled, hx]
  | graft a b iha ihb =>
      obtain ⟨ha, hb, hd⟩ := ht
      apply joinPruned_wellLabelled _ _ (iha ha) (ihb hb)
      rw [prune_leaves, prune_leaves]
      apply Finset.disjoint_left.mpr
      intro x hxa hxb
      exact (Finset.disjoint_left.mp hd) (Finset.mem_inter.mp hxa).1
        (Finset.mem_inter.mp hxb).1

/-- Every sampled original label occurs in exactly one live genealogy. -/
theorem unique_live_genealogy (s : State V E Copy) (hs : Valid s) (x : Copy) :
    ∃! l : {l // l ∈ s.live}, x ∈ (s.genealogy l.val).leaves := by
  refine ⟨⟨s.ancestor x, hs.ancestor_live x⟩, ?_, ?_⟩
  · exact (hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl
  · intro l hl
    apply Subtype.ext
    exact ((hs.leaf_fiber l.val l.property x).mp hl).symm

theorem source_live_root_is_original (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) {l : Copy}
    (hl : l ∈ s.live) {r : V} (hr : s.location l = .rootPopulation r) : r = N.root := by
  have h := hs.original_descendant l
  simp only [copyLocation, hs.forest.representative l hl, hr, DescendsTo] at h
  exact h.1

/-- Complete source history records every merger once. This is a source-copy
resource invariant; it does not reinterpret compressed source actuator cost. -/
def SourceEvent.mergerNumber : SourceEvent V E Copy → Nat
  | .merger _ _ _ => 1
  | _ => 0

def mergerCount (s : State V E Copy) : Nat := (s.history.map SourceEvent.mergerNumber).sum

theorem step_original_copy_budget {s t : State V E Copy} (hstep : Step N s t) :
    t.live.card + mergerCount t = s.live.card + mergerCount s := by
  cases hstep with
  | merger a b hm =>
      have hc := merge_live_card _ hm
      simp only [merge] at hc
      simp only [mergerCount, merge, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, SourceEvent.mergerNumber]
      omega
  | exit e => simp [mergerCount, exitEdge, transport, SourceEvent.mergerNumber]
  | ordinary e hd => simp [mergerCount, enterEdge, transport, SourceEvent.mergerNumber]
  | root => simp [mergerCount, enterRoot, transport, SourceEvent.mergerNumber]
  | independent H coin => simp [mergerCount, pulse, transport, SourceEvent.mergerNumber]
  | common H => simp [mergerCount, commonPulse, pulse, transport, SourceEvent.mergerNumber]

theorem source_trace_original_copy_budget (sample : Copy → X) (register : V → Bool)
    {s : State V E Copy}
    (trace : Relation.ReflTransGen (Step N) (initial N sample register) s) :
    s.live.card + mergerCount s = Fintype.card Copy := by
  induction trace with
  | refl => simp [initial, mergerCount]
  | tail _ hstep ih => exact (step_original_copy_budget hstep).trans ih

theorem source_trace_history_prefix {s t : State V E Copy}
    (trace : Relation.ReflTransGen (Step N) s t) :
    ∃ events, t.history = s.history ++ events := by
  induction trace with
  | refl => exact ⟨[], by simp⟩
  | tail _ hstep ih =>
      obtain ⟨events, hevents⟩ := ih
      obtain ⟨event, hevent⟩ := step_history_extends hstep
      exact ⟨events ++ [event], by rw [hevent, hevents, List.append_assoc]⟩

/-- Actual independent routing cylinder mass: unobserved CURRENT ancestors are
summed out, while the retained ancestors' original-hybrid coins are specified. -/
noncomputable def coinCylinderMass {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℚ) (retain : Finset A) (wanted : A → Bool) : ℚ := by
  classical
  exact ∑ coin : A → Bool, independentWeight p coin *
    if ∀ a ∈ retain, coin a = wanted a then 1 else 0

noncomputable def cylinderFactor {A : Type*} [DecidableEq A] (p : ℚ)
    (retain : Finset A) (wanted : A → Bool) (a : A) (b : Bool) : ℚ :=
  if a ∈ retain then (if b = wanted a then bitWeight p b else 0) else bitWeight p b

theorem cylinderFactor_sum {A : Type*} [DecidableEq A] (p : ℚ)
    (retain : Finset A) (wanted : A → Bool) (a : A) :
    (∑ b : Bool, cylinderFactor p retain wanted a b) =
    if a ∈ retain then bitWeight p (wanted a) else 1 := by
  by_cases ha : a ∈ retain <;> cases hw : wanted a <;>
    simp [Fintype.sum_bool, cylinderFactor, bitWeight, ha, hw]

theorem cylinderFactor_product {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℚ) (retain : Finset A) (wanted coin : A → Bool) :
    (∏ a, cylinderFactor p retain wanted a (coin a)) =
    independentWeight p coin * if ∀ a ∈ retain, coin a = wanted a then 1 else 0 := by
  classical
  have hfactor : ∀ a, cylinderFactor p retain wanted a (coin a) =
      bitWeight p (coin a) * (if a ∈ retain → coin a = wanted a then 1 else 0) := by
    intro a
    by_cases ha : a ∈ retain <;> by_cases hc : coin a = wanted a <;>
      simp [cylinderFactor, ha, hc]
  simp only [hfactor, Finset.prod_mul_distrib, Fintype.prod_boole, independentWeight]

/-- Local all-copy projectivity of the ACTUAL live-token independent pulse.
The marginal weights on retained ancestors are again exactly the product law;
extra-copy coins are not silently redrawn or independently fitted. -/
theorem coinCylinderMass_eq_retained_product {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℚ) (retain : Finset A) (wanted : A → Bool) :
    coinCylinderMass p retain wanted = ∏ a ∈ retain, bitWeight p (wanted a) := by
  classical
  simp only [coinCylinderMass, ← cylinderFactor_product]
  rw [← Fintype.prod_sum]
  simp only [cylinderFactor_sum, Finset.prod_ite_mem_eq]

/-- Source-facing selected-label routing marginal: retained roots are exactly
current roots at this ORIGINAL hybrid whose selected genealogy is nonempty. -/
theorem pulse_selected_coin_marginal (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (keep : Finset Copy) (p : ℚ)
    (wanted : AtNode s H.hybrid → Bool) :
    let retain := (Finset.univ : Finset (AtNode s H.hybrid)).filter
      (fun l => (selectedBlock s keep l.val).Nonempty)
    coinCylinderMass p retain wanted = ∏ l ∈ retain, bitWeight p (wanted l) := by
  classical
  exact coinCylinderMass_eq_retained_product p _ wanted

#print axioms pulse_selected_coin_marginal
#print axioms coinCylinderMass_eq_retained_product
#print axioms Genealogy.prune_wellLabelled
#print axioms unique_live_genealogy
#print axioms source_live_root_is_original
#print axioms source_trace_original_copy_budget
#print axioms source_trace_history_prefix
#print axioms Genealogy.prune_leaves
#print axioms selectedBlock_injective_on_visible
#print axioms selectedBlock_merge_survivor
#print axioms prune_merge_survivor
#print axioms source_trace_valid
#print axioms source_trace_register
#print axioms step_history_extends
#print axioms pulseExpectation_one
#print axioms pulseExpectation_nonnegative
#print axioms initial_valid
#print axioms merge_valid
#print axioms merge_population_preserved
#print axioms merge_never_splits
#print axioms merge_live_card
#print axioms enterRoot_retains_original_root
#print axioms pulse_valid
#print axioms pulse_routes_current_ancestor
#print axioms pulse_cannot_split_copies
#print axioms independentWeight_normalized
#print axioms independentWeight_nonnegative

end GProgram.SourceForest
