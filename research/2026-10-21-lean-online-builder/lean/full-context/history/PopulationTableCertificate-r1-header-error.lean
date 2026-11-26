import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Finset.Union
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.List.Perm.Basic

section FullContextModule0



/-!
Raw edge-indexed graph foundations for the source network class.

Edges have their own type: distinct edges with the same endpoints are NOT
identified.  In particular the source's parallel two-cycles are not lost.
No canonical-blob representation, quartet factorization, circular metric,
or desired conclusion is a field of these structures.

Root suppression, planar embeddings, galledness/level certification, canonical
coverage, and actual quartet composition are separate proof obligations.
-/

namespace Nanuq.Source

universe u v w

structure EdgeGraph (V : Type u) (E : Type v) where
  source : E → V
  target : E → V

namespace EdgeGraph

variable {V : Type u} {E : Type v} (G : EdgeGraph V E)

/-- Undirected incidence still refers to the individual edge identity. -/
def Inc (e : E) (a b : V) : Prop :=
  (G.source e = a ∧ G.target e = b) ∨
  (G.source e = b ∧ G.target e = a)

theorem inc_symm {e : E} {a b : V} (h : G.Inc e a b) : G.Inc e b a :=
  h.symm

theorem inc_source_target (e : E) : G.Inc e (G.source e) (G.target e) :=
  Or.inl ⟨rfl, rfl⟩

def UStep (keep : E → Prop) (a b : V) : Prop :=
  ∃ e, keep e ∧ G.Inc e a b

def UReach (keep : E → Prop) (a b : V) : Prop :=
  Relation.ReflTransGen (G.UStep keep) a b

theorem ustep_symm {keep : E → Prop} {a b : V} (h : G.UStep keep a b) :
    G.UStep keep b a := by
  obtain ⟨e, he, hab⟩ := h
  exact ⟨e, he, G.inc_symm hab⟩

theorem ustep_mono {keep more : E → Prop} (hm : ∀ e, keep e → more e)
    {a b : V} (h : G.UStep keep a b) : G.UStep more a b := by
  obtain ⟨e, he, hab⟩ := h
  exact ⟨e, hm e he, hab⟩

theorem ureach_refl (keep : E → Prop) (a : V) : G.UReach keep a a :=
  .refl

theorem ureach_single {keep : E → Prop} {a b : V} (h : G.UStep keep a b) :
    G.UReach keep a b :=
  Relation.ReflTransGen.single h

theorem ureach_trans {keep : E → Prop} {a b c : V}
    (hab : G.UReach keep a b) (hbc : G.UReach keep b c) : G.UReach keep a c :=
  hab.trans hbc

theorem ureach_symm {keep : E → Prop} {a b : V}
    (h : G.UReach keep a b) : G.UReach keep b a := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
      exact (G.ureach_single (G.ustep_symm hstep)).trans ih

theorem ureach_mono {keep more : E → Prop} (hm : ∀ e, keep e → more e)
    {a b : V} (h : G.UReach keep a b) : G.UReach more a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (G.ustep_mono hm hstep)

/-- Deletion removes one edge ID, not all edges with the same endpoints. -/
def ReachWithout (e : E) (a b : V) : Prop :=
  G.UReach (fun f => f ≠ e) a b

/-- An edge is a bridge precisely when its endpoints disconnect on its deletion. -/
def IsBridge (e : E) : Prop :=
  ¬ G.ReachWithout e (G.source e) (G.target e)

theorem not_bridge_of_detour {e : E}
    (h : G.ReachWithout e (G.source e) (G.target e)) : ¬ G.IsBridge e := by
  intro hb
  exact hb h

theorem not_bridge_of_parallel {e f : E} (hne : f ≠ e)
    (hs : G.source f = G.source e) (ht : G.target f = G.target e) :
    ¬ G.IsBridge e := by
  apply G.not_bridge_of_detour
  exact G.ureach_single ⟨f, hne, Or.inl ⟨hs, ht⟩⟩

theorem not_bridge_of_loop {e : E} (h : G.source e = G.target e) :
    ¬ G.IsBridge e := by
  apply G.not_bridge_of_detour
  rw [← h]
  exact .refl

theorem bridge_endpoints_ne {e : E} (h : G.IsBridge e) :
    G.source e ≠ G.target e := by
  intro heq
  exact G.not_bridge_of_loop heq h

/-- The actual blob equivalence: connectivity after deleting every bridge. -/
def SameBlob (a b : V) : Prop :=
  G.UReach (fun e => ¬ G.IsBridge e) a b

theorem sameBlob_refl (a : V) : G.SameBlob a a := .refl

theorem sameBlob_symm {a b : V} (h : G.SameBlob a b) : G.SameBlob b a :=
  G.ureach_symm h

theorem sameBlob_trans {a b c : V} (hab : G.SameBlob a b)
    (hbc : G.SameBlob b c) : G.SameBlob a c :=
  hab.trans hbc

def blobSetoid : Setoid V where
  r := G.SameBlob
  iseqv := ⟨G.sameBlob_refl, G.sameBlob_symm, G.sameBlob_trans⟩

def Blob := Quotient G.blobSetoid

def blobOf (a : V) : G.Blob := Quotient.mk G.blobSetoid a

theorem nonbridge_sameBlob {e : E} (h : ¬ G.IsBridge e) :
    G.SameBlob (G.source e) (G.target e) :=
  G.ureach_single ⟨e, h, G.inc_source_target e⟩

theorem bridge_not_sameBlob {e : E} (h : G.IsBridge e) :
    ¬ G.SameBlob (G.source e) (G.target e) := by
  intro hab
  apply h
  apply G.ureach_mono (keep := fun f => ¬ G.IsBridge f) _ hab
  intro f hf hfe
  subst f
  exact hf h

theorem bridge_blob_ne {e : E} (h : G.IsBridge e) :
    G.blobOf (G.source e) ≠ G.blobOf (G.target e) := by
  intro heq
  exact G.bridge_not_sameBlob h (Quotient.exact heq)

def DStep (a b : V) : Prop :=
  ∃ e, G.source e = a ∧ G.target e = b

def DReach (a b : V) : Prop := Relation.ReflTransGen G.DStep a b

def Acyclic : Prop := ∀ a, ¬ Relation.TransGen G.DStep a a

theorem dstep_ureach {a b : V} (h : G.DStep a b) :
    G.UReach (fun _ => True) a b := by
  obtain ⟨e, hs, ht⟩ := h
  exact G.ureach_single ⟨e, trivial, Or.inl ⟨hs, ht⟩⟩

theorem dreach_ureach {a b : V} (h : G.DReach a b) :
    G.UReach (fun _ => True) a b := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.trans (G.dstep_ureach hstep)

theorem acyclic_no_loop (h : G.Acyclic) (e : E) :
    G.source e ≠ G.target e := by
  intro heq
  apply h (G.source e)
  exact Relation.TransGen.single ⟨e, rfl, heq.symm⟩

theorem dreach_antisymm (h : G.Acyclic) {a b : V}
    (hab : G.DReach a b) (hba : G.DReach b a) : a = b := by
  rcases Relation.ReflTransGen.cases_head hab with heq | ⟨c, hac, hcb⟩
  · exact heq
  · exact False.elim (h a (Relation.TransGen.head' hac (hcb.trans hba)))

/-- A directed walk avoiding a vertex, including its two endpoints. -/
def AvoidReach (blocked a b : V) : Prop :=
  a ≠ blocked ∧ b ≠ blocked ∧
  Relation.ReflTransGen (fun x y => G.DStep x y ∧ x ≠ blocked ∧ y ≠ blocked) a b

def Dominates (root blocked a : V) : Prop := ¬ G.AvoidReach blocked root a

theorem root_dominates (root a : V) : G.Dominates root root a := by
  intro h
  exact h.1 rfl

theorem self_dominates (root a : V) : G.Dominates root a a := by
  intro h
  exact h.2.1 rfl

section FiniteDegree
variable [Fintype E] [DecidableEq V]

def inDegree (a : V) : Nat :=
  (Finset.univ.filter (fun e => G.target e = a)).card

def outDegree (a : V) : Nat :=
  (Finset.univ.filter (fun e => G.source e = a)).card

def IsHybrid (a : V) : Prop := G.inDegree a = 2 ∧ G.outDegree a = 1

end FiniteDegree
end EdgeGraph

/-- Raw finite rooted binary phylogenetic data with the source LSA condition.
`rooted` is ordinary reachability from the root, not a decomposition premise.
This structure deliberately does NOT claim galledness, level, or planarity.
-/
structure RootedBinary (V : Type u) (E : Type v) (X : Type w)
    [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] where
  graph : EdgeGraph V E
  root : V
  leaf : X ↪ V
  at_least_two_taxa : 2 ≤ Fintype.card X
  root_degrees : graph.inDegree root = 0 ∧ graph.outDegree root = 2
  leaf_degrees : ∀ x, graph.inDegree (leaf x) = 1 ∧ graph.outDegree (leaf x) = 0
  internal_degrees : ∀ a, a ≠ root → (∀ x, leaf x ≠ a) →
    (graph.inDegree a = 1 ∧ graph.outDegree a = 2) ∨ graph.IsHybrid a
  acyclic : graph.Acyclic
  rooted : ∀ a, graph.DReach root a
  least_stable : ∀ a, (∀ x, graph.Dominates root a (leaf x)) → a = root

namespace RootedBinary
variable {V : Type u} {E : Type v} {X : Type w}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem leaf_ne_root (x : X) : N.leaf x ≠ N.root := by
  intro heq
  have h := (N.leaf_degrees x).2
  rw [heq, N.root_degrees.2] at h
  cases h

theorem underlying_connected (a b : V) :
    N.graph.UReach (fun _ => True) a b :=
  (N.graph.ureach_symm (N.graph.dreach_ureach (N.rooted a))).trans
    (N.graph.dreach_ureach (N.rooted b))

theorem unique_common_dominator {a : V}
    (h : ∀ x, N.graph.Dominates N.root a (N.leaf x)) : a = N.root :=
  N.least_stable a h

end RootedBinary
end Nanuq.Source







end FullContextModule0

section FullContextModule1




/-!
Bounded executable reachability used by the original edge-ID admission tests.
Contributor: dot, 2026-10-09. Ordinary finite saturation, without a decision
oracle. The bound is the actual finite vertex count.
-/
namespace GProgram.G7.FiniteReachability
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (R : V → V → Prop) [DecidableRel R]

def grow (s : Finset V) : Finset V :=
  s ∪ Finset.univ.filter (fun b => ∃ a ∈ s, R a b)

def reached (a : V) : ℕ → Finset V
  | 0 => {a}
  | n+1 => grow R (reached a n)

theorem subset_grow (s : Finset V) : s ⊆ grow R s := Finset.subset_union_left

theorem grow_mono {s t : Finset V} (h : s ⊆ t) : grow R s ⊆ grow R t := by
  intro b hb
  rcases Finset.mem_union.mp hb with hb | hb
  · exact Finset.mem_union_left _ (h hb)
  · obtain ⟨a,ha,hr⟩ := (Finset.mem_filter.mp hb).2
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,h ha,hr⟩)

theorem reached_step (a : V) (n : ℕ) : reached R a n ⊆ reached R a (n+1) := subset_grow R _

theorem reached_mono (a : V) {m n : ℕ} (h : m ≤ n) : reached R a m ⊆ reached R a n := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | @step n h ih => exact Finset.Subset.trans ih (reached_step R a n)

theorem self_mem (a : V) (n : ℕ) : a ∈ reached R a n :=
  reached_mono R a (Nat.zero_le n) (by simp [reached])

theorem reached_sound (a : V) (n : ℕ) {b : V} (h : b ∈ reached R a n) :
    Relation.ReflTransGen R a b := by
  induction n generalizing b with
  | zero => have he : b = a := by simpa [reached] using h
            subst b; exact .refl
  | succ n ih =>
    rcases Finset.mem_union.mp h with hb | hb
    · exact ih hb
    · obtain ⟨c,hc,hr⟩ := (Finset.mem_filter.mp hb).2
      exact (ih hc).tail hr

theorem stable_later (a : V) {k : ℕ} (h : reached R a k = reached R a (k+1))
    (j : ℕ) : reached R a (k+j) = reached R a k := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      reached R a (k+(j+1)) = grow R (reached R a (k+j)) := by rw [Nat.add_succ, reached]
      _ = grow R (reached R a k) := congrArg (grow R) ih
      _ = reached R a k := h.symm

theorem exists_stable (a : V) : ∃ k ≤ Fintype.card V,
    reached R a k = reached R a (k+1) := by
  by_contra hn
  have hneq : ∀ k ≤ Fintype.card V, reached R a k ≠ reached R a (k+1) := by
    intro k hk he
    exact hn ⟨k,hk,he⟩
  have hc : ∀ k ≤ Fintype.card V, k+1 ≤ (reached R a k).card := by
    intro k
    induction k with
    | zero => intro _; simp [reached]
    | succ k ih =>
      intro hk
      have ht : (reached R a k).card < (reached R a (k+1)).card :=
        Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr
          ⟨reached_step R a k, hneq k (by omega)⟩)
      have hi := ih (by omega)
      omega
  have hi := hc (Fintype.card V) (by omega)
  have hb := Finset.card_le_univ (reached R a (Fintype.card V))
  omega

theorem reached_complete (a b : V) (h : Relation.ReflTransGen R a b) :
    b ∈ reached R a (Fintype.card V) := by
  obtain ⟨k,hk,hs⟩ := exists_stable R a
  have hc : ∀ x y, x ∈ reached R a k → R x y → y ∈ reached R a k := by
    intro x y hx hr
    rw [hs]
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,hx,hr⟩)
  have hm : b ∈ reached R a k := by
    induction h with
    | refl => exact self_mem R a k
    | tail _ hr ih => exact hc _ _ ih hr
  exact reached_mono R a hk hm

theorem reached_iff (a b : V) : b ∈ reached R a (Fintype.card V) ↔
    Relation.ReflTransGen R a b := ⟨reached_sound R a _, reached_complete R a b⟩

def decideReach (a b : V) : Decidable (Relation.ReflTransGen R a b) :=
  decidable_of_iff _ (reached_iff R a b)



end GProgram.G7.FiniteReachability

end FullContextModule1

section FullContextModule2




/-!
# Original-hybrid pulse: coins index live ancestors, not original copies

New assumption stress test: dot's dedicated Lean lane, 2026-10-01.
The pulse names one actual original hybrid and its two original incoming edge
IDs. A current ancestral forest token can contain several original copies.
Independent inheritance supplies one coin to that LIVE token. This primitive
cannot split copies whose ancestors have already coalesced.

This does not construct the whole coalescent source process or prove all-copy
projectivity. The compiler must still establish that its current forest state
has the claimed ancestor map and that original IDs/parameters/registers are
held fixed. The exact finite wrong-pulse control below checks that requirement.
-/

namespace GProgram.G2

open Nanuq.Source

variable {V E X Copy L : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- One named actual original hybrid with the two legal original parent edges. -/
structure OriginalHybridParents (N : RootedBinary V E X) where
  hybrid : V
  isHybrid : N.graph.IsHybrid hybrid
  parent0 : E
  parent1 : E
  target0 : N.graph.target parent0 = hybrid
  target1 : N.graph.target parent1 = hybrid
  different : parent0 ≠ parent1

def OriginalHybridParents.parent {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (bit : Bool) : E :=
  if bit then H.parent1 else H.parent0

theorem OriginalHybridParents.parent_injective {N : RootedBinary V E X}
    (H : OriginalHybridParents N) : Function.Injective H.parent := by
  intro a b hab
  cases a <;> cases b
  · rfl
  · exact False.elim (H.different (by simpa [parent] using hab))
  · exact False.elim (H.different (by simpa [parent] using hab.symm))
  · rfl

/-- Current original-copy membership in each live ancestral forest token. -/
structure LiveAncestry (Copy L : Type*) where
  ancestor : Copy → L
  surjective : Function.Surjective ancestor

def routedParent {N : RootedBinary V E X} (H : OriginalHybridParents N)
    (state : LiveAncestry Copy L) (coin : L → Bool) (copy : Copy) : E :=
  H.parent (coin (state.ancestor copy))

/-- A source-mode independent pulse preserves an already merged ancestral
forest token. This holds for every coin realization, not only on average. -/
theorem coalesced_copies_cannot_split {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (state : LiveAncestry Copy L) (coin : L → Bool)
    {x y : Copy} (hxy : state.ancestor x = state.ancestor y) :
    routedParent H state coin x = routedParent H state coin y := by
  simp only [routedParent, hxy]

/-- The pulse exposes exactly the live-ancestor coin. Original parent labels
cannot be silently merged or reinterpreted as a compressed actuator ID. -/
theorem routed_parent_eq_iff_live_coin_eq {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (state : LiveAncestry Copy L) (coin : L → Bool)
    (x y : Copy) :
    routedParent H state coin x = routedParent H state coin y ↔
      coin (state.ancestor x) = coin (state.ancestor y) := by
  exact H.parent_injective.eq_iff

def mergedPair : LiveAncestry Bool Unit :=
  ⟨fun _ => (), by intro u; cases u; exact ⟨false, rfl⟩⟩

/-- A per-original-copy assignment can fail to factor through the actual
single live ancestor after the pair's merger. -/
theorem opposite_copy_bits_are_not_a_live_pulse :
    ¬ ∃ coin : Unit → Bool, ∀ copy : Bool, coin (mergedPair.ancestor copy) = copy := by
  rintro ⟨coin, hcoin⟩
  have hf := hcoin false
  have ht := hcoin true
  have h : (false : Bool) = true := hf.symm.trans ht
  cases h

def bitWeight (p : ℚ) (bit : Bool) : ℚ := if bit then 1 - p else p

/-- Incorrect pulse: one independent coin for each original copy, even though
they currently share one live ancestral forest token. -/
def perCopyPulse (p : ℚ) (a b : Bool) : ℚ := bitWeight p a * bitWeight p b

/-- Correct single-live-ancestor pulse, lifted back to its original copy labels. -/
def oneLivePulse (p : ℚ) (a b : Bool) : ℚ :=
  if a = b then bitWeight p a else 0

theorem perCopyPulse_normalized (p : ℚ) :
    perCopyPulse p false false + perCopyPulse p false true +
    perCopyPulse p true false + perCopyPulse p true true = 1 := by
  simp [perCopyPulse, bitWeight]
  ring

theorem oneLivePulse_normalized (p : ℚ) :
    oneLivePulse p false false + oneLivePulse p false true +
    oneLivePulse p true false + oneLivePulse p true true = 1 := by
  simp [oneLivePulse, bitWeight]

theorem wrong_pulse_split_mass (p : ℚ) :
    perCopyPulse p false true + perCopyPulse p true false = 2 * p * (1 - p) ∧
    oneLivePulse p false true + oneLivePulse p true false = 0 := by
  constructor
  · simp [perCopyPulse, bitWeight]
    ring
  · simp [oneLivePulse]

theorem fair_copy_pulse_splits_merged_ancestor :
    perCopyPulse (1 / 2) false true + perCopyPulse (1 / 2) true false = 1 / 2 ∧
    oneLivePulse (1 / 2) false true + oneLivePulse (1 / 2) true false = 0 := by
  exact ⟨by norm_num [perCopyPulse, bitWeight], by simp [oneLivePulse]⟩







end GProgram.G2

end FullContextModule2

section FullContextModule3









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





























end GProgram.SourceForest

end FullContextModule3

section FullContextModule4






/-!
Selected-label visible-pair bijection for the actual labelled source state.

Current ancestors need not be selected original representatives. They are kept
exactly when their genealogy contains a selected original label. The validity
theorem makes their nonempty selected blocks injective, so pair rates transfer
without multiplicities. Ordered pairs receive rate 1/2, hence each unordered
visible pair receives rate 1.

This is the actual-state combinatorial generator ingredient. It does not yet
prove matrix-exponential kernel intertwining, holding-time projectivity,
four-taxon pruning, or the all-copy G4 normal form.
-/

namespace GProgram.SourceForestKingmanProjection

open GProgram.SourceForest

section FinitePairBijection

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def pairMap (f : α → β) (p : α × α) : β × β := (f p.1, f p.2)

theorem image_offDiag_eq (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b) :
    s.offDiag.image (pairMap f) = (s.image f).offDiag := by
  ext p
  rcases p with ⟨x, y⟩
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨⟨a, b⟩, hab, heq⟩
    rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, hne⟩
    have hx : f a = x := congrArg Prod.fst heq
    have hy : f b = y := congrArg Prod.snd heq
    refine Finset.mem_offDiag.mpr ⟨Finset.mem_image.mpr ⟨a, ha, hx⟩,
      Finset.mem_image.mpr ⟨b, hb, hy⟩, ?_⟩
    intro hxy
    exact hne (hf a ha b hb (hx.trans (hxy.trans hy.symm)))
  · intro h
    rcases Finset.mem_offDiag.mp h with ⟨hx, hy, hne⟩
    rcases Finset.mem_image.mp hx with ⟨a, ha, hax⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, hby⟩
    refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, ?_⟩, ?_⟩
    · intro hab
      exact hne (hax.symm.trans ((congrArg f hab).trans hby))
    · apply Prod.ext
      · exact hax
      · exact hby

theorem pairMap_injective_on_offDiag (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    {p q : α × α} (hp : p ∈ s.offDiag) (hq : q ∈ s.offDiag)
    (heq : pairMap f p = pairMap f q) : p = q := by
  rcases Finset.mem_offDiag.mp hp with ⟨hp1, hp2, _⟩
  rcases Finset.mem_offDiag.mp hq with ⟨hq1, hq2, _⟩
  apply Prod.ext
  · exact hf p.1 hp1 q.1 hq1 (congrArg Prod.fst heq)
  · exact hf p.2 hp2 q.2 hq2 (congrArg Prod.snd heq)

theorem each_projected_pair_has_unique_original (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    (p : β × β) (hp : p ∈ (s.image f).offDiag) :
    ∃! q : α × α, q ∈ s.offDiag ∧ pairMap f q = p := by
  have hmem : p ∈ s.offDiag.image (pairMap f) := by
    rw [image_offDiag_eq s f hf]
    exact hp
  rcases Finset.mem_image.mp hmem with ⟨q, hq, heq⟩
  refine ⟨q, ⟨hq, heq⟩, ?_⟩
  intro r hr
  exact pairMap_injective_on_offDiag s f hf hr.1 hq (hr.2.trans heq.symm)

theorem projected_pair_sum (s : Finset α) (f : α → β)
    (hf : ∀ a ∈ s, ∀ b ∈ s, f a = f b → a = b)
    (w : β × β → ℝ) :
    (∑ p ∈ s.offDiag, w (pairMap f p)) =
      ∑ q ∈ (s.image f).offDiag, w q := by
  rw [← image_offDiag_eq s f hf]
  rw [Finset.sum_image]
  exact fun p hp q hq h => pairMap_injective_on_offDiag s f hf hp hq h

end FinitePairBijection

section ActualSource

variable {V E Copy : Type*} [DecidableEq V] [DecidableEq E]
  [Fintype V] [Fintype E] [DecidableEq Copy] [Fintype Copy]

def visibleActiveRoots (s : State V E Copy) (keep active : Finset Copy) : Finset Copy :=
  active.filter (fun a => (selectedBlock s keep a).Nonempty)

def selectedActiveBlocks (s : State V E Copy) (keep active : Finset Copy) : Finset (Finset Copy) :=
  (visibleActiveRoots s keep active).image (selectedBlock s keep)

theorem selectedBlock_injective_on_visibleActive
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) :
    ∀ a ∈ visibleActiveRoots s keep active,
      ∀ b ∈ visibleActiveRoots s keep active,
        selectedBlock s keep a = selectedBlock s keep b → a = b := by
  intro a ha b hb heq
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hav : a ∈ visibleAncestors s keep := by
    rw [mem_visibleAncestors]
    exact ⟨hactive ha'.1, ha'.2⟩
  have hbv : b ∈ visibleAncestors s keep := by
    rw [mem_visibleAncestors]
    exact ⟨hactive hb'.1, hb'.2⟩
  exact selectedBlock_injective_on_visible s hs keep hav hbv heq

theorem source_visible_pair_image
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) :
    (visibleActiveRoots s keep active).offDiag.image (pairMap (selectedBlock s keep)) =
      (selectedActiveBlocks s keep active).offDiag := by
  exact image_offDiag_eq (visibleActiveRoots s keep active) (selectedBlock s keep)
    (selectedBlock_injective_on_visibleActive s hs keep active hactive)

theorem source_visible_pair_unique_preimage
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep active).offDiag) :
    ∃! q : Copy × Copy, q ∈ (visibleActiveRoots s keep active).offDiag ∧
      pairMap (selectedBlock s keep) q = p := by
  exact each_projected_pair_has_unique_original (visibleActiveRoots s keep active)
    (selectedBlock s keep)
    (selectedBlock_injective_on_visibleActive s hs keep active hactive) p hp

noncomputable def visiblePairGenerator
    (s : State V E Copy) (keep active : Finset Copy)
    (increment : Finset Copy × Finset Copy → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ (visibleActiveRoots s keep active).offDiag,
    increment (pairMap (selectedBlock s keep) p)

noncomputable def projectedPairGenerator
    (s : State V E Copy) (keep active : Finset Copy)
    (increment : Finset Copy × Finset Copy → ℝ) : ℝ :=
  (1 / 2) * ∑ p ∈ (selectedActiveBlocks s keep active).offDiag, increment p

theorem actual_source_visible_generator_identity
    (s : State V E Copy) (hs : Valid s) (keep active : Finset Copy)
    (hactive : active ⊆ s.live) (increment : Finset Copy × Finset Copy → ℝ) :
    visiblePairGenerator s keep active increment =
      projectedPairGenerator s keep active increment := by
  unfold visiblePairGenerator projectedPairGenerator selectedActiveBlocks
  rw [projected_pair_sum (visibleActiveRoots s keep active) (selectedBlock s keep)
    (selectedBlock_injective_on_visibleActive s hs keep active hactive) increment]

end ActualSource

end GProgram.SourceForestKingmanProjection




end FullContextModule4

section FullContextModule5


/-!
Source-population wrapper for the selected-label Kingman pair bijection.

Active operands are now computed from the actual state at one original edge or
the retained root population. Every candidate pair is proved LegalMerge in the
existing source semantics, and every projected nonempty-block pair has a unique
original legal preimage. Invisible representatives are not required to belong
to the selected label panel.

This proves the visible pair-rate ingredient on actual source-legal operands.
The silent-merger/pruned-genealogy generator equation and transition-semigroup
projectivity remain separate obligations.
-/

namespace GProgram.SourceForestKingmanPopulationProjection

open GProgram.SourceForest GProgram.SourceForestKingmanProjection

variable {V E Copy : Type*} [DecidableEq V] [DecidableEq E]
  [Fintype V] [Fintype E] [DecidableEq Copy] [Fintype Copy]

def populationRoots (s : State V E Copy) (place : Location V E) : Finset Copy :=
  s.live.filter (fun a => s.location a = place)

theorem populationRoots_subset_live (s : State V E Copy) (place : Location V E) :
    populationRoots s place ⊆ s.live := by
  intro a ha
  exact (Finset.mem_filter.mp ha).1

theorem population_pair_is_source_legal
    (s : State V E Copy) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v)
    {a b : Copy} (hab : (a, b) ∈ (populationRoots s place).offDiag) :
    LegalMerge s a b := by
  rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, hne⟩
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  refine ⟨ha'.1, hb'.1, hne, ha'.2.trans hb'.2.symm, ?_⟩
  intro v hv
  exact hplace v (ha'.2.symm.trans hv)

theorem visible_population_pair_is_source_legal
    (s : State V E Copy) (keep : Finset Copy) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v)
    {a b : Copy}
    (hab : (a, b) ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag) :
    LegalMerge s a b := by
  rcases Finset.mem_offDiag.mp hab with ⟨ha, hb, hne⟩
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact population_pair_is_source_legal s place hplace
    (Finset.mem_offDiag.mpr ⟨ha'.1, hb'.1, hne⟩)

theorem projected_population_pair_has_unique_legal_preimage
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy)
    (place : Location V E) (hplace : ∀ v, place ≠ Location.node v)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep (populationRoots s place)).offDiag) :
    ∃! q : Copy × Copy,
      q ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag ∧
      pairMap (selectedBlock s keep) q = p ∧ LegalMerge s q.1 q.2 := by
  obtain ⟨q, hq, huniq⟩ := source_visible_pair_unique_preimage s hs keep
    (populationRoots s place) (populationRoots_subset_live s place) p hp
  have hlegal : LegalMerge s q.1 q.2 :=
    visible_population_pair_is_source_legal s keep place hplace hq.1
  refine ⟨q, ⟨hq.1, hq.2, hlegal⟩, ?_⟩
  intro r hr
  exact huniq r ⟨hr.1, hr.2.1⟩

theorem actual_population_visible_generator_identity
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy)
    (place : Location V E) (increment : Finset Copy × Finset Copy → ℝ) :
    visiblePairGenerator s keep (populationRoots s place) increment =
      projectedPairGenerator s keep (populationRoots s place) increment := by
  exact actual_source_visible_generator_identity s hs keep (populationRoots s place)
    (populationRoots_subset_live s place) increment

theorem edge_projected_pair_has_unique_legal_preimage
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy) (e : E)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep (populationRoots s (Location.edge e))).offDiag) :
    ∃! q : Copy × Copy,
      q ∈ (visibleActiveRoots s keep (populationRoots s (Location.edge e))).offDiag ∧
      pairMap (selectedBlock s keep) q = p ∧ LegalMerge s q.1 q.2 := by
  apply projected_population_pair_has_unique_legal_preimage s hs keep (Location.edge e)
    (fun v h => by cases h) p hp

theorem root_projected_pair_has_unique_legal_preimage
    (s : State V E Copy) (hs : Valid s) (keep : Finset Copy) (root : V)
    (p : Finset Copy × Finset Copy)
    (hp : p ∈ (selectedActiveBlocks s keep
      (populationRoots s (Location.rootPopulation root))).offDiag) :
    ∃! q : Copy × Copy,
      q ∈ (visibleActiveRoots s keep (populationRoots s (Location.rootPopulation root))).offDiag ∧
      pairMap (selectedBlock s keep) q = p ∧ LegalMerge s q.1 q.2 := by
  apply projected_population_pair_has_unique_legal_preimage s hs keep
    (Location.rootPopulation root) (fun v h => by cases h) p hp

end GProgram.SourceForestKingmanPopulationProjection





end FullContextModule5

section FullContextModule6


/-!
# Silent original-population mergers under actual genealogy pruning

Contributor: dot, 2026-10-02. This fills the silent-merger component of the
inherited actual source generator/projectivity gate. The readout retains each
selected original copy's whole pruned genealogy, its ORIGINAL population and
the original shared register. Representative IDs may be invisible; they are
not substituted for selected labels. Source-legal mergers involving at most
one visible operand leave this readout unchanged. Transition-semigroup and
whole calendar/pulse projectivity are subsequent obligations.
-/
namespace UnifiedLean.Source.SourceForestSilentPruning
open GProgram.SourceForest
open scoped Classical
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

lemma genealogy_leaves_nonempty (t : Genealogy Copy) : t.leaves.Nonempty := by
  induction t with
  | leaf x => exact ⟨x,Finset.mem_singleton_self x⟩
  | graft a b ih _ =>
      obtain ⟨x,hx⟩ := ih
      exact ⟨x,Finset.mem_union.mpr (Or.inl hx)⟩

lemma optionLeaves_empty_iff_none (t : Option (Genealogy Copy)) :
    Genealogy.optionLeaves t = ∅ ↔ t = none := by
  cases t with
  | none => simp [Genealogy.optionLeaves]
  | some t =>
      simp only [Genealogy.optionLeaves,Option.some_ne_none,iff_false]
      exact (genealogy_leaves_nonempty t).ne_empty

lemma prune_none_iff_no_selected_leaves (keep : Finset Copy) (t : Genealogy Copy) :
    t.prune keep = none ↔ t.leaves ∩ keep = ∅ := by
  rw [← optionLeaves_empty_iff_none, Genealogy.prune_leaves]

/-- Selected copies retain full pruned merger subtrees, not just block counts. -/
noncomputable def selectedGenealogy (s : State V E Copy) (keep : Finset Copy)
    (x : Copy) : Option (Genealogy Copy) :=
  if x ∈ keep then (s.genealogy (s.ancestor x)).prune keep else none

noncomputable def selectedLocation (s : State V E Copy) (keep : Finset Copy)
    (x : Copy) : Option (Location V E) :=
  if x ∈ keep then some (copyLocation s x) else none

@[ext] structure SelectedView (V E Copy : Type*) where
  genealogy : Copy → Option (Genealogy Copy)
  population : Copy → Option (Location V E)
  register : V → Bool

noncomputable def selectedView (s : State V E Copy) (keep : Finset Copy) :
    SelectedView V E Copy where
  genealogy := selectedGenealogy s keep
  population := selectedLocation s keep
  register := s.register

lemma selected_label_not_in_invisible_operand (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {l x : Copy} (hl : l ∈ s.live)
    (hi : (s.genealogy l).prune keep = none) (hx : x ∈ keep) : s.ancestor x ≠ l := by
  intro heq
  have he : (s.genealogy l).leaves ∩ keep = ∅ :=
    (prune_none_iff_no_selected_leaves keep _).mp hi
  have hm : x ∈ (s.genealogy l).leaves ∩ keep :=
    Finset.mem_inter.mpr ⟨(hs.leaf_fiber l hl x).mpr heq,hx⟩
  rw [he] at hm
  exact Finset.notMem_empty _ hm

/-- Invisible operand means exactly an empty selected genealogy, not an
original representative ID outside keep. -/
lemma invisible_operand_iff_pruned_none (s : State V E Copy) (keep : Finset Copy)
    (l : Copy) : ¬ (selectedBlock s keep l).Nonempty ↔
      (s.genealogy l).prune keep = none := by
  rw [prune_none_iff_no_selected_leaves]
  exact Finset.not_nonempty_iff_eq_empty

/-- Full selected genealogy maps are invariant under a source-legal merger
with at least one invisible operand. -/
theorem selectedGenealogy_merge_silent (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hi : (s.genealogy a).prune keep = none ∨ (s.genealogy b).prune keep = none) :
    selectedGenealogy (merge s a b) keep = selectedGenealogy s keep := by
  funext x
  by_cases hx : x ∈ keep
  · simp only [selectedGenealogy,if_pos hx]
    by_cases hxb : s.ancestor x = b
    · simp only [merge,hxb,if_true,Genealogy.prune]
      rcases hi with ha | hb
      · simp [ha,Genealogy.joinPruned]
      · exact False.elim ((selected_label_not_in_invisible_operand s hs keep
          hm.second_live hb hx) hxb)
    · by_cases hxa : s.ancestor x = a
      · simp only [merge,if_neg hxb,hxa,if_true,Genealogy.prune]
        rcases hi with ha | hb
        · exact False.elim ((selected_label_not_in_invisible_operand s hs keep
            hm.first_live ha hx) hxa)
        · cases hp : (s.genealogy a).prune keep <;> simp [Genealogy.prune,hb,hp,Genealogy.joinPruned]
      · simp [merge,hxb,hxa]
  · simp only [selectedGenealogy,if_neg hx]

theorem selectedLocation_merge_unchanged (s : State V E Copy) (keep : Finset Copy)
    {a b : Copy} (hm : LegalMerge s a b) :
    selectedLocation (merge s a b) keep = selectedLocation s keep := by
  funext x
  unfold selectedLocation
  rw [merge_population_preserved s hm]

/-- Actual pruned forest/population/register state is unchanged. Silent
mergers are therefore zero terms in every readout's source generator. -/
theorem selectedView_merge_silent (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hi : ¬ (selectedBlock s keep a).Nonempty ∨ ¬ (selectedBlock s keep b).Nonempty) :
    selectedView (merge s a b) keep = selectedView s keep := by
  have hi' : (s.genealogy a).prune keep = none ∨ (s.genealogy b).prune keep = none :=
    hi.imp (invisible_operand_iff_pruned_none s keep a).mp
      (invisible_operand_iff_pruned_none s keep b).mp
  apply SelectedView.ext
  · exact selectedGenealogy_merge_silent s hs keep hm hi'
  · exact selectedLocation_merge_unchanged s keep hm
  · rfl

/-- The zero increment is derived from the ORIGINAL source merger/pruning
semantics, not postulated by a projected generator interface. -/
theorem silent_merger_readout_increment_zero (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hi : ¬ (selectedBlock s keep a).Nonempty ∨ ¬ (selectedBlock s keep b).Nonempty)
    (f : SelectedView V E Copy → ℝ) :
    f (selectedView (merge s a b) keep) - f (selectedView s keep) = 0 := by
  rw [selectedView_merge_silent s hs keep hm hi,sub_self]








end UnifiedLean.Source.SourceForestSilentPruning

end FullContextModule6

section FullContextModule7



/-!
# Constructed finite encoding of all well-labelled original-copy genealogies

Contributor: dot, 2026-10-02. The existing actual source genealogy datatype is
encoded, not replaced by a fitted finite-state model. A well-labelled tree's
height is strictly below its number of distinct original leaves, hence below
the finite original copy cap. The bounded code is constructed with a proved
left inverse. This supplies a genuine finite-state ingredient for the next
positive-rate source-kernel/semigroup construction; no stochastic closure is
claimed by this datatype lemma.
-/
namespace UnifiedLean.Source.FiniteGenealogyEncoding
open GProgram.SourceForest
open scoped Classical
variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]

def genealogyHeight : Genealogy Copy → Nat
  | .leaf _ => 0
  | .graft a b => max (genealogyHeight a) (genealogyHeight b)+1

/-- Every binary shape up to bounded height, with its ORIGINAL copy labels. -/
def TreeCode (Copy : Type*) : Nat → Type _
  | 0 => Copy
  | n+1 => Copy ⊕ (TreeCode Copy n × TreeCode Copy n)

instance treeCodeFintype : ∀ n : Nat, Fintype (TreeCode Copy n)
  | 0 => inferInstanceAs (Fintype Copy)
  | n+1 => by
      letI := treeCodeFintype n
      change Fintype (Copy ⊕ (TreeCode Copy n × TreeCode Copy n))
      infer_instance

def decodeTree : (n : Nat) → TreeCode Copy n → Genealogy Copy
  | 0,x => .leaf x
  | n+1,.inl x => .leaf x
  | n+1,.inr (a,b) => .graft (decodeTree n a) (decodeTree n b)

def encodeTree : (n : Nat) → (t : Genealogy Copy) → genealogyHeight t ≤ n → TreeCode Copy n
  | 0,.leaf x,_ => x
  | 0,.graft a b,h => False.elim (by simp [genealogyHeight] at h)
  | n+1,.leaf x,_ => .inl x
  | n+1,.graft a b,h => .inr
      (encodeTree n a (by simp only [genealogyHeight] at h; omega),
       encodeTree n b (by simp only [genealogyHeight] at h; omega))

lemma decode_encode (n : Nat) (t : Genealogy Copy) (h : genealogyHeight t ≤ n) :
    decodeTree n (encodeTree n t h) = t := by
  induction n generalizing t with
  | zero =>
      cases t with
      | leaf x => rfl
      | graft a b => simp [genealogyHeight] at h
  | succ n ih =>
      cases t with
      | leaf x => rfl
      | graft a b =>
          simp only [encodeTree,decodeTree]
          rw [ih,ih]

abbrev HeightBoundedTree (Copy : Type*) (n : Nat) :=
  {t : Genealogy Copy // genealogyHeight t ≤ n}

noncomputable instance heightBoundedTreeFintype (n : Nat) :
    Fintype (HeightBoundedTree Copy n) :=
  Fintype.ofInjective (fun t : HeightBoundedTree Copy n => encodeTree n t.val t.property) (by
    intro a b h
    apply Subtype.ext
    have hh := congrArg (decodeTree n) h
    simpa only [decode_encode] using hh)

/-- Disjoint original labels, not a supplied shape/hidden graph budget, bound
the tree height. This covers every actually valid current source genealogy. -/
theorem wellLabelled_height_lt_leaves (t : Genealogy Copy) (ht : t.WellLabelled) :
    genealogyHeight t < t.leaves.card := by
  induction t with
  | leaf x => simp [genealogyHeight,Genealogy.leaves]
  | graft a b iha ihb =>
      obtain ⟨ha,hb,hd⟩ := ht
      have hA := iha ha
      have hB := ihb hb
      simp only [genealogyHeight,Genealogy.leaves,Finset.card_union_of_disjoint hd]
      omega

theorem wellLabelled_height_below_copy_cap (t : Genealogy Copy) (ht : t.WellLabelled) :
    genealogyHeight t < Fintype.card Copy :=
  (wellLabelled_height_lt_leaves t ht).trans_le (Finset.card_le_univ t.leaves)

abbrev WellLabelledTree (Copy : Type*) [DecidableEq Copy] := {t : Genealogy Copy // t.WellLabelled}

/-- Actual well-labelled genealogy space is finite by the constructed code. -/
noncomputable instance wellLabelledTreeFintype : Fintype (WellLabelledTree Copy) :=
  Fintype.ofInjective
    (fun t : WellLabelledTree Copy =>
      (⟨t.val,(wellLabelled_height_below_copy_cap t.val t.property).le⟩ :
        HeightBoundedTree Copy (Fintype.card Copy)))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun t : HeightBoundedTree Copy (Fintype.card Copy) => t.val) h)

/-- An ACTUAL existing live source genealogy supplies its own bounded code. -/
noncomputable def liveGenealogyCode {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (l : {l // l ∈ s.live}) : TreeCode Copy (Fintype.card Copy) :=
  encodeTree _ (s.genealogy l.val)
    (wellLabelled_height_below_copy_cap _ (hs.wellLabelled l.val l.property)).le

theorem liveGenealogyCode_decodes {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (l : {l // l ∈ s.live}) :
    decodeTree (Fintype.card Copy) (liveGenealogyCode s hs l) = s.genealogy l.val :=
  decode_encode _ _ _





end UnifiedLean.Source.FiniteGenealogyEncoding

end FullContextModule7

section FullContextModule8



/-!
# Finite snapshot of the existing original labelled source state

Contributor: dot, 2026-10-02. Encodes actual live genealogies, ancestry, original
population IDs and shared registers. Only dead-representative garbage and event
history are omitted; full unranked-output genealogy is retained (with the old
internal ordered encoding). Decoding preserves the inherited source invariant
and the exact selected internal view. This is for a GIVEN finite original graph
and copy cap, not a graph-size budget, G3 recognition decision, or a stochastic
kernel/biological-law completion.
-/
namespace UnifiedLean.Source.FiniteSourceSnapshot
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.FiniteGenealogyEncoding
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

/-- Separate constructor tags keep original edge IDs and ancestral root IDs. -/
def locationEquiv : Location V E ≃ V ⊕ (E ⊕ V) where
  toFun
    | .node v => .inl v
    | .edge e => .inr (.inl e)
    | .rootPopulation v => .inr (.inr v)
  invFun
    | .inl v => .node v
    | .inr (.inl e) => .edge e
    | .inr (.inr v) => .rootPopulation v
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with v | (e | v) <;> rfl

noncomputable instance locationFintype : Fintype (Location V E) :=
  Fintype.ofEquiv (V ⊕ (E ⊕ V)) locationEquiv.symm

@[ext] structure Snapshot (V E Copy : Type*) [DecidableEq Copy] where
  live : Finset Copy
  ancestor : Copy → Copy
  genealogy : Copy → Option (WellLabelledTree Copy)
  population : Copy → Option (Location V E)
  register : V → Bool

noncomputable def snapshotEquiv : Snapshot V E Copy ≃
    (Finset Copy × (Copy → Copy) × (Copy → Option (WellLabelledTree Copy)) ×
      (Copy → Option (Location V E)) × (V → Bool)) where
  toFun s := (s.live,s.ancestor,s.genealogy,s.population,s.register)
  invFun s := ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩
  left_inv s := rfl
  right_inv s := rfl

noncomputable instance snapshotFintype : Fintype (Snapshot V E Copy) :=
  Fintype.ofEquiv _ snapshotEquiv.symm

noncomputable def encodeSnapshot (s : State V E Copy) (hs : Valid s) : Snapshot V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := if h : l ∈ s.live then some ⟨s.genealogy l,hs.wellLabelled l h⟩ else none
  population l := if l ∈ s.live then some (s.location l) else none
  register := s.register

/-- The existing State representation is reconstructed on all live operands.
Dead garbage and ranked history are irrelevant to this snapshot interface. -/
noncomputable def decodeSnapshot (root : V) (s : Snapshot V E Copy) : State V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := match s.genealogy l with
    | some t => t.val
    | none => .leaf l
  location l := match s.population l with
    | some p => p
    | none => .node root
  register := s.register
  history := []

lemma decode_encode_live_genealogy (root : V) (s : State V E Copy) (hs : Valid s)
    {l : Copy} (hl : l ∈ s.live) :
    (decodeSnapshot root (encodeSnapshot s hs)).genealogy l = s.genealogy l := by
  simp only [decodeSnapshot,encodeSnapshot,dif_pos hl]

lemma decode_encode_live_population (root : V) (s : State V E Copy) (hs : Valid s)
    {l : Copy} (hl : l ∈ s.live) :
    (decodeSnapshot root (encodeSnapshot s hs)).location l = s.location l := by
  simp only [decodeSnapshot,encodeSnapshot,if_pos hl]

/-- Every selected ORIGINAL copy still uses its actual current live ancestor. -/
lemma decode_encode_copyLocation (root : V) (s : State V E Copy) (hs : Valid s) (x : Copy) :
    copyLocation (decodeSnapshot root (encodeSnapshot s hs)) x = copyLocation s x := by
  change (decodeSnapshot root (encodeSnapshot s hs)).location (s.ancestor x) = _
  exact decode_encode_live_population root s hs (hs.ancestor_live x)

theorem decode_encode_valid (root : V) (s : State V E Copy) (hs : Valid s) :
    Valid (decodeSnapshot root (encodeSnapshot s hs)) := by
  constructor
  · exact hs.ancestor_live
  · exact hs.representative
  · intro l hl x
    change x ∈ ((decodeSnapshot root (encodeSnapshot s hs)).genealogy l).leaves ↔ s.ancestor x = l
    rw [decode_encode_live_genealogy root s hs hl]
    exact hs.leaf_fiber l hl x
  · intro l hl
    rw [decode_encode_live_genealogy root s hs hl]
    exact hs.wellLabelled l hl

/-- Same original graph, sample assignment and source populations. No source
validity/kernel equation is inserted as a new asserted contract field. -/
theorem decode_encode_sourceValid [Fintype X] (N : RootedBinary V E X)
    (sample : Copy → X) (s : State V E Copy) (hs : SourceValid N sample s) :
    SourceValid N sample (decodeSnapshot N.root (encodeSnapshot s hs.forest)) := by
  refine ⟨decode_encode_valid N.root s hs.forest,?_⟩
  intro x
  rw [decode_encode_copyLocation N.root s hs.forest x]
  exact hs.original_descendant x

/-- Snapshot encoding keeps the whole selected genealogy/population/register
interface exactly. It is not an observed-data sufficiency theorem. -/
theorem decode_encode_selectedView (root : V) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) :
    selectedView (decodeSnapshot root (encodeSnapshot s hs)) keep = selectedView s keep := by
  apply SelectedView.ext
  · funext x
    unfold selectedView selectedGenealogy
    change (if x ∈ keep then
      ((decodeSnapshot root (encodeSnapshot s hs)).genealogy (s.ancestor x)).prune keep
      else none) = _
    rw [decode_encode_live_genealogy root s hs (hs.ancestor_live x)]
  · funext x
    change (if x ∈ keep then some (copyLocation (decodeSnapshot root (encodeSnapshot s hs)) x)
      else none) = (if x ∈ keep then some (copyLocation s x) else none)
    rw [decode_encode_copyLocation root s hs x]
  · rfl

/-- Genuine finite original-source snapshot carrier, parameterized by the
unchanged original graph and SAME sample assignment. -/
abbrev AdmittedSnapshot [Fintype X] (N : RootedBinary V E X) (sample : Copy → X) :=
  {s : Snapshot V E Copy // SourceValid N sample (decodeSnapshot N.root s)}

noncomputable instance admittedSnapshotFintype [Fintype X]
    (N : RootedBinary V E X) (sample : Copy → X) : Fintype (AdmittedSnapshot N sample) := by
  unfold AdmittedSnapshot
  infer_instance

/-- Every existing actually source-valid state yields an admitted finite code. -/
noncomputable def admittedCode [Fintype X] (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) : AdmittedSnapshot N sample :=
  ⟨encodeSnapshot s hs.forest,decode_encode_sourceValid N sample s hs⟩





end UnifiedLean.Source.FiniteSourceSnapshot

end FullContextModule8

section FullContextModule9



namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

theorem dreach_preserves {P : V → Prop}
    (closed : ∀ a b, G.DStep a b → P a → P b)
    {a b : V} (hab : G.DReach a b) (ha : P a) : P b := by
  induction hab with
  | refl => exact ha
  | tail _ hstep ih => exact closed _ _ hstep ih

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem outDegree_pos_of_not_leaf {a : V} (h : ¬ ∃ x, N.leaf x = a) :
    0 < N.graph.outDegree a := by
  by_cases har : a = N.root
  · rw [har, N.root_degrees.2]
    exact Nat.zero_lt_succ 1
  · have hi := N.internal_degrees a har (fun x hx => h ⟨x, hx⟩)
    rcases hi with ht | hh
    · rw [ht.2]
      exact Nat.zero_lt_succ 1
    · rw [hh.2]
      exact Nat.zero_lt_succ 0

theorem leaf_iff_outDegree_zero (a : V) :
    (∃ x, N.leaf x = a) ↔ N.graph.outDegree a = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (N.leaf_degrees x).2
  · intro hzero
    classical
    by_contra hn
    have hp := N.outDegree_pos_of_not_leaf hn
    rw [hzero] at hp
    exact Nat.lt_irrefl 0 hp

/-- Actual descendant-leaf existence derived from finite directed acyclicity. -/
theorem every_vertex_reaches_leaf (a : V) :
    ∃ x, N.graph.DReach a (N.leaf x) := by
  classical
  let r : V → V → Prop := fun b a => Relation.TransGen N.graph.DStep a b
  haveI : IsTrans V r := ⟨fun _ _ _ hab hbc => hbc.trans hab⟩
  haveI : Std.Irrefl r := ⟨fun a => N.acyclic a⟩
  have hw : WellFounded r := Finite.wellFounded_of_trans_of_irrefl r
  refine hw.induction (C := fun v => ∃ x, N.graph.DReach v (N.leaf x)) a ?_
  intro v ih
  by_cases hl : ∃ x, N.leaf x = v
  · obtain ⟨x, rfl⟩ := hl
    exact ⟨x, .refl⟩
  · have hp := N.outDegree_pos_of_not_leaf hl
    obtain ⟨e, he⟩ := Finset.card_pos.mp hp
    have hs : N.graph.source e = v := (Finset.mem_filter.mp he).2
    have hstep : N.graph.DStep v (N.graph.target e) := ⟨e, hs, rfl⟩
    obtain ⟨x, hx⟩ := ih (N.graph.target e) (Relation.TransGen.single hstep)
    exact ⟨x, (Relation.ReflTransGen.single hstep).trans hx⟩

theorem forward_closed_contains_leaf {P : V → Prop}
    (hclosed : ∀ a b, N.graph.DStep a b → P a → P b)
    {a : V} (ha : P a) : ∃ x, P (N.leaf x) := by
  obtain ⟨x, hx⟩ := N.every_vertex_reaches_leaf a
  exact ⟨x, N.graph.dreach_preserves hclosed hx ha⟩

/-- LSA supplies a real root-to-leaf walk avoiding every non-root vertex. -/
theorem exists_leaf_avoiding_of_ne_root {a : V} (hne : a ≠ N.root) :
    ∃ x, N.graph.AvoidReach a N.root (N.leaf x) := by
  classical
  by_contra hn
  apply hne
  apply N.least_stable a
  intro x hx
  exact hn ⟨x, hx⟩

end RootedBinary
end Nanuq.Source





end FullContextModule9

section FullContextModule10


namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)

/-- Deleting one edge leaves at most two relevant sides of a connected graph. -/
theorem edge_side_cover (e : E) {a : V}
    (h : G.UReach (fun _ => True) (G.source e) a) :
    G.ReachWithout e (G.source e) a ∨ G.ReachWithout e (G.target e) a := by
  induction h with
  | refl => exact Or.inl (.refl)
  | @tail b c _ hstep ih =>
      obtain ⟨f, _, hinc⟩ := hstep
      by_cases hfe : f = e
      · subst f
        rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · apply Or.inr
          rw [← ht]
          exact .refl
        · apply Or.inl
          rw [← hs]
          exact .refl
      · rcases ih with hb | hb
        · exact Or.inl (hb.tail ⟨f, hfe, hinc⟩)
        · exact Or.inr (hb.tail ⟨f, hfe, hinc⟩)

theorem bridge_sides_disjoint {e : E} (he : G.IsBridge e) {a : V}
    (hs : G.ReachWithout e (G.source e) a)
    (ht : G.ReachWithout e (G.target e) a) : False :=
  he (hs.trans (G.ureach_symm ht))

/-- The target side of a directed bridge is closed under directed edges. -/
theorem bridge_target_forward_closed {e : E} (he : G.IsBridge e)
    {a b : V} (hab : G.DStep a b)
    (ha : G.ReachWithout e (G.target e) a) :
    G.ReachWithout e (G.target e) b := by
  obtain ⟨f, hs, ht⟩ := hab
  have hfe : f ≠ e := by
    intro hfe
    subst f
    apply he
    rw [← hs] at ha
    exact G.ureach_symm ha
  exact ha.tail ⟨f, hfe, Or.inl ⟨hs, ht⟩⟩

/-- A directed path whose endpoint is not below an edge cannot use that edge. -/
theorem dreach_without_of_no_return (e : E) {a b : V} (hab : G.DReach a b) :
    (¬ G.DReach (G.target e) b) → G.ReachWithout e a b := by
  induction hab with
  | refl => intro _; exact .refl
  | @tail b c _ hstep ih =>
      intro hno
      have hp := ih (fun h => hno (h.tail hstep))
      obtain ⟨f, hs, ht⟩ := hstep
      have hfe : f ≠ e := by
        intro hfe
        subst f
        apply hno
        rw [← ht]
        exact .refl
      exact hp.tail ⟨f, hfe, Or.inl ⟨hs, ht⟩⟩

theorem avoid_target_reach_without (e : E) {a b : V}
    (h : G.AvoidReach (G.target e) a b) : G.ReachWithout e a b := by
  rcases h with ⟨ha, hb, hw⟩
  clear ha hb
  induction hw with
  | refl => exact .refl
  | tail _ hstep ih =>
      obtain ⟨f, hs, ht⟩ := hstep.1
      have hfe : f ≠ e := by
        intro hfe
        subst f
        exact hstep.2.2 ht.symm
      exact ih.tail ⟨f, hfe, Or.inl ⟨hs, ht⟩⟩

end EdgeGraph

namespace RootedBinary
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

theorem edge_target_ne_root (e : E) : N.graph.target e ≠ N.root := by
  intro ht
  apply N.acyclic N.root
  exact Relation.TransGen.tail' (N.rooted (N.graph.source e)) ⟨e, rfl, ht⟩

theorem root_on_source_side (e : E) :
    N.graph.ReachWithout e (N.graph.source e) N.root := by
  apply N.graph.ureach_symm
  apply N.graph.dreach_without_of_no_return e (N.rooted (N.graph.source e))
  intro hreturn
  exact N.acyclic (N.graph.source e)
    (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hreturn)

theorem bridge_target_side_contains_taxon {e : E} (he : N.graph.IsBridge e) :
    ∃ x, N.graph.ReachWithout e (N.graph.target e) (N.leaf x) := by
  apply N.forward_closed_contains_leaf
    (P := fun a => N.graph.ReachWithout e (N.graph.target e) a)
  · intro a b hab ha
    exact N.graph.bridge_target_forward_closed he hab ha
  · exact Relation.ReflTransGen.refl (a := N.graph.target e)

/-- LSA excludes an empty rootward side of every bridge. -/
theorem bridge_source_side_contains_taxon (e : E) :
    ∃ x, N.graph.ReachWithout e (N.graph.source e) (N.leaf x) := by
  obtain ⟨x, hx⟩ := N.exists_leaf_avoiding_of_ne_root (N.edge_target_ne_root e)
  exact ⟨x, (N.root_on_source_side e).trans (N.graph.avoid_target_reach_without e hx)⟩

/-- Both sides of each actual cut edge contain labeled taxa. -/
theorem bridge_both_sides_contain_taxa {e : E} (he : N.graph.IsBridge e) :
    (∃ x, N.graph.ReachWithout e (N.graph.source e) (N.leaf x)) ∧
    (∃ x, N.graph.ReachWithout e (N.graph.target e) (N.leaf x)) :=
  ⟨N.bridge_source_side_contains_taxon e, N.bridge_target_side_contains_taxon he⟩

end RootedBinary
end Nanuq.Source





end FullContextModule10

section FullContextModule11


/-!
# Actual-source child-bridge graph component of G5

New proof contribution: the dot dedicated Lean lane, 2026-10-01.
The imported edge-indexed graph API and its foundations retain the original
Samuel Alexander research attribution and exact source baseline.

This file proves a graph theorem on the actual finite rooted binary source.
Parallel edge IDs are retained. There is no bounded-source replacement and
no canonical shape, switching-support, or desired biological conclusion in
the premises. The calendar/no-merger support and chronological lifting
parts of G5 are separate proof obligations.
-/

namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- The component below an actual directed bridge consists exactly of its
target's directed descendants. This is independent of inheritance mode. -/
theorem bridge_target_component_iff_descendant (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) (v : V) :
    N.graph.ReachWithout e (N.graph.target e) v ↔
      N.graph.DReach (N.graph.target e) v := by
  constructor
  · intro hv
    by_contra hn
    have hr := N.graph.dreach_without_of_no_return e (N.rooted v) hn
    have hs := (N.root_on_source_side e).trans hr
    exact N.graph.bridge_sides_disjoint he hs hv
  · intro hv
    exact N.graph.dreach_preserves
      (fun _ _ hstep hmem => N.graph.bridge_target_forward_closed he hstep hmem)
      hv (.refl)

/-- On the original source, a selected tip is in the child component iff it
descends from the child. No pruned selected-tip source is introduced. -/
theorem bridge_selected_tip_iff (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) (x : X) :
    N.graph.ReachWithout e (N.graph.target e) (N.leaf x) ↔
      N.graph.DReach (N.graph.target e) (N.leaf x) :=
  bridge_target_component_iff_descendant N he (N.leaf x)

/-- A one-child vertex has exactly one outgoing original edge identity. -/
theorem unique_child_edge (N : RootedBinary V E X) {h : V}
    (hh : N.graph.outDegree h = 1) :
    ∃! e : E, N.graph.source e = h := by
  classical
  obtain ⟨e, he, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hh
  refine ⟨e, (Finset.mem_filter.mp he).2, ?_⟩
  intro f hf
  exact hu f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩)

/-- Every genuine descendant other than the one-child vertex itself is
already a descendant of the target of its unique child edge. -/
theorem descendant_via_unique_child (N : RootedBinary V E X)
    {h v : V} (hh : N.graph.outDegree h = 1) {e : E}
    (hs : N.graph.source e = h) (hne : h ≠ v) :
    N.graph.DReach h v ↔ N.graph.DReach (N.graph.target e) v := by
  obtain ⟨f, hf, hu⟩ := unique_child_edge N hh
  have hfe : f = e := (hu e hs).symm
  subst f
  constructor
  · intro hv
    rcases Relation.ReflTransGen.cases_head hv with heq | ⟨u, hstep, huv⟩
    · exact False.elim (hne heq)
    · obtain ⟨g, hgs, hgt⟩ := hstep
      have hge := hu g hgs
      subst g
      simpa only [EdgeGraph.DReach, hgt] using huv
  · intro hv
    exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans hv

/-- The selected descendants of a hybrid are precisely its child-bridge
component, when the actual source cut-child condition is supplied. -/
theorem hybrid_descendant_component (N : RootedBinary V E X)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e) (x : X) :
    N.graph.DReach h (N.leaf x) ↔
      N.graph.ReachWithout e (N.graph.target e) (N.leaf x) := by
  have hne : h ≠ N.leaf x := by
    intro heq
    have hz := (N.leaf_degrees x).2
    rw [← heq, hh.2] at hz
    cases hz
  rw [descendant_via_unique_child N hh.2 hs hne]
  exact (bridge_selected_tip_iff N he x).symm






end GProgram.G5

end FullContextModule11

section FullContextModule12




/-!
# Calendar route test for the protective child-bridge assumption

New proof contribution: dot's dedicated Lean lane, 2026-10-01.
An original route is a finite list of original directed edge IDs, from the
original root to one selected tip. No pruned source or sampled ancestor is
substituted. An active population uses the older-side convention
age(target) <= t < age(source).

The module tests the deterministic source/calendar premise of G5. A stochastic
coalescent law, positive no-merger route probabilities, observed-germ recovery,
and the whole chronological algorithm are not encoded as hypotheses here.
-/

namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Strict original edge durations, without a source-replacement assumption. -/
structure Calendar (G : EdgeGraph V E) where
  age : V → ℝ
  edge_older : ∀ e, age (G.target e) < age (G.source e)

def Calendar.Active {G : EdgeGraph V E} (C : Calendar G) (t : ℝ) (e : E) : Prop :=
  C.age (G.target e) ≤ t ∧ t < C.age (G.source e)

/-- Explicit edge-ID paths, preserving parallel arcs. -/
inductive EdgePath (G : EdgeGraph V E) : V → V → List E → Prop
  | nil (a : V) : EdgePath G a a []
  | cons {a b : V} {e : E} {es : List E}
      (hs : G.source e = a) (rest : EdgePath G (G.target e) b es) :
      EdgePath G a b (e :: es)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.directed {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : EdgePath G a b es) : G.DReach a b := by
  induction p with
  | nil => exact .refl
  | cons hs rest ih =>
      exact (Relation.ReflTransGen.single ⟨_, hs, rfl⟩).trans ih

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.append {G : EdgeGraph V E} {a b c : V} {es fs : List E}
    (p : EdgePath G a b es) (q : EdgePath G b c fs) :
    EdgePath G a c (es ++ fs) := by
  induction p with
  | nil => exact q
  | cons hs rest ih => exact .cons hs (ih q)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem exists_edgePath_of_directed {G : EdgeGraph V E} {a b : V}
    (p : G.DReach a b) : ∃ es : List E, EdgePath G a b es := by
  induction p with
  | refl => exact ⟨[], .nil _⟩
  | @tail b c _ step ih =>
      obtain ⟨es, hp⟩ := ih
      obtain ⟨e, hs, ht⟩ := step
      have he : EdgePath G b c [e] := by
        exact .cons hs (by rw [ht]; exact .nil c)
      exact ⟨es ++ [e], hp.append he⟩

theorem original_tip_route_exists (N : RootedBinary V E X) (x : X) :
    ∃ es : List E, EdgePath N.graph N.root (N.leaf x) es :=
  exists_edgePath_of_directed (N.rooted (N.leaf x))

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem Calendar.age_le_of_directed {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} (p : G.DReach a b) : C.age b ≤ C.age a := by
  induction p with
  | refl => exact le_refl _
  | tail _ step ih =>
      obtain ⟨e, hs, ht⟩ := step
      have h := C.edge_older e
      rw [hs, ht] at h
      exact (le_of_lt h).trans ih

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.reach_without_of_not_mem {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (hne : e ∉ es) : G.ReachWithout e a b := by
  induction p with
  | nil => exact .refl
  | @cons a b f fs hs rest ih =>
      have hfe : f ≠ e := by
        intro hf
        exact hne (List.mem_cons.mpr (Or.inl hf.symm))
      have htail : e ∉ fs := fun hm => hne (List.mem_cons.mpr (Or.inr hm))
      exact (G.ureach_single ⟨f, hfe, Or.inl ⟨hs, rfl⟩⟩).trans (ih htail)

/-- Every original root-to-tip path to a downstream descendant crosses the
actual bridge edge, independent of the allowed parent choices along that path. -/
theorem bridge_mem_every_descendant_route (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) {x : X} {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es)
    (hd : N.graph.DReach (N.graph.target e) (N.leaf x)) : e ∈ es := by
  classical
  by_contra hn
  have hr := p.reach_without_of_not_mem hn
  have hs := (N.root_on_source_side e).trans hr
  have ht := (bridge_selected_tip_iff N he x).mpr hd
  exact N.graph.bridge_sides_disjoint he hs ht

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.source_age_le {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (he : e ∈ es) : C.age (G.source e) ≤ C.age a := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
      rcases List.mem_cons.mp he with hef | he
      · subst e
        rw [hs]
      · exact (ih he).trans (by
          have h := C.edge_older f
          rw [hs] at h
          exact le_of_lt h)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- Strict edge ages make the active original population edge unique along
each complete route, including the older-side convention at node ages. -/
theorem EdgePath.active_unique {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : EdgePath G a b es)
    {t : ℝ} {e f : E} (he : e ∈ es) (hf : f ∈ es)
    (hae : C.Active t e) (haf : C.Active t f) : e = f := by
  induction p with
  | nil => simp at he
  | @cons a b g gs hs rest ih =>
      rcases List.mem_cons.mp he with heg | he
      · subst e
        rcases List.mem_cons.mp hf with hfg | hf
        · exact hfg.symm
        · have hsrc := rest.source_age_le C hf
          exact False.elim (not_lt_of_ge (hsrc.trans hae.1) haf.2)
      · rcases List.mem_cons.mp hf with hfg | hf
        · subst f
          have hsrc := rest.source_age_le C he
          exact False.elim (not_lt_of_ge (hsrc.trans haf.1) hae.2)
        · exact ih he hf

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem EdgePath.target_reaches_end_of_mem {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : EdgePath G a b es) {e : E}
    (he : e ∈ es) : G.DReach (G.target e) b := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
      rcases List.mem_cons.mp he with hef | he
      · subst e
        exact rest.directed
      · exact ih he

/-- Throughout the protective child-edge interval, every descendant's original
route has exactly that edge as its active population. No law decoder is assumed. -/
theorem protective_edge_active_on_every_route (N : RootedBinary V E X)
    (C : Calendar N.graph) {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e)
    {x : X} (hd : N.graph.DReach h (N.leaf x)) {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es) {t : ℝ}
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h) :
    e ∈ es ∧ C.Active t e ∧
      ∀ f ∈ es, C.Active t f → f = e := by
  have hdown := (descendant_via_unique_child N hh.2 hs
    (by intro hx; have hz := (N.leaf_degrees x).2; rw [← hx, hh.2] at hz; cases hz)).mp hd
  have hm := bridge_mem_every_descendant_route N he p hdown
  have ha : C.Active t e := by simpa only [Calendar.Active, hs] using ht
  exact ⟨hm, ha, fun f hf hfa => p.active_unique C hf hm hfa ha⟩

/-- No route from an outside tip can visit the hybrid's child population. -/
theorem protective_edge_absent_on_outside_route (N : RootedBinary V E X)
    {h : V} {e : E} (hs : N.graph.source e = h)
    {x : X} (hout : ¬ N.graph.DReach h (N.leaf x)) {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es) : e ∉ es := by
  intro he
  apply hout
  exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans
    (p.target_reaches_end_of_mem he)

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The source's strictly positive child-edge duration gives a nonempty
protective interval, with its youngest endpoint included. -/
theorem protective_interval_nonempty {G : EdgeGraph V E} (C : Calendar G) (e : E) :
    ∃ t : ℝ, C.Active t e :=
  ⟨C.age (G.target e), le_refl _, C.edge_older e⟩

/-- Assumption stress test: under the opposite endpoint convention a first
nontrivial block in this positive interval need not be attained. -/
theorem younger_side_open_interval_has_no_first :
    ¬ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → t ≤ u := by
  rintro ⟨t, ht, ht1, hmin⟩
  have h := hmin (t / 2) (by linarith) (by linarith)
  linarith









end GProgram.G5

end FullContextModule12

section FullContextModule13


/-!
# Exact protective population block on original no-merger route families

New proof contribution: dot's dedicated Lean lane, 2026-10-01.
This tests the stronger 'exact whole block' step in G5, rather than a claim
that descendants are merely possibly co-located or contained in a larger block.

A route family contains original-tip paths on the unchanged original source.
Its existence follows from source rootedness. No assumptions concerning the
desired population-block support, gene-law identifiability, or Q/S appear as
fields. Probability/support of these route families remains a separate task.
-/

namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

structure RouteFamily (N : RootedBinary V E X) where
  edges : X → List E
  valid : ∀ x, EdgePath N.graph N.root (N.leaf x) (edges x)

theorem routeFamily_exists (N : RootedBinary V E X) : Nonempty (RouteFamily N) := by
  classical
  exact ⟨⟨fun x => Classical.choose (original_tip_route_exists N x),
    fun x => Classical.choose_spec (original_tip_route_exists N x)⟩⟩

noncomputable def selectedPopulationBlock (N : RootedBinary V E X)
    (R : RouteFamily N) (B : Finset X) (C : Calendar N.graph) (t : ℝ) (e : E) :
    Finset X := by
  classical
  exact B.filter (fun x => e ∈ R.edges x ∧ C.Active t e)

noncomputable def selectedDescendants (N : RootedBinary V E X)
    (B : Finset X) (h : V) : Finset X := by
  classical
  exact B.filter (fun x => N.graph.DReach h (N.leaf x))

/-- At every protective calendar time, the child population's selected-tip
fiber is exactly the whole selected descendant set, for every original-route
assignment, even if different tips choose hybrid parents independently. -/
theorem protective_population_block_eq (N : RootedBinary V E X)
    (R : RouteFamily N) (B : Finset X) (C : Calendar N.graph)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e) {t : ℝ}
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h) :
    selectedPopulationBlock N R B C t e = selectedDescendants N B h := by
  classical
  apply Finset.filter_congr
  intro x _
  constructor
  · intro hmem
    exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans
      ((R.valid x).target_reaches_end_of_mem hmem.1)
  · intro hd
    have hp := protective_edge_active_on_every_route N C hh hs he hd (R.valid x) ht
    exact ⟨hp.1, hp.2.1⟩




end GProgram.G5

end FullContextModule13

section FullContextModule14


/-!
# Weaker graph interface isolated by the G5 hypothesis audit

New formal generalization: dot's dedicated Lean lane, 2026-10-01.
Original edge-ID graph API and foundational lemmas retain Samuel attribution.

The bridge/descendant theorem needs only directed rootedness and acyclicity.
No LSA, binary degrees, finite vertex bound, galledness or planar embedding is
assumed. This is a genuine stronger graph statement, not a full biological Q
or split-identification theorem. Finite stochastic route-support, calendar and
chronological lifting obligations remain separate.
-/

namespace GProgram.G5.Minimal

open Nanuq.Source

variable {V E : Type*}

theorem root_source_side_of_rooted_acyclic (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) (e : E) :
    G.ReachWithout e (G.source e) root := by
  apply G.ureach_symm
  apply G.dreach_without_of_no_return e (hr (G.source e))
  intro hreturn
  exact ha (G.source e) (Relation.TransGen.head' ⟨e, rfl, rfl⟩ hreturn)

/-- Actual directed bridge components equal actual directed descendants on
every rooted acyclic edge-indexed graph, without the stronger source package. -/
theorem bridge_component_iff_descendant (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) (v : V) :
    G.ReachWithout e (G.target e) v ↔ G.DReach (G.target e) v := by
  constructor
  · intro hv
    by_contra hn
    have hroot := G.dreach_without_of_no_return e (hr v) hn
    have hs := (root_source_side_of_rooted_acyclic G root ha hr e).trans hroot
    exact G.bridge_sides_disjoint he hs hv
  · intro hv
    exact G.dreach_preserves
      (fun _ _ hstep hmem => G.bridge_target_forward_closed he hstep hmem)
      hv (.refl)




end GProgram.G5.Minimal

end FullContextModule14

section FullContextModule15



/-!
# Original bridge targets have one incoming edge occurrence

Dedicated Sol6.1 source-graph contribution. Rootedness and directed acyclicity
force every underlying bridge target to have a unique incoming original edge
ID. Parallel same-parent arcs remain distinct edge occurrences. No planar,
galled, child-cut, LSA or biological-kernel conclusion is assumed in the generic
lemma. Binary source consequences support the separate nonplanar G6 proof.
-/

namespace GProgram.G6.BridgeEntry

open Nanuq.Source

variable {V E : Type*}

theorem bridge_incoming_unique (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) {f : E} (hf : G.target f = G.target e) : f = e := by
  classical
  by_contra hne
  have hs : G.ReachWithout e (G.target e) (G.source f) :=
    G.ureach_single ⟨f,hne,Or.inr ⟨rfl,hf⟩⟩
  have hd := (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr he (G.source f)).mp hs
  exact ha (G.source f) (Relation.TransGen.head' ⟨f,rfl,hf⟩ hd)

theorem bridge_target_indegree_one (G : EdgeGraph V E) (root : V)
    [Fintype E] [DecidableEq V] (ha : G.Acyclic) (hr : ∀ v, G.DReach root v)
    {e : E} (he : G.IsBridge e) : G.inDegree (G.target e) = 1 := by
  classical
  unfold EdgeGraph.inDegree
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨e,by simp,?_⟩
  intro f hf
  exact bridge_incoming_unique G root ha hr he (Finset.mem_filter.mp hf).2

/-- Any two distinct incoming edge OCCURRENCES exclude a bridge, even if their
sources are the same vertex. This does not require binarity or finite vertices. -/
theorem two_incoming_occurrences_not_bridge (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e f : E}
    (hne : f ≠ e) (hf : G.target f = G.target e) : ¬ G.IsBridge e := by
  intro he
  exact hne (bridge_incoming_unique G root ha hr he hf)

/-- Distinct bridge edge occurrences have distinct downstream entry vertices.
This provides distinct child-cut targets/ports without a planar embedding. -/
theorem bridge_targets_injective (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) :
    Function.Injective (fun e : {e : E // G.IsBridge e} => G.target e.val) := by
  intro e f hf
  apply Subtype.ext
  exact (bridge_incoming_unique G root ha hr e.property hf.symm).symm

section OriginalSource

variable {X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem original_bridge_target_not_hybrid (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) : ¬ N.graph.IsHybrid (N.graph.target e) := by
  intro hh
  have hc := bridge_target_indegree_one N.graph N.root N.acyclic N.rooted he
  have ht : N.graph.inDegree (N.graph.target e) = 2 := hh.1
  rw [hc] at ht
  cases ht

theorem incoming_hybrid_edge_not_bridge (N : RootedBinary V E X)
    {e : E} (hh : N.graph.IsHybrid (N.graph.target e)) : ¬ N.graph.IsBridge e := by
  intro he
  exact original_bridge_target_not_hybrid N he hh

theorem original_hybrid_parents_nonbridge {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) :
    ¬ N.graph.IsBridge H.parent0 ∧ ¬ N.graph.IsBridge H.parent1 := by
  constructor
  · apply incoming_hybrid_edge_not_bridge N
    simpa only [H.target0] using H.isHybrid
  · apply incoming_hybrid_edge_not_bridge N
    simpa only [H.target1] using H.isHybrid

end OriginalSource








end GProgram.G6.BridgeEntry

end FullContextModule15

section FullContextModule16



/-!
# Actual bridge components have unique rootward entries

New proof contribution: dot's Lean source-bridge lane, 2026-10-02.
The original edge-indexed rooted acyclic graph itself implies that every
non-root bridge-deleted component has exactly one incoming bridge occurrence.
No finite size, binary degree, LSA, level, embedding or canonical component
representation is needed by the generic uniqueness proof. Together with the
cut-child nonbridge route bound this supplies genuine graph premises for the
current-component G5 argument; clocks, source probabilities and chronology are
still separate formal obligations.
-/

namespace GProgram.G5.ComponentEntries

open Nanuq.Source

variable {V E : Type*}

/-- A nonbridge-component path avoids EVERY specified bridge occurrence. -/
theorem sameBlob_avoids_bridge (G : EdgeGraph V E) {e : E}
    (he : G.IsBridge e) {a b : V} (hab : G.SameBlob a b) : G.ReachWithout e a b := by
  apply G.ureach_mono (keep := fun f => ¬ G.IsBridge f) _ hab
  intro f hf hfe
  subst f
  exact hf he

/-- Two different incoming bridges cannot enter the same actual component. -/
theorem bridge_targets_sameBlob_iff_eq (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e f : E}
    (he : G.IsBridge e) (hf : G.IsBridge f) :
    G.SameBlob (G.target e) (G.target f) ↔ e = f := by
  constructor
  · intro hblob
    have hef := (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr he
      (G.target f)).mp (sameBlob_avoids_bridge G he hblob)
    have hfe := (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr hf
      (G.target e)).mp (sameBlob_avoids_bridge G hf (G.sameBlob_symm hblob))
    have ht := G.dreach_antisymm ha hef hfe
    exact (GProgram.G6.BridgeEntry.bridge_incoming_unique G root ha hr he ht.symm).symm
  · intro h
    subst f
    exact G.sameBlob_refl _

/-- The component of the original root has no incoming bridge. -/
theorem bridge_target_not_root_component (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) : ¬ G.SameBlob (G.target e) root := by
  intro hb
  exact G.bridge_sides_disjoint he
    (GProgram.G5.Minimal.root_source_side_of_rooted_acyclic G root ha hr e)
    (sameBlob_avoids_bridge G he hb)

/-- Any original directed route either stays in one component or has a final
incoming bridge followed only by original nonbridge component connectivity. -/
theorem EdgePath.sameBlob_or_incoming_bridge {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es) :
    G.SameBlob a b ∨ ∃ e ∈ es, G.IsBridge e ∧ G.SameBlob (G.target e) b := by
  induction p with
  | nil a => exact Or.inl (G.sameBlob_refl a)
  | @cons a b e es hs rest ih =>
    rcases ih with hsame | ⟨f, hmem, hf, hfb⟩
    · by_cases he : G.IsBridge e
      · exact Or.inr ⟨e, List.mem_cons_self, he, hsame⟩
      · apply Or.inl
        have het := G.nonbridge_sameBlob he
        rw [hs] at het
        exact het.trans hsame
    · exact Or.inr ⟨f, List.mem_cons_of_mem e hmem, hf, hfb⟩

/-- Rootedness supplies an actual incoming original bridge for every component
other than the root component, without assuming a bridge-tree decomposition. -/
theorem nonroot_component_has_incoming_bridge (G : EdgeGraph V E) (root : V)
    (hr : ∀ v, G.DReach root v) (v : V) (hv : ¬ G.SameBlob root v) :
    ∃ e, G.IsBridge e ∧ G.SameBlob (G.target e) v := by
  obtain ⟨es, hp⟩ := GProgram.G5.exists_edgePath_of_directed (hr v)
  rcases EdgePath.sameBlob_or_incoming_bridge hp with hs | ⟨e, _, he, hb⟩
  · exact False.elim (hv hs)
  · exact ⟨e, he, hb⟩

/-- Exact original bridge occurrence uniqueness for every non-root component. -/
theorem nonroot_component_unique_entry (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) (v : V)
    (hv : ¬ G.SameBlob root v) :
    ∃! e, G.IsBridge e ∧ G.SameBlob (G.target e) v := by
  obtain ⟨e, he, hb⟩ := nonroot_component_has_incoming_bridge G root hr v hv
  refine ⟨e, ⟨he, hb⟩, ?_⟩
  intro f hf
  exact (bridge_targets_sameBlob_iff_eq G root ha hr hf.1 he).mp
    (hf.2.trans (G.sameBlob_symm hb))






end GProgram.G5.ComponentEntries

end FullContextModule16

section FullContextModule17



/-!
# Original cut-child nonbridge routes have at most two choices

New proof contribution: dot's active Lean source-bridge lane, 2026-10-02.
We use original edge occurrences, including parallel arcs. The generic proof
needs only acyclicity and unique incoming edges at sources of kept edges.
The actual binary cut-child source supplies this uniqueness for nonbridges:
a hybrid cannot be the source of a nonbridge, since its child is a bridge.
A rootward nonbridge route is consequently fixed by its first parent edge.
This is the graph core of the two-route current-blob claim, not a stochastic
route probability, calendar compiler, or full G5 identification theorem.
-/

namespace GProgram.G5.NonbridgeRoutes

open Nanuq.Source

variable {V E : Type*}

/-- Rootward paths explicitly retain all original edge occurrence IDs. -/
inductive UpPath (G : EdgeGraph V E) (keep : E → Prop) : V → V → List E → Prop
  | nil (a : V) : UpPath G keep a a []
  | cons {a b : V} {e : E} {es : List E}
      (ht : G.target e = a) (he : keep e)
      (rest : UpPath G keep (G.source e) b es) : UpPath G keep a b (e :: es)

theorem UpPath.directed {G : EdgeGraph V E} {keep : E → Prop}
    {a b : V} {es : List E} (p : UpPath G keep a b es) : G.DReach b a := by
  induction p with
  | nil => exact .refl
  | cons ht _ rest ih =>
    exact ih.tail ⟨_, rfl, ht⟩

theorem UpPath.nonempty_start_ne_end {G : EdgeGraph V E} {keep : E → Prop}
    (ha : G.Acyclic) {a b : V} {e : E} {es : List E}
    (p : UpPath G keep a b (e :: es)) : a ≠ b := by
  intro hab
  cases p with
  | cons ht he rest =>
    subst b
    exact ha a (Relation.TransGen.tail' rest.directed ⟨e, rfl, ht⟩)

/-- Once an original parent edge is selected, the whole remaining rootward
kept-edge route is unique. This premise is local degree information, not the
route uniqueness conclusion itself. -/
theorem UpPath.unique_from_kept_source {G : EdgeGraph V E} {keep : E → Prop}
    (ha : G.Acyclic)
    (hu : ∀ e, keep e → ∀ f g, G.target f = G.source e →
      G.target g = G.source e → f = g)
    {a b : V} {es fs : List E} (p : UpPath G keep a b es)
    (q : UpPath G keep a b fs)
    (hsource : ∃ e, keep e ∧ G.source e = a) : es = fs := by
  induction p generalizing fs with
  | nil a =>
    cases q with
    | nil => rfl
    | cons ht he rest =>
      exact False.elim ((UpPath.cons ht he rest).nonempty_start_ne_end ha rfl)
  | @cons a b e es ht he rest ih =>
    cases q with
    | nil =>
      exact False.elim ((UpPath.cons ht he rest).nonempty_start_ne_end ha rfl)
    | @cons _ _ f fs htf hf tail =>
      obtain ⟨g, hg, hgs⟩ := hsource
      have hef : e = f := hu g hg e f (ht.trans hgs.symm) (htf.trans hgs.symm)
      subst f
      congr 1
      exact ih tail ⟨e, he, rfl⟩

/-- First-parent-edge equality already determines the complete nonbridge
route, even when the endpoint itself has two parent edges. -/
theorem UpPath.unique_of_same_first {G : EdgeGraph V E} {keep : E → Prop}
    (ha : G.Acyclic)
    (hu : ∀ e, keep e → ∀ f g, G.target f = G.source e →
      G.target g = G.source e → f = g)
    {a b : V} {e : E} {es fs : List E}
    (p : UpPath G keep a b (e :: es)) (q : UpPath G keep a b (e :: fs)) : es = fs := by
  cases p with
  | cons ht he rest =>
    cases q with
    | cons htf hf tail =>
      exact rest.unique_from_kept_source ha hu tail ⟨e, he, rfl⟩

section OriginalSource

variable {X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem incoming_equal_of_indegree_le_one (N : RootedBinary V E X) {v : V}
    (hdeg : N.graph.inDegree v ≤ 1) {e f : E}
    (he : N.graph.target e = v) (hf : N.graph.target f = v) : e = f := by
  classical
  exact Finset.card_le_one.mp hdeg e (by simp [he]) f (by simp [hf])

theorem nonhybrid_indegree_le_one (N : RootedBinary V E X) {v : V}
    (hv : ¬ N.graph.IsHybrid v) : N.graph.inDegree v ≤ 1 := by
  by_cases hr : v = N.root
  · rw [hr, N.root_degrees.1]
    omega
  · by_cases hl : ∃ x, N.leaf x = v
    · obtain ⟨x, rfl⟩ := hl
      rw [(N.leaf_degrees x).1]
    · rcases N.internal_degrees v hr (fun x hx => hl ⟨x, hx⟩) with ht | hh
      · rw [ht.1]
      · exact False.elim (hv hh)

theorem cut_child_nonbridge_incoming_unique (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (e : E) (he : ¬ N.graph.IsBridge e) (f g : E)
    (hf : N.graph.target f = N.graph.source e)
    (hg : N.graph.target g = N.graph.source e) : f = g := by
  apply incoming_equal_of_indegree_le_one N
    (nonhybrid_indegree_le_one N (fun hh => he (hcut e hh))) hf hg

/-- Actual binary cut-child source consequence. Selecting one of a hybrid's
at most two original parents fixes the rest of its nonbridge route. -/
theorem original_nonbridge_route_unique_of_first (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} {e : E} {es fs : List E}
    (p : UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b (e :: es))
    (q : UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b (e :: fs)) : es = fs := by
  exact p.unique_of_same_first N.acyclic (cut_child_nonbridge_incoming_unique N hcut) q

/-- Every finite family of distinct original nonbridge routes has cardinal
at most the actual incoming edge-occurrence count of its starting port. -/
theorem finite_nonbridge_route_family_card_le_indegree (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ N.graph.inDegree a := by
  classical
  let incoming : Finset E := Finset.univ.filter (fun e => N.graph.target e = a)
  have hmap : Set.MapsTo List.head? (R : Set (List E))
      ((incoming.image Option.some) : Set (Option E)) := by
    intro es hes
    have hp := hR es hes
    cases es with
    | nil => cases hp; exact False.elim (hab rfl)
    | cons e tail =>
      cases hp with
      | cons ht _ _ =>
        simp only [List.head?_cons, Finset.mem_coe, Finset.mem_image]
        exact ⟨e, by simp [incoming, ht], rfl⟩
  have hinj : Set.InjOn List.head? (R : Set (List E)) := by
    intro es hes fs hfs heq
    have hp := hR es hes
    have hq := hR fs hfs
    cases es with
    | nil => cases hp; exact False.elim (hab rfl)
    | cons e tail =>
      cases fs with
      | nil => simp at heq
      | cons f rest =>
        simp only [List.head?_cons, Option.some.injEq] at heq
        subst f
        exact congrArg (List.cons e) (original_nonbridge_route_unique_of_first N hcut hp hq)
  have hc := Finset.card_le_card_of_injOn List.head? hmap hinj
  simpa only [Finset.card_image_of_injective incoming (Option.some_injective E), incoming, EdgeGraph.inDegree] using hc

/-- At a genuine hybrid port there are at most TWO original nonbridge routes
through the current component. Parallel parents still count as distinct choices. -/
theorem hybrid_nonbridge_route_family_card_le_two (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (ha : N.graph.IsHybrid a) (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ 2 := by
  simpa only [ha.1] using finite_nonbridge_route_family_card_le_indegree N hcut hab R hR

/-- At an ordinary port the same actual-source argument supplies at most ONE
route, without assuming a canonical blob, planar embedding, or route oracle. -/
theorem ordinary_nonbridge_route_family_card_le_one (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (ha : ¬ N.graph.IsHybrid a) (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ 1 := by
  exact (finite_nonbridge_route_family_card_le_indegree N hcut hab R hR).trans
    (nonhybrid_indegree_le_one N ha)

end OriginalSource









end GProgram.G5.NonbridgeRoutes

end FullContextModule17

section FullContextModule18




/-!
# Actual original root routes cover component calendar intervals

Contributor: dot, 2026-10-02. The route suffix inside an actual bridge-deleted
component is derived from original rooted acyclic graph paths. It is not a
provided nonbridge-route oracle. Strict original edge clocks then supply the
unique active population on every entry/port interval. Source coin laws and
observation-driven safe chronology remain separate.
-/
namespace GProgram.G5.ComponentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E : Type*}

theorem EdgePath.source_reachable_of_mem {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {e : E} (he : e ∈ es) : G.DReach a (G.source e) := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
    rcases List.mem_cons.mp he with h | h
    · subst e
      rw [hs]
      exact .refl
    · exact (Relation.ReflTransGen.single ⟨f,hs,rfl⟩).trans (ih h)

theorem EdgePath.all_nonbridge_of_sameBlob {G : EdgeGraph V E} (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v)
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    (hab : G.SameBlob a b) : ∀ e ∈ es, ¬G.IsBridge e := by
  intro e he heb
  have htb := p.target_reaches_end_of_mem he
  have havoid := GProgram.G5.ComponentEntries.sameBlob_avoids_bridge G heb hab
  have hbt : G.ReachWithout e (G.target e) b :=
    (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr heb b).mpr htb
  have hta : G.DReach (G.target e) a :=
    (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr heb a).mp
      (hbt.trans (G.ureach_symm havoid))
  have hts := hta.trans (EdgePath.source_reachable_of_mem p he)
  exact ha (G.target e) (Relation.TransGen.tail' hts ⟨e,rfl,rfl⟩)

theorem EdgePath.split_at_original_edge {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {e : E} (he : e ∈ es) :
    ∃ pre post, es = pre ++ e :: post ∧
      GProgram.G5.EdgePath G a (G.source e) pre ∧
      GProgram.G5.EdgePath G (G.target e) b post := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
    rcases List.mem_cons.mp he with h | h
    · subst e
      refine ⟨[],fs,rfl,?_,rest⟩
      rw [hs]
      exact .nil a
    · rcases ih h with ⟨pre,post,heq,hpre,hpost⟩
      exact ⟨f::pre,post,by simp [heq],.cons hs hpre,hpost⟩

theorem root_route_component_decomposition (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v)
    {port : V} {es : List E} (p : GProgram.G5.EdgePath G root port es) :
    (G.SameBlob root port ∧ ∀ e ∈ es, ¬G.IsBridge e) ∨
    ∃ entry pre post, es = pre ++ entry :: post ∧ G.IsBridge entry ∧
      G.SameBlob (G.target entry) port ∧
      GProgram.G5.EdgePath G root (G.source entry) pre ∧
      GProgram.G5.EdgePath G (G.target entry) port post ∧
      (∀ e ∈ post, ¬G.IsBridge e) := by
  rcases GProgram.G5.ComponentEntries.EdgePath.sameBlob_or_incoming_bridge p with
    hs | ⟨entry,hemem,hbridge,hblob⟩
  · exact Or.inl ⟨hs,EdgePath.all_nonbridge_of_sameBlob root ha hr p hs⟩
  · rcases EdgePath.split_at_original_edge p hemem with ⟨pre,post,heq,hpre,hpost⟩
    exact Or.inr ⟨entry,pre,post,heq,hbridge,hblob,hpre,hpost,
      EdgePath.all_nonbridge_of_sameBlob root ha hr hpost hblob⟩

theorem EdgePath.active_exists {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {t : ℝ} (hl : C.age b ≤ t) (hu : t < C.age a) :
    ∃ e ∈ es, C.Active t e := by
  induction p with
  | nil a => exact False.elim (not_lt_of_ge hl hu)
  | @cons a b e es hs rest ih =>
    by_cases he : C.age (G.target e) ≤ t
    · exact ⟨e,List.mem_cons_self,he,by simpa [hs] using hu⟩
    · rcases ih hl (lt_of_not_ge he) with ⟨f,hmem,hactive⟩
      exact ⟨f,List.mem_cons_of_mem e hmem,hactive⟩

theorem EdgePath.unique_active_exists {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {t : ℝ} (hl : C.age b ≤ t) (hu : t < C.age a) :
    ∃! e, e ∈ es ∧ C.Active t e := by
  obtain ⟨e,he,ha⟩ := EdgePath.active_exists C p hl hu
  exact ⟨e,⟨he,ha⟩,fun f hf => p.active_unique C hf.1 he hf.2 ha⟩




end GProgram.G5.ComponentCalendar

end FullContextModule18

section FullContextModule19


/-!
# Actual component calendar support is bounded by original port indegree

Contributor: dot, 2026-10-02. Original directed edge-occurrence paths are
reversed into the rootward nonbridge representation. Current populations are
then defined by active edges on ALL actual nonbridge component paths. Their
support bound is derived from original binary cut-child degrees and strict
calendar clocks; neither a route oracle nor the desired support bound is an
interface assumption. Source coin probabilities and observed chronology are
separate obligations.
-/

namespace GProgram.G5.NonbridgeRoutes
open Nanuq.Source
variable {V E : Type*}

theorem UpPath.append {G : EdgeGraph V E} {keep : E → Prop}
    {a b c : V} {es fs : List E} (p : UpPath G keep a b es)
    (q : UpPath G keep b c fs) : UpPath G keep a c (es ++ fs) := by
  induction p with
  | nil => exact q
  | cons ht he rest ih => exact .cons ht he (ih q)

theorem EdgePath.to_upPath_reverse {G : EdgeGraph V E} {keep : E → Prop}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    (hk : ∀ e ∈ es, keep e) : UpPath G keep b a es.reverse := by
  induction p with
  | nil a => exact .nil a
  | @cons a b e es hs rest ih =>
    have hr := ih (fun f hf => hk f (List.mem_cons_of_mem e hf))
    have he : UpPath G keep (G.target e) a [e] := by
      exact .cons rfl (hk e List.mem_cons_self) (by rw [hs]; exact .nil a)
    simpa only [List.reverse_cons] using hr.append he



end GProgram.G5.NonbridgeRoutes

namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- ALL original nonbridge paths from a component entry to a port contribute
current population edges. The definition contains no support cardinal bound. -/
noncomputable def activeComponentEdges (G : EdgeGraph V E) (C : Calendar G)
    (entry port : V) (t : ℝ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ∃ es : List E,
    EdgePath G entry port es ∧ (∀ f ∈ es, ¬G.IsBridge f) ∧
    e ∈ es ∧ C.Active t e)

theorem mem_activeComponentEdges_iff (G : EdgeGraph V E) (C : Calendar G)
    (entry port : V) (t : ℝ) (e : E) :
    e ∈ activeComponentEdges G C entry port t ↔ ∃ es : List E,
      EdgePath G entry port es ∧ (∀ f ∈ es, ¬G.IsBridge f) ∧
      e ∈ es ∧ C.Active t e := by
  classical
  simp only [activeComponentEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Distinct actual current population edges require distinct original routes:
strict calendar clocks permit only one active edge along any one route. -/
theorem finite_active_nonbridge_edges_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {entry port : V} (hne : port ≠ entry) (t : ℝ) (A : Finset E)
    (hA : ∀ e ∈ A, ∃ es : List E, EdgePath N.graph entry port es ∧
      (∀ f ∈ es, ¬N.graph.IsBridge f) ∧ e ∈ es ∧ C.Active t e) :
    A.card ≤ N.graph.inDegree port := by
  classical
  have hw : ∀ u : {e // e ∈ A}, ∃ es : List E,
      EdgePath N.graph entry port es ∧
      (∀ f ∈ es, ¬N.graph.IsBridge f) ∧ u.val ∈ es ∧ C.Active t u.val :=
    fun u => hA u.val u.property
  choose route hroute using hw
  let R : Finset (List E) := A.attach.image (fun u => (route u).reverse)
  have hR : ∀ es ∈ R,
      UpPath N.graph (fun f => ¬N.graph.IsBridge f) port entry es := by
    intro es hes
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hes
    exact GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse (hroute u).1 (hroute u).2.1
  have hi : Function.Injective (fun u : {e // e ∈ A} => (route u).reverse) := by
    intro u v huv
    have huv' : route u = route v := List.reverse_inj.mp huv
    apply Subtype.ext
    exact (hroute u).1.active_unique C (hroute u).2.2.1
      (by simpa only [huv'] using (hroute v).2.2.1)
      (hroute u).2.2.2 (hroute v).2.2.2
  have hcard : R.card = A.card := by
    simp only [R, Finset.card_image_of_injective _ hi, Finset.card_attach]
  rw [← hcard]
  exact finite_nonbridge_route_family_card_le_indegree N hcut hne R hR

/-- The original source degree theorem bounds the defined actual active support. -/
theorem activeComponentEdges_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {entry port : V} {t : ℝ} (hl : C.age port ≤ t) (hu : t < C.age entry) :
    (activeComponentEdges N.graph C entry port t).card ≤ N.graph.inDegree port := by
  have hne : port ≠ entry := by
    intro h
    rw [h] at hl
    exact not_lt_of_ge hl hu
  apply finite_active_nonbridge_edges_card_le_indegree N C hcut hne t
  intro e he
  exact (mem_activeComponentEdges_iff N.graph C entry port t e).mp he



end GProgram.G5.ComponentSupport

end FullContextModule19

section FullContextModule20


/-!
# Complete original root routes induce the actual current component support

Contributor: dot, 2026-10-02. The active support is defined using every complete
original root-to-port path. Its equality with the nonbridge component support
is proved using the actual incoming bridge and strictly positive clocks. The
resulting bound comes from original binary cut-child degrees, with original
parallel edge occurrences retained. No stochastic coin law or observation
chronology is asserted here.
-/
namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentCalendar
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Current original population support over all complete original routes. -/
noncomputable def activeRootRouteEdges (G : EdgeGraph V E) (C : Calendar G)
    (root port : V) (t : ℝ) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => ∃ es : List E,
    EdgePath G root port es ∧ e ∈ es ∧ C.Active t e)

theorem mem_activeRootRouteEdges_iff (G : EdgeGraph V E) (C : Calendar G)
    (root port : V) (t : ℝ) (e : E) :
    e ∈ activeRootRouteEdges G C root port t ↔ ∃ es : List E,
      EdgePath G root port es ∧ e ∈ es ∧ C.Active t e := by
  classical
  simp only [activeRootRouteEdges, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every complete original route into an incoming bridge's actual component
contains that exact bridge occurrence. -/
theorem incoming_bridge_mem_root_route (N : RootedBinary V E X)
    {entry : E} (he : N.graph.IsBridge entry) {port : V}
    (hb : N.graph.SameBlob (N.graph.target entry) port)
    {es : List E} (p : EdgePath N.graph N.root port es) : entry ∈ es := by
  by_contra hn
  have hsource : N.graph.ReachWithout entry (N.graph.source entry) port :=
    (N.root_on_source_side entry).trans (p.reach_without_of_not_mem hn)
  have htarget : N.graph.ReachWithout entry (N.graph.target entry) port :=
    GProgram.G5.ComponentEntries.sameBlob_avoids_bridge N.graph he hb
  exact N.graph.bridge_sides_disjoint he hsource htarget

/-- Before the component entry age, every active edge of a complete original
route lies on its actual all-nonbridge suffix. Prefixes and the entry bridge
are excluded by their original clocks. -/
theorem active_root_edge_has_nonbridge_suffix (N : RootedBinary V E X)
    (C : Calendar N.graph) {entry : E} (he : N.graph.IsBridge entry)
    {port : V} (hb : N.graph.SameBlob (N.graph.target entry) port)
    {es : List E} (p : EdgePath N.graph N.root port es)
    {t : ℝ} (hu : t < C.age (N.graph.target entry)) {f : E}
    (hf : f ∈ es) (ha : C.Active t f) :
    ∃ post : List E, EdgePath N.graph (N.graph.target entry) port post ∧
      (∀ g ∈ post, ¬N.graph.IsBridge g) ∧ f ∈ post := by
  have hem := incoming_bridge_mem_root_route N he hb p
  obtain ⟨pre,post,hes,hpre,hpost⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge p hem
  refine ⟨post,hpost,
    GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob N.root
      N.acyclic N.rooted hpost hb,?_⟩
  rw [hes] at hf
  rcases List.mem_append.mp hf with hp | hp
  · have hage : C.age (N.graph.source entry) ≤ C.age (N.graph.target f) :=
      C.age_le_of_directed (hpre.target_reaches_end_of_mem hp)
    have hlt : t < C.age (N.graph.target f) :=
      hu.trans ((C.edge_older entry).trans_le hage)
    exact False.elim (not_le_of_gt hlt ha.1)
  · rcases List.mem_cons.mp hp with h | hp
    · subst f
      exact False.elim (not_le_of_gt hu ha.1)
    · exact hp

/-- Exact equality: complete original root-route support equals the support
of actual component paths in an incoming-entry calendar interval. -/
theorem activeRootRouteEdges_eq_component (N : RootedBinary V E X)
    (C : Calendar N.graph) {entry : E} (he : N.graph.IsBridge entry)
    {port : V} (hb : N.graph.SameBlob (N.graph.target entry) port)
    {t : ℝ} (hu : t < C.age (N.graph.target entry)) :
    activeRootRouteEdges N.graph C N.root port t =
      activeComponentEdges N.graph C (N.graph.target entry) port t := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, mem_activeComponentEdges_iff]
  constructor
  · rintro ⟨es,hp,hmem,hactive⟩
    obtain ⟨post,hpost,hkeep,hf⟩ :=
      active_root_edge_has_nonbridge_suffix N C he hb hp hu hmem hactive
    exact ⟨post,hpost,hkeep,hf,hactive⟩
  · rintro ⟨post,hpost,_,hf,hactive⟩
    obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed (N.rooted (N.graph.source entry))
    have hentry : EdgePath N.graph (N.graph.source entry) (N.graph.target entry) [entry] :=
      .cons rfl (.nil _)
    exact ⟨pre ++ [entry] ++ post,(hpre.append hentry).append hpost,
      List.mem_append_right _ hf,hactive⟩

/-- Root-component routes are themselves all-nonbridge paths. -/
theorem activeRootRouteEdges_eq_root_component (N : RootedBinary V E X)
    (C : Calendar N.graph) {port : V} (hb : N.graph.SameBlob N.root port) (t : ℝ) :
    activeRootRouteEdges N.graph C N.root port t =
      activeComponentEdges N.graph C N.root port t := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, mem_activeComponentEdges_iff]
  constructor
  · rintro ⟨es,hp,hf,ha⟩
    exact ⟨es,hp,GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob
      N.root N.acyclic N.rooted hp hb,hf,ha⟩
  · rintro ⟨es,hp,_,hf,ha⟩
    exact ⟨es,hp,hf,ha⟩

/-- Actual original complete-route current support is bounded by the current
component port's actual incoming edge-occurrence count. -/
theorem activeRootRouteEdges_card_le_indegree_of_entry
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {entry : E} (he : N.graph.IsBridge entry) {port : V}
    (hb : N.graph.SameBlob (N.graph.target entry) port) {t : ℝ}
    (hl : C.age port ≤ t) (hu : t < C.age (N.graph.target entry)) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ N.graph.inDegree port := by
  rw [activeRootRouteEdges_eq_component N C he hb hu]
  exact activeComponentEdges_card_le_indegree N C hcut hl hu






end GProgram.G5.ComponentSupport

end FullContextModule20

section FullContextModule21


/-!
# The original binary cut-child source has at most two current port positions

Contributor: dot, 2026-10-02. The current component interval is specified only
by actual graph connectivity, original incoming bridges and original clocks.
The population support over all complete original root routes is nonempty and
has at most two edge occurrences there. Ordinary ports have at most one. This
is a graph/calendar source theorem, not a claim of fair coin probabilities,
merger-free sampling, or the full G5 identification theorem.
-/
namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Calendar interval inside the actual bridge-deleted component of a port. -/
def InCurrentComponentInterval (N : RootedBinary V E X) (C : Calendar N.graph)
    (port : V) (t : ℝ) : Prop :=
  C.age port ≤ t ∧
    ((N.graph.SameBlob N.root port ∧ t < C.age N.root) ∨
      ∃ entry : E, N.graph.IsBridge entry ∧
        N.graph.SameBlob (N.graph.target entry) port ∧
        t < C.age (N.graph.target entry))

theorem binary_indegree_le_two (N : RootedBinary V E X) (v : V) :
    N.graph.inDegree v ≤ 2 := by
  by_cases h : N.graph.IsHybrid v
  · exact le_of_eq h.1
  · exact (nonhybrid_indegree_le_one N h).trans (by decide)

/-- Actual current-component support of complete original root routes is
bounded by the actual incoming occurrence count of its port. -/
theorem current_port_support_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ N.graph.inDegree port := by
  rcases ht with ⟨hl,⟨hb,hu⟩ | ⟨entry,he,hb,hu⟩⟩
  · rw [activeRootRouteEdges_eq_root_component N C hb t]
    exact activeComponentEdges_card_le_indegree N C hcut hl hu
  · exact activeRootRouteEdges_card_le_indegree_of_entry N C hcut he hb hl hu

/-- The derived two-position source conclusion, with no assumed support bound. -/
theorem current_port_support_card_le_two
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ 2 :=
  (current_port_support_card_le_indegree N C hcut ht).trans
    (binary_indegree_le_two N port)

/-- Ordinary ports have only one possible current population. -/
theorem current_ordinary_port_support_card_le_one
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} (ho : ¬N.graph.IsHybrid port) {t : ℝ}
    (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ 1 :=
  (current_port_support_card_le_indegree N C hcut ht).trans
    (nonhybrid_indegree_le_one N ho)

/-- Rootedness and the real component calendar interval guarantee an actual
active original population, rather than a vacuous support upper bound. -/
theorem current_port_support_nonempty
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).Nonempty := by
  obtain ⟨es,hp⟩ := exists_edgePath_of_directed (N.rooted port)
  have hu : t < C.age N.root := by
    rcases ht.2 with ⟨_,hu⟩ | ⟨entry,_,_,hu⟩
    · exact hu
    · exact hu.trans_le (C.age_le_of_directed (N.rooted (N.graph.target entry)))
  obtain ⟨e,hem,ha⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hp ht.1 hu
  exact ⟨e,(mem_activeRootRouteEdges_iff N.graph C N.root port t e).mpr ⟨es,hp,hem,ha⟩⟩

/-- At an ordinary port the actual current source population is unique. -/
theorem current_ordinary_port_support_card_eq_one
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} (ho : ¬N.graph.IsHybrid port) {t : ℝ}
    (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card = 1 := by
  have hl := Finset.card_pos.mpr (current_port_support_nonempty N C ht)
  have hu := current_ordinary_port_support_card_le_one N C hcut ho ht
  omega







end GProgram.G5.ComponentSupport

end FullContextModule21

section FullContextModule22


/-!
# Actual original-tip support above an exit bridge equals port support

Contributor: dot, 2026-10-02. An original bridge separating a selected tip from
its older component is present on every complete original tip route. At ages
at least its source-port age, all younger route suffix populations are inactive.
Thus the actual original-tip population support equals actual port support,
and the binary cut-child two-position result applies to original tips. No
conditioning on merger survival or stochastic coin law is involved.
-/
namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Above an actual exit bridge's source age, an active original-tip edge must
belong to the complete original root-to-port prefix. -/
theorem active_tip_edge_has_root_port_prefix
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {es : List E} (p : EdgePath N.graph N.root (N.leaf x) es)
    {t : ℝ} (hl : C.age (N.graph.source exit) ≤ t) {f : E}
    (hf : f ∈ es) (ha : C.Active t f) :
    ∃ pre : List E, EdgePath N.graph N.root (N.graph.source exit) pre ∧ f ∈ pre := by
  have hem := bridge_mem_every_descendant_route N he p hd
  obtain ⟨pre,post,hes,hpre,hpost⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge p hem
  refine ⟨pre,hpre,?_⟩
  rw [hes] at hf
  rcases List.mem_append.mp hf with hp | hp
  · exact hp
  · rcases List.mem_cons.mp hp with h | hp
    · subst f
      exact False.elim (not_lt_of_ge hl ha.2)
    · have hage : C.age (N.graph.source f) ≤ C.age (N.graph.target exit) :=
        hpost.source_age_le C hp
      have hle : C.age (N.graph.source f) ≤ t :=
        hage.trans ((le_of_lt (C.edge_older exit)).trans hl)
      exact False.elim (not_lt_of_ge hle ha.2)

/-- Exact source support equality for an original tip and its fixed actual
exit-bridge port throughout the older component calendar interval. -/
theorem original_tip_support_eq_port
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {t : ℝ} (hl : C.age (N.graph.source exit) ≤ t) :
    activeRootRouteEdges N.graph C N.root (N.leaf x) t =
      activeRootRouteEdges N.graph C N.root (N.graph.source exit) t := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, mem_activeRootRouteEdges_iff]
  constructor
  · rintro ⟨es,hp,hf,ha⟩
    obtain ⟨pre,hpre,hmem⟩ := active_tip_edge_has_root_port_prefix N C he hd hp hl hf ha
    exact ⟨pre,hpre,hmem,ha⟩
  · rintro ⟨pre,hpre,hf,ha⟩
    obtain ⟨post,hpost⟩ := exists_edgePath_of_directed hd
    have hexit : EdgePath N.graph (N.graph.source exit) (N.graph.target exit) [exit] :=
      .cons rfl (.nil _)
    exact ⟨pre ++ ([exit] ++ post),hpre.append (hexit.append hpost),
      List.mem_append_left _ hf,ha⟩

/-- The actual original-tip current population support is nonempty and has at
most two original edge occurrences in its exit port's current component. -/
theorem original_tip_current_support_nonempty_card_le_two
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {t : ℝ} (ht : InCurrentComponentInterval N C (N.graph.source exit) t) :
    (activeRootRouteEdges N.graph C N.root (N.leaf x) t).Nonempty ∧
      (activeRootRouteEdges N.graph C N.root (N.leaf x) t).card ≤ 2 := by
  rw [original_tip_support_eq_port N C he hd ht.1]
  exact ⟨current_port_support_nonempty N C ht,current_port_support_card_le_two N C hcut ht⟩

/-- During an actual exit-bridge population interval, every original tip below
that bridge has precisely that one original population in its route support. -/
theorem original_tip_bridge_support_eq_singleton
    (N : RootedBinary V E X) (C : Calendar N.graph)
    {exit : E} (he : N.graph.IsBridge exit) {x : X}
    (hd : N.graph.DReach (N.graph.target exit) (N.leaf x))
    {t : ℝ} (ht : C.Active t exit) :
    activeRootRouteEdges N.graph C N.root (N.leaf x) t = {exit} := by
  classical
  ext f
  rw [mem_activeRootRouteEdges_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨es,hp,hf,ha⟩
    exact hp.active_unique C hf (bridge_mem_every_descendant_route N he hp hd) ha ht
  · intro hf
    subst f
    obtain ⟨es,hp⟩ := original_tip_route_exists N x
    exact ⟨es,hp,bridge_mem_every_descendant_route N he hp hd,ht⟩





end GProgram.G5.ComponentSupport

end FullContextModule22

section FullContextModule23


/-!
# Original hybrid parent occurrence determines its entire current calendar route

Contributor: dot, 2026-10-02. Component entries are actual original roots or
actual incoming bridge targets. Each original hybrid parent occurrence admits
an all-nonbridge route from that entry; the binary cut-child graph uniquely
fixes it once the last original parent is specified. Strict clocks then give
one actual current population for each parent bit. No stochastic probability
or source-observation chronology is an interface field here.
-/
namespace GProgram.G5.ParentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentSupport
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Actual entry into the bridge-deleted component of a specified port. -/
def IsComponentEntryFor (N : RootedBinary V E X) (entry port : V) : Prop :=
  (entry = N.root ∧ N.graph.SameBlob N.root port) ∨
    ∃ e : E, N.graph.IsBridge e ∧ entry = N.graph.target e ∧
      N.graph.SameBlob (N.graph.target e) port

theorem component_entry_sameBlob (N : RootedBinary V E X) {entry port : V}
    (he : IsComponentEntryFor N entry port) : N.graph.SameBlob entry port := by
  rcases he with ⟨rfl,hb⟩ | ⟨e,_,rfl,hb⟩ <;> exact hb

/-- Rootedness and actual incoming-bridge connectivity imply a directed route
from the component entry to every vertex in that same component. -/
theorem component_entry_reaches_sameBlob (N : RootedBinary V E X)
    {entry port v : V} (he : IsComponentEntryFor N entry port)
    (hb : N.graph.SameBlob entry v) : N.graph.DReach entry v := by
  rcases he with ⟨rfl,_⟩ | ⟨e,hbridge,rfl,_⟩
  · exact N.rooted v
  · exact (GProgram.G5.Minimal.bridge_component_iff_descendant N.graph N.root
      N.acyclic N.rooted hbridge v).mp
        (GProgram.G5.ComponentEntries.sameBlob_avoids_bridge N.graph hbridge hb)

theorem original_parent_nonbridge {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (b : Bool) :
    ¬N.graph.IsBridge (H.parent b) := by
  cases b
  · exact (GProgram.G6.BridgeEntry.original_hybrid_parents_nonbridge H).1
  · exact (GProgram.G6.BridgeEntry.original_hybrid_parents_nonbridge H).2

theorem original_parent_target {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (b : Bool) :
    N.graph.target (H.parent b) = H.hybrid := by
  cases b
  · exact H.target0
  · exact H.target1

/-- Every actual original parent occurrence admits an all-nonbridge route
from the actual entry. Parallel incoming arcs remain distinct choices. -/
theorem parent_route_prefix_exists {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) :
    ∃ pre : List E, EdgePath N.graph entry (N.graph.source (H.parent b)) pre ∧
      (∀ f ∈ pre, ¬N.graph.IsBridge f) := by
  have hp := N.graph.nonbridge_sameBlob (original_parent_nonbridge H b)
  rw [original_parent_target H b] at hp
  have hb := (component_entry_sameBlob N he).trans (N.graph.sameBlob_symm hp)
  obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed
    (component_entry_reaches_sameBlob N he hb)
  exact ⟨pre,hpre,GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob
    N.root N.acyclic N.rooted hpre hb⟩

noncomputable def parentRoutePrefix {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) : List E :=
  Classical.choose (parent_route_prefix_exists H he b)

noncomputable def parentRoute {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) : List E :=
  parentRoutePrefix H he b ++ [H.parent b]

theorem parentRoute_path {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) :
    EdgePath N.graph entry H.hybrid (parentRoute H he b) := by
  have hpre := (Classical.choose_spec (parent_route_prefix_exists H he b)).1
  have hparent : EdgePath N.graph (N.graph.source (H.parent b)) H.hybrid [H.parent b] :=
    .cons rfl (by rw [original_parent_target H b]; exact .nil _)
  exact hpre.append hparent

theorem parentRoute_nonbridge {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool) :
    ∀ f ∈ parentRoute H he b, ¬N.graph.IsBridge f :=
  GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob N.root N.acyclic N.rooted
    (parentRoute_path H he b) (component_entry_sameBlob N he)

/-- The deterministic original cut-child graph fixes the entire path once its
last original parent occurrence is given. This is stronger than a support bound. -/
theorem parent_route_unique {N : RootedBinary V E X}
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) (b : Bool)
    {pre : List E} (hp : EdgePath N.graph entry H.hybrid (pre ++ [H.parent b])) :
    pre ++ [H.parent b] = parentRoute H he b := by
  have hk := GProgram.G5.ComponentCalendar.EdgePath.all_nonbridge_of_sameBlob
    N.root N.acyclic N.rooted hp (component_entry_sameBlob N he)
  have p := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hp hk
  have q := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse
    (parentRoute_path H he b) (parentRoute_nonbridge H he b)
  simp only [parentRoute, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append] at p q
  have hrev := original_nonbridge_route_unique_of_first N hcut p q
  have heq := List.reverse_inj.mp hrev
  exact congrArg (fun xs => xs ++ [H.parent b]) heq

/-- A current actual population selected deterministically by one ORIGINAL
parent coin, including coincidence of both choices above their joining point. -/
noncomputable def parentPosition {N : RootedBinary V E X}
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (b : Bool) : E :=
  Classical.choose (GProgram.G5.ComponentCalendar.EdgePath.active_exists C
    (parentRoute_path H he b) hl hu)

theorem parentPosition_spec {N : RootedBinary V E X}
    (C : Calendar N.graph) (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (b : Bool) :
    parentPosition C H he hl hu b ∈ parentRoute H he b ∧
      C.Active t (parentPosition C H he hl hu b) :=
  Classical.choose_spec (GProgram.G5.ComponentCalendar.EdgePath.active_exists C
    (parentRoute_path H he b) hl hu)

/-- Every other actual route with that last original parent has the same
current population. The result is valid for each switching, not in expectation. -/
theorem active_edge_eq_parentPosition {N : RootedBinary V E X}
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) (b : Bool)
    {pre : List E} (hp : EdgePath N.graph entry H.hybrid (pre ++ [H.parent b]))
    {f : E} (hf : f ∈ pre ++ [H.parent b]) (ha : C.Active t f) :
    f = parentPosition C H he hl hu b := by
  have hroute := parent_route_unique hcut H he b hp
  rw [hroute] at hf
  exact (parentRoute_path H he b).active_unique C hf
    (parentPosition_spec C H he hl hu b).1 ha (parentPosition_spec C H he hl hu b).2






end GProgram.G5.ParentCalendar

end FullContextModule23

section FullContextModule24


/-!
# Actual selector/occupancy interpretation for G5's fair two-position kernel

Contributor: dot, 2026-10-02. Theorems below hold for an arbitrary population
position type, not just a enumerated fixture. Each label has two actual route
positions. Their selector witness is proved equivalent to the block-count
predicate used by the hand Q theorem. No genealogy/Q equality is assumed.
The full six-moment absence criterion and original-source probability bridge
remain separate proof obligations.
-/
namespace GProgram.G5.QuartetKernel

variable {α : Type*} [DecidableEq α]

def blockCount (p : Fin 2 → α) (e : α) : Nat :=
  (if p 0 = e then 1 else 0) + (if p 1 = e then 1 else 0)

def pairCount (p q : Fin 2 → α) : Nat :=
  (if p 0 = q 0 then 1 else 0) + (if p 0 = q 1 then 1 else 0) +
  (if p 1 = q 0 then 1 else 0) + (if p 1 = q 1 then 1 else 0)

theorem blockCount_pos_iff (p : Fin 2 → α) (e : α) :
    0 < blockCount p e ↔ ∃ k : Fin 2, p k = e := by
  by_cases h0 : p 0 = e <;> by_cases h1 : p 1 = e
  · simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨0, h0⟩
    · intro _; simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨1, h1⟩
    · intro _; simp [blockCount, h0, h1]
  · simp only [blockCount, h0, h1, ↓reduceIte, Nat.add_zero, lt_self_iff_false,
      false_iff, not_exists]
    intro k
    fin_cases k
    · simpa using h0
    · simpa using h1

theorem blockCount_lt_two_iff (p : Fin 2 → α) (e : α) :
    blockCount p e < 2 ↔ ∃ k : Fin 2, p k ≠ e := by
  by_cases h0 : p 0 = e <;> by_cases h1 : p 1 = e
  · simp only [blockCount, h0, h1, ↓reduceIte, Nat.reduceAdd, lt_self_iff_false,
      false_iff, not_exists, not_not]
    intro k
    fin_cases k
    · simpa using h0
    · simpa using h1
  · constructor
    · intro _; exact ⟨1, h1⟩
    · intro _; simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨0, h0⟩
    · intro _; simp [blockCount, h0, h1]
  · constructor
    · intro _; exact ⟨0, h0⟩
    · intro _; simp [blockCount, h0, h1]

def selectorWitness (p : Fin 4 → Fin 2 → α) : Prop :=
  ∃ (ka kb kc kd : Fin 2),
    (p 0 ka = p 1 kb ∧ p 0 ka ≠ p 2 kc ∧ p 0 ka ≠ p 3 kd) ∨
    (p 2 kc = p 3 kd ∧ p 2 kc ≠ p 0 ka ∧ p 2 kc ≠ p 1 kb)

def blockWitness (p : Fin 4 → Fin 2 → α) : Prop :=
  ∃ e : α,
    (0 < blockCount (p 0) e ∧ 0 < blockCount (p 1) e ∧
      blockCount (p 2) e < 2 ∧ blockCount (p 3) e < 2) ∨
    (0 < blockCount (p 2) e ∧ 0 < blockCount (p 3) e ∧
      blockCount (p 0) e < 2 ∧ blockCount (p 1) e < 2)

theorem selectorWitness_iff_blockWitness (p : Fin 4 → Fin 2 → α) :
    selectorWitness p ↔ blockWitness p := by
  simp only [selectorWitness, blockWitness, blockCount_pos_iff,
    blockCount_lt_two_iff]
  constructor
  · rintro ⟨ka, kb, kc, kd, h | h⟩
    · refine ⟨p 0 ka, Or.inl ?_⟩
      exact ⟨⟨ka, rfl⟩, ⟨kb, h.1.symm⟩,
        ⟨kc, Ne.symm h.2.1⟩, ⟨kd, Ne.symm h.2.2⟩⟩
    · refine ⟨p 2 kc, Or.inr ?_⟩
      exact ⟨⟨kc, rfl⟩, ⟨kd, h.1.symm⟩,
        ⟨ka, Ne.symm h.2.1⟩, ⟨kb, Ne.symm h.2.2⟩⟩
  · rintro ⟨e, h | h⟩
    · rcases h with ⟨⟨ka, ha⟩, ⟨kb, hb⟩, ⟨kc, hc⟩, ⟨kd, hd⟩⟩
      refine ⟨ka, kb, kc, kd, Or.inl ?_⟩
      exact ⟨ha.trans hb.symm, by simpa [ha] using Ne.symm hc,
        by simpa [ha] using Ne.symm hd⟩
    · rcases h with ⟨⟨kc, hc⟩, ⟨kd, hd⟩, ⟨ka, ha⟩, ⟨kb, hb⟩⟩
      refine ⟨ka, kb, kc, kd, Or.inr ?_⟩
      exact ⟨hc.trans hd.symm, by simpa [hc] using Ne.symm ha,
        by simpa [hc] using Ne.symm hb⟩

theorem pairCount_four_iff (p q : Fin 2 → α) :
    pairCount p q = 4 ↔ p 0 = p 1 ∧ q 0 = q 1 ∧ p 0 = q 0 := by
  unfold pairCount
  split_ifs <;> simp_all <;> grind

theorem pairCount_one_split (p q : Fin 2 → α) (h : pairCount p q = 1) :
    p 0 ≠ p 1 ∧ q 0 ≠ q 1 := by
  unfold pairCount at h
  split_ifs at h <;> simp_all <;> grind




end GProgram.G5.QuartetKernel

end FullContextModule24

section FullContextModule25
/- Hosted4.35 source variant only. The pinned4.33 source is unchanged.
The old uniformOfFintype PMF API became a measure alias. This variant uses
an actual normalized PMF with the SAME four atom masses1/4 and proves the
unchanged event-count theorem. It has not been accepted by preparation alone.
-/




/-!
# Genuine fair selector probability equals the raw pair count

Contributor: dot, 2026-10-02. The probability law is the uniform PMF on two
actual independent binary selectors. Its co-occupancy probability is proved
from PMF counting, not stored as a requested observation-output field.
Original graph route coins must still be mapped to this law separately.
-/
namespace GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {α : Type*} [DecidableEq α]

def meetingChoices (p q : Fin 2 → α) : Finset (Fin 2 × Fin 2) :=
  Finset.univ.filter (fun k => p k.1 = q k.2)

theorem meetingChoices_card (p q : Fin 2 → α) :
    (meetingChoices p q).card = pairCount p q := by
  rw [Finset.card_eq_sum_ones]
  simp only [meetingChoices, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two, pairCount]
  omega

noncomputable def fairMeetingMass (p q : Fin 2 → α) : ℝ≥0∞ :=
  (PMF.ofFintype (fun _ : Fin 2 × Fin 2 => (1 / 4 : ℝ≥0∞))
    (by
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_two]
      exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num))).toOuterMeasure
    {k | p k.1 = q k.2}

theorem fairMeetingMass_eq_count (p q : Fin 2 → α) :
    fairMeetingMass p q = (pairCount p q : ℝ≥0∞) / 4 := by
  classical
  rw [fairMeetingMass, PMF.toOuterMeasure_ofFintype_apply, tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_setOf_eq]
  change (∑ k : Fin 2 × Fin 2, if p k.1 = q k.2 then (1 / 4 : ℝ≥0∞) else 0) = _
  calc
    _ = ∑ k ∈ meetingChoices p q, (1 / 4 : ℝ≥0∞) := by
      rw [meetingChoices, Finset.sum_filter]
    _ = (pairCount p q : ℝ≥0∞) / 4 := by
      simp [Finset.sum_const, meetingChoices_card, nsmul_eq_mul, div_eq_mul_inv]



end GProgram.G5.QuartetKernel

end FullContextModule25

section FullContextModule26






/-!
# Actual finite original-site fair coin law and pair selector moments

Contributor: dot, 2026-10-02. The finite law uses the already constructed
source-forest product weights on original coin sites, including current-live
token sites for an independent pulse. Marginalizing all other original sites
gives an exact fair two-coordinate law when the retained sites are distinct.
This is an unconditional law, with no no-merger posterior refitting. A whole
continuous source trace, component-route compiler and safe-past disjointness
remain separate source obligations.
-/
namespace GProgram.G5.OriginalCoinLaw
open GProgram.SourceForest
open GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {Site α : Type*} [Fintype Site] [DecidableEq Site]

@[simp] theorem bitWeight_fair (b : Bool) : bitWeight (1 / 2) b = (1 / 2 : ℚ) := by
  cases b <;> norm_num [bitWeight]

/-- Actual joint mass under the original finite product-weight source law. -/
noncomputable def jointBitMass (u v : Site) (a b : Bool) : ℚ := by
  classical
  exact ∑ coin : Site → Bool, independentWeight (1 / 2) coin *
    if coin u = a ∧ coin v = b then 1 else 0

/-- Distinct actual source coin sites have fair independent marginals after
all other site coins are summed out. -/
theorem jointBitMass_eq_quarter {u v : Site} (hne : u ≠ v) (a b : Bool) :
    jointBitMass u v a b = 1 / 4 := by
  classical
  let wanted : Site → Bool := fun s => if s = u then a else b
  have hc : jointBitMass u v a b = coinCylinderMass (1 / 2) {u,v} wanted := by
    simp only [jointBitMass, coinCylinderMass]
    apply Finset.sum_congr rfl
    intro coin hcoin
    simp [wanted, hne, hne.symm]
  rw [hc, coinCylinderMass_eq_retained_product]
  rw [Finset.prod_pair hne]
  simp only [bitWeight_fair]
  norm_num

/-- Every two-coordinate readout is the actual four equally weighted selector
readouts, not a chosen marginal probability interface. -/
theorem fair_two_site_expectation {u v : Site} (hne : u ≠ v)
    (readout : Bool → Bool → ℚ) :
    (∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      readout (coin u) (coin v)) =
      (readout false false + readout false true +
        readout true false + readout true true) / 4 := by
  classical
  have hp : ∀ coin : Site → Bool,
      independentWeight (1 / 2) coin * readout (coin u) (coin v) =
        (independentWeight (1 / 2) coin *
          (if coin u = false ∧ coin v = false then 1 else 0)) * readout false false +
        (independentWeight (1 / 2) coin *
          (if coin u = false ∧ coin v = true then 1 else 0)) * readout false true +
        (independentWeight (1 / 2) coin *
          (if coin u = true ∧ coin v = false then 1 else 0)) * readout true false +
        (independentWeight (1 / 2) coin *
          (if coin u = true ∧ coin v = true then 1 else 0)) * readout true true := by
    intro coin
    cases hu : coin u <;> cases hv : coin v <;> simp [hu,hv]
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]
  change jointBitMass u v false false * readout false false +
      jointBitMass u v false true * readout false true +
      jointBitMass u v true false * readout true false +
      jointBitMass u v true true * readout true true = _
  simp_rw [jointBitMass_eq_quarter hne]
  ring

/-- Standard selector indexing of the two actual source bit values. -/
def binaryPositions (position : Bool → α) : Fin 2 → α :=
  fun i => if i = 0 then position false else position true

/-- Actual unconditional original-site co-occupancy mass equals the raw
selector pair count divided by four. -/
theorem fair_source_meeting_weight [DecidableEq α] {u v : Site} (hne : u ≠ v)
    (p q : Bool → α) :
    (∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      (if p (coin u) = q (coin v) then 1 else 0)) =
      (pairCount (binaryPositions p) (binaryPositions q) : ℚ) / 4 := by
  rw [fair_two_site_expectation hne (fun a b => if p a = q b then 1 else 0)]
  simp only [pairCount, binaryPositions]
  norm_num




end GProgram.G5.OriginalCoinLaw

end FullContextModule26

section FullContextModule27


/-!
# Probability measure for the actual finite original-site product weights

Contributor: dot, 2026-10-02. The PMF is constructed from the existing source
product weights and their proved normalization/nonnegativity. Finite event
probabilities equal the exact rational weighted sums. Thus distinct original
fair source sites give the actual uniform selector co-occupancy PMF mass.
This does not assert a continuous-time source law, safe-past disjointness,
posterior independence or an executable stochastic refinement.
-/
namespace GProgram.G5.OriginalCoinLaw
open GProgram.SourceForest
open GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {Site α : Type*} [Fintype Site] [DecidableEq Site]

theorem independentWeight_real_nonnegative {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (coin : Site → Bool) : 0 ≤ (independentWeight p coin : ℝ) := by
  exact_mod_cast independentWeight_nonnegative hp hp1 coin

theorem independentWeight_ennreal_normalized {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ coin : Site → Bool, ENNReal.ofReal (independentWeight p coin : ℝ)) = 1 := by
  have hr : (∑ coin : Site → Bool, (independentWeight p coin : ℝ)) = 1 := by
    exact_mod_cast independentWeight_normalized Site p
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun coin _ => independentWeight_real_nonnegative hp hp1 coin), hr]
  norm_num

/-- A genuine PMF constructed from the actual finite original-source weights. -/
noncomputable def independentPMF (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    PMF (Site → Bool) :=
  PMF.ofFintype (fun coin => ENNReal.ofReal (independentWeight p coin : ℝ))
    (independentWeight_ennreal_normalized hp hp1)

noncomputable def weightedEvent (p : ℚ) (event : (Site → Bool) → Prop) : ℚ := by
  classical
  exact ∑ coin : Site → Bool, independentWeight p coin * if event coin then 1 else 0

/-- No external probability is fitted: the constructed source PMF event mass
is exactly the original unconditional finite product-weight sum. -/
theorem independentPMF_event {p : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : (Site → Bool) → Prop) :
    (independentPMF p hp hp1).toOuterMeasure {coin | event coin} =
      ENNReal.ofReal (weightedEvent p event : ℝ) := by
  classical
  rw [independentPMF, PMF.toOuterMeasure_ofFintype_apply, tsum_fintype]
  simp only [weightedEvent, Rat.cast_sum, Rat.cast_mul, apply_ite,
    Rat.cast_one, Rat.cast_zero]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro coin hcoin
    by_cases he : event coin <;> simp [Set.indicator, he]
  · intro coin hcoin
    split_ifs
    · simpa using independentWeight_real_nonnegative hp hp1 coin
    · simp

/-- Source finite PMF co-occupancy equals the genuine fair pair selector PMF
mass, for distinct original source sites and arbitrary actual position maps. -/
theorem fair_source_meeting_probability [DecidableEq α] {u v : Site}
    (hne : u ≠ v) (p q : Bool → α) :
    (independentPMF (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure
      {coin | p (coin u) = q (coin v)} =
        fairMeetingMass (binaryPositions p) (binaryPositions q) := by
  classical
  have hw : weightedEvent (1 / 2) (fun coin : Site → Bool => p (coin u) = q (coin v)) =
      (pairCount (binaryPositions p) (binaryPositions q) : ℚ) / 4 := by
    rw [weightedEvent]
    trans ∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      (if p (coin u) = q (coin v) then 1 else 0)
    · apply Finset.sum_congr rfl
      intro coin hcoin
      by_cases hc : p (coin u) = q (coin v) <;> simp [hc]
    · exact fair_source_meeting_weight hne p q
  rw [independentPMF_event, hw, fairMeetingMass_eq_count]
  push_cast
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  simp




end GProgram.G5.OriginalCoinLaw

end FullContextModule27

section FullContextModule28



/-!
# Actual current hybrid-port support and fair original-source pushforward

Contributor: dot, 2026-10-02. Both original parent occurrences exhaust the
binary hybrid's incoming edges. Every actual component path therefore ends
with one of them, and its active population is the constructed parent-position
map. The full root-route support equals that map's image. Distinct original
finite source sites then have the genuine fair-selector co-occupancy law for
these actual graph/calendar positions. Entire safe-past disjointness and the
continuous trace/observed chronology remain separate.
-/
namespace GProgram.G5.ParentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentSupport
open GProgram.G5.OriginalCoinLaw
open GProgram.G5.QuartetKernel
open scoped ENNReal NNReal Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Original indegree TWO and the supplied distinct parent occurrences exhaust
all actual incoming edges, including parallel arcs. -/
theorem incoming_edge_is_original_parent {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) {e : E}
    (ht : N.graph.target e = H.hybrid) : ∃ b : Bool, H.parent b = e := by
  classical
  let incoming : Finset E := Finset.univ.filter (fun f => N.graph.target f = H.hybrid)
  have hsub : ({H.parent0,H.parent1} : Finset E) ⊆ incoming := by
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · simp [incoming,H.target0]
    · simp [incoming,H.target1]
  have hc : incoming.card ≤ ({H.parent0,H.parent1} : Finset E).card := by
    rw [Finset.card_pair H.different]
    exact le_of_eq H.isHybrid.1
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  have hem : e ∈ ({H.parent0,H.parent1} : Finset E) := by
    rw [heq]
    simp [incoming,ht]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hem
  rcases hem with h | h
  · exact ⟨false,h.symm⟩
  · exact ⟨true,h.symm⟩

/-- Any nonempty original edge-ID path has an actual final incoming edge. -/
theorem EdgePath.empty_or_last {G : EdgeGraph V E} {a b : V} {es : List E}
    (p : GProgram.G5.EdgePath G a b es) :
    es = [] ∨ ∃ pre e, es = pre ++ [e] ∧ G.target e = b := by
  have hp := GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse
    (keep := fun _ => True) p (fun _ _ => trivial)
  cases hr : es.reverse with
  | nil => exact Or.inl (List.reverse_inj.mp (by simpa using hr))
  | cons e rest =>
    rw [hr] at hp
    cases hp with
    | cons ht _ _ =>
      exact Or.inr ⟨rest.reverse,e,by
        have heq := congrArg List.reverse hr
        simpa only [List.reverse_reverse,List.reverse_cons] using heq,ht⟩

/-- The actual component support is exactly the image of the ORIGINAL parent
bit current-position map, including coincidence above a joining point. -/
theorem activeComponentEdges_eq_parentPosition_image {N : RootedBinary V E X}
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    activeComponentEdges N.graph C entry H.hybrid t =
      Finset.univ.image (parentPosition C H he hl hu) := by
  classical
  ext f
  rw [mem_activeComponentEdges_iff,Finset.mem_image]
  constructor
  · rintro ⟨es,hp,_,hf,ha⟩
    rcases GProgram.G5.ParentCalendar.EdgePath.empty_or_last hp with hnil | ⟨pre,e,hes,hte⟩
    · rw [hnil] at hf
      simp at hf
    · obtain ⟨b,hbe⟩ := incoming_edge_is_original_parent H hte
      subst e
      rw [hes] at hp hf
      exact ⟨b,Finset.mem_univ _,(active_edge_eq_parentPosition C hcut H he hl hu b hp hf ha).symm⟩
  · rintro ⟨b,_,rfl⟩
    exact ⟨parentRoute H he b,parentRoute_path H he b,parentRoute_nonbridge H he b,
      (parentPosition_spec C H he hl hu b).1,(parentPosition_spec C H he hl hu b).2⟩

/-- The exact parent image also describes ALL complete original root routes. -/
theorem activeRootRouteEdges_eq_parentPosition_image {N : RootedBinary V E X}
    (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : GProgram.G2.OriginalHybridParents N) {entry : V}
    (he : IsComponentEntryFor N entry H.hybrid) {t : ℝ}
    (hl : C.age H.hybrid ≤ t) (hu : t < C.age entry) :
    activeRootRouteEdges N.graph C N.root H.hybrid t =
      Finset.univ.image (parentPosition C H he hl hu) := by
  trans activeComponentEdges N.graph C entry H.hybrid t
  · rcases he with ⟨rfl,hb⟩ | ⟨e,hbridge,rfl,hb⟩
    · exact activeRootRouteEdges_eq_root_component N C hb t
    · exact activeRootRouteEdges_eq_component N C hbridge hb hu
  · exact activeComponentEdges_eq_parentPosition_image C hcut H he hl hu

/-- Genuine source PMF co-occupancy for actual graph/calendar parent positions.
The sites are distinct ORIGINAL source coordinates; safe chronology must still
justify that condition for the retained original representatives. -/
theorem actual_parent_position_fair_meeting_probability
    {Site : Type*} [Fintype Site] [DecidableEq Site]
    {N : RootedBinary V E X} (C : Calendar N.graph)
    (H K : GProgram.G2.OriginalHybridParents N) {entryH entryK : V}
    (heH : IsComponentEntryFor N entryH H.hybrid)
    (heK : IsComponentEntryFor N entryK K.hybrid) {t : ℝ}
    (hlH : C.age H.hybrid ≤ t) (huH : t < C.age entryH)
    (hlK : C.age K.hybrid ≤ t) (huK : t < C.age entryK)
    {u v : Site} (hne : u ≠ v) :
    (independentPMF (1 / 2) (by norm_num) (by norm_num)).toOuterMeasure
      {coin : Site → Bool |
        parentPosition C H heH hlH huH (coin u) =
          parentPosition C K heK hlK huK (coin v)} =
      fairMeetingMass (binaryPositions (parentPosition C H heH hlH huH))
        (binaryPositions (parentPosition C K heK hlK huK)) := by
  classical
  exact fair_source_meeting_probability hne _ _






end GProgram.G5.ParentCalendar

end FullContextModule28

section FullContextModule29



/-!
# Positive original child intervals enforce entire safe-past site separation

Contributor: dot, 2026-10-02. This is a deterministic chronological source
lemma on original edge occurrences and original-tip route families. Absence
of a sure exact nonsingleton block in a stage, together with the stage's
initial invariant, excludes every shared original hybrid up to the stage's
older endpoint. Entire original hybrid-past site sets are therefore disjoint.
It does not construct the observed stochastic support or prove that a deletion
algorithm establishes its initial invariant.
-/
namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Sure exact block over ALL original root-to-tip route families. -/
def SureExactBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  ∀ R : RouteFamily N, ∃ e : E, selectedPopulationBlock N R B C t e = D

/-- No such nonsingleton exact block has occurred at any stage age. -/
def NoSureNontrivialBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s t : ℝ) : Prop :=
  ∀ u : ℝ, s ≤ u → u < t → ∀ D : Finset X, D ⊆ B → 2 ≤ D.card →
    ¬SureExactBlock N C B D u

/-- Initial safe-past invariant, stated only at the stage's younger endpoint. -/
def SafeAt (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s : ℝ) : Prop :=
  ∀ h : V, N.graph.IsHybrid h → C.age h ≤ s →
    (selectedDescendants N B h).card ≤ 1

theorem selectedDescendants_subset (N : RootedBinary V E X)
    (B : Finset X) (h : V) : selectedDescendants N B h ⊆ B := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem protective_sure_exact_block (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e) {u : ℝ}
    (hu : C.age (N.graph.target e) ≤ u ∧ u < C.age h) :
    SureExactBlock N C B (selectedDescendants N B h) u := by
  intro R
  exact ⟨e, protective_population_block_eq N R B C hh hs he hu⟩

/-- A shared hybrid strictly after the stage start creates a sure block at
an earlier actual positive child-edge age, even if that edge straddles s. -/
theorem shared_hybrid_produces_earlier_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} {h : V} (hh : N.graph.IsHybrid h)
    (hs : s < C.age h) (ht : C.age h ≤ t)
    (hcard : 2 ≤ (selectedDescendants N B h).card) :
    ∃ u : ℝ, s ≤ u ∧ u < t ∧
      SureExactBlock N C B (selectedDescendants N B h) u := by
  obtain ⟨e,he,_⟩ := unique_child_edge N hh.2
  have hbridge := hcut e (by simpa only [he] using hh)
  have hage : C.age (N.graph.target e) < C.age h := by
    simpa only [he] using C.edge_older e
  refine ⟨max s (C.age (N.graph.target e)),le_max_left _ _,?_,?_⟩
  · exact (max_lt hs hage).trans_le ht
  · exact protective_sure_exact_block N C B hh he hbridge
      ⟨le_max_right _ _,max_lt hs hage⟩

/-- The safe invariant advances over the ENTIRE original past, including the
older endpoint. Nothing is asserted only about a current component or a
survival-conditioned pair. -/
theorem safeAt_of_no_earlier_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hquiet : NoSureNontrivialBlock N C B s t) : SafeAt N C B t := by
  intro h hh ht
  by_cases hs : C.age h ≤ s
  · exact hstart h hh hs
  · by_contra hc
    have hcard : 2 ≤ (selectedDescendants N B h).card := by omega
    obtain ⟨u,hus,hut,hublock⟩ := shared_hybrid_produces_earlier_sure_block
      N C hcut B hh (lt_of_not_ge hs) ht hcard
    exact hquiet u hus hut (selectedDescendants N B h)
      (selectedDescendants_subset N B h) hcard hublock

/-- Full original hybrid site past: all original hybrids at ages <= t from
which this original tip descends, irrespective of its current route. -/
noncomputable def originalHybridPast (N : RootedBinary V E X)
    (C : Calendar N.graph) (x : X) (t : ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun h => N.graph.IsHybrid h ∧ C.age h ≤ t ∧
    N.graph.DReach h (N.leaf x))

theorem mem_originalHybridPast_iff (N : RootedBinary V E X)
    (C : Calendar N.graph) (x : X) (t : ℝ) (h : V) :
    h ∈ originalHybridPast N C x t ↔
      N.graph.IsHybrid h ∧ C.age h ≤ t ∧ N.graph.DReach h (N.leaf x) := by
  classical
  simp only [originalHybridPast,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Any distinct retained original tips have disjoint ENTIRE past original
hybrid sites whenever the actual source safe invariant holds. -/
theorem originalHybridPast_disjoint (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) {t : ℝ} (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
    Disjoint (originalHybridPast N C x t) (originalHybridPast N C y t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro h hhx hhy
  have hp := (mem_originalHybridPast_iff N C x t h).mp hhx
  have hq := (mem_originalHybridPast_iff N C y t h).mp hhy
  have hcard := hsafe h hp.1 hp.2.1
  have hmemx : x ∈ selectedDescendants N B h := Finset.mem_filter.mpr ⟨hx,hp.2.2⟩
  have hmemy : y ∈ selectedDescendants N B h := Finset.mem_filter.mpr ⟨hy,hq.2.2⟩
  exact hne (Finset.card_le_one.mp hcard x hmemx y hmemy)

/-- Chronological no-sure-block progress gives the full original-site
separation needed before independent source product-law readouts. -/
theorem originalHybridPast_disjoint_of_no_earlier_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hquiet : NoSureNontrivialBlock N C B s t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
    Disjoint (originalHybridPast N C x t) (originalHybridPast N C y t) :=
  originalHybridPast_disjoint N C B
    (safeAt_of_no_earlier_sure_block N C hcut B hstart hquiet) hx hy hne






end GProgram.G5.SafePast

end FullContextModule29

section FullContextModule30


/-!
# Pair-only sure exact blocks on actual original route families

Contributor: dot, 2026-10-02. At a valid calendar age, a nonempty selected
original-label set is a sure exact population block iff all its DISTINCT
inside pairs are surely together and every inside/outside pair is surely
separate. No diagonal pair observation is required. This deterministic
source-support identity advances the safe-past theorem using pair predicates;
recovering these predicates from observed genealogy laws is still separate.
-/
namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Actual simultaneous original-population occupancy on one original route
family. This is not a survival-conditioned stochastic moment. -/
def CoOccupy (N : RootedBinary V E X) (R : RouteFamily N)
    (C : Calendar N.graph) (t : ℝ) (x y : X) : Prop :=
  ∃ e : E, e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e

/-- All predicates use distinct original-label pair readouts. -/
def PairSureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ D, x ≠ y → CoOccupy N R C t x y) ∧
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ B, y ∉ D → ¬CoOccupy N R C t x y)

/-- Complete exact-fiber equivalence, with active positions derived from the
original calendar. The only source-age premises guarantee occupancy exists. -/
theorem sureExactBlock_iff_distinct_pair_predicates
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) {t : ℝ} (hDB : D ⊆ B) (hD : D.Nonempty)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ t) (hu : t < C.age N.root) :
    SureExactBlock N C B D t ↔ PairSureBlock N C B D t := by
  classical
  constructor
  · intro hsure
    constructor
    · intro R x hx y hy _
      obtain ⟨e,he⟩ := hsure R
      have hxm : x ∈ selectedPopulationBlock N R B C t e := by rw [he]; exact hx
      have hym : y ∈ selectedPopulationBlock N R B C t e := by rw [he]; exact hy
      have hxp := (Finset.mem_filter.mp hxm).2
      have hyp := (Finset.mem_filter.mp hym).2
      exact ⟨e,hxp.1,hyp.1,hxp.2⟩
    · intro R x hx y hyB hyD hco
      obtain ⟨e,he⟩ := hsure R
      have hxm : x ∈ selectedPopulationBlock N R B C t e := by rw [he]; exact hx
      have hxp := (Finset.mem_filter.mp hxm).2
      obtain ⟨f,hfx,hfy,hfa⟩ := hco
      have hef := (R.valid x).active_unique C hxp.1 hfx hxp.2 hfa
      subst f
      have hym : y ∈ selectedPopulationBlock N R B C t e :=
        Finset.mem_filter.mpr ⟨hyB,hfy,hxp.2⟩
      exact hyD (by rw [he] at hym; exact hym)
  · intro hpair R
    obtain ⟨x,hxD⟩ := hD
    obtain ⟨e,hem,hea⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists
      C (R.valid x) (hl x (hDB hxD)) hu
    refine ⟨e,?_⟩
    ext y
    constructor
    · intro hym
      have hyp := Finset.mem_filter.mp hym
      by_contra hyD
      exact hpair.2 R x hxD y hyp.1 hyD ⟨e,hem,hyp.2.1,hea⟩
    · intro hyD
      apply Finset.mem_filter.mpr
      refine ⟨hDB hyD,?_,hea⟩
      by_cases hxy : x = y
      · subst y
        exact hem
      · obtain ⟨f,hfx,hfy,hfa⟩ := hpair.1 R x hxD y hyD hxy
        have hef := (R.valid x).active_unique C hem hfx hea hfa
        subst f
        exact hfy

/-- The stage's absence test can be stated entirely in pair predicates. -/
def NoPairSureNontrivialBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s t : ℝ) : Prop :=
  ∀ u : ℝ, s ≤ u → u < t → ∀ D : Finset X, D ⊆ B → 2 ≤ D.card →
    ¬PairSureBlock N C B D u

/-- At valid original-tip ages the pair-only absence test equals the full
sure-exact-block absence test, without a triple or four-label input. -/
theorem noSureNontrivialBlock_iff_pair_predicates
    (N : RootedBinary V E X) (C : Calendar N.graph) (B : Finset X)
    {s t : ℝ} (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hu : t ≤ C.age N.root) :
    NoSureNontrivialBlock N C B s t ↔ NoPairSureNontrivialBlock N C B s t := by
  have heq (u : ℝ) (hs : s ≤ u) (ht : u < t) (D : Finset X)
      (hDB : D ⊆ B) (hc : 2 ≤ D.card) :
      SureExactBlock N C B D u ↔ PairSureBlock N C B D u := by
    apply sureExactBlock_iff_distinct_pair_predicates N C B D hDB
    · apply Finset.card_pos.mp
      omega
    · intro x hx
      exact (hl x hx).trans hs
    · exact ht.trans_le hu
  constructor
  · intro hquiet u hs ht D hDB hc hp
    exact hquiet u hs ht D hDB hc ((heq u hs ht D hDB hc).mpr hp)
  · intro hquiet u hs ht D hDB hc hp
    exact hquiet u hs ht D hDB hc ((heq u hs ht D hDB hc).mp hp)

/-- The advanced entire-safe-past invariant needs only the distinct-label
pair sure-together / sure-separate predicates on its stage interval. -/
theorem safeAt_of_no_earlier_pair_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hu : t ≤ C.age N.root)
    (hquiet : NoPairSureNontrivialBlock N C B s t) : SafeAt N C B t :=
  safeAt_of_no_earlier_sure_block N C hcut B hstart
    ((noSureNontrivialBlock_iff_pair_predicates N C B hl hu).mpr hquiet)




end GProgram.G5.SafePast

end FullContextModule30

section FullContextModule31


/-!
# Actual original-route meetings cannot separate during an entire safe past

Contributor: dot, 2026-10-02. Rootward paths retain original parallel arc IDs.
Two routes with a common younger population can first diverge rootward only
at a hybrid. The entire-safe-past invariant excludes that shared hybrid, so
co-occupancy persists through every older safe calendar age. No survival law,
posterior route distribution or continuous stochastic process is assumed.
-/
namespace GProgram.G5.NonbridgeRoutes
open Nanuq.Source
variable {V E : Type*}

theorem UpPath.to_edgePath_reverse {G : EdgeGraph V E} {keep : E → Prop}
    {a b : V} {es : List E} (p : UpPath G keep a b es) :
    GProgram.G5.EdgePath G b a es.reverse := by
  induction p with
  | nil a => exact .nil a
  | @cons a b e es ht he rest ih =>
    have hs : GProgram.G5.EdgePath G (G.source e) a [e] :=
      .cons rfl (by rw [ht]; exact .nil _)
    simpa only [List.reverse_cons] using ih.append hs


end GProgram.G5.NonbridgeRoutes

namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Two selected descendants at a processed age cannot share that original
hybrid; the claim concerns the whole original descendant relation. -/
theorem shared_ancestor_not_hybrid (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) {t : ℝ} (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    {v : V} (hvx : N.graph.DReach v (N.leaf x))
    (hvy : N.graph.DReach v (N.leaf y)) (hvt : C.age v ≤ t) :
    ¬N.graph.IsHybrid v := by
  classical
  intro hh
  have hc := hsafe v hh hvt
  exact hne (Finset.card_le_one.mp hc x
    (Finset.mem_filter.mpr ⟨hx,hvx⟩) y (Finset.mem_filter.mpr ⟨hy,hvy⟩))

/-- Active populations of two rootward original paths agree if every shared
ancestor processed by this age is ordinary. This premise is vertex degree
information, not the active-edge equality conclusion. -/
theorem UpPath.active_edges_equal_of_no_processed_hybrid
    (N : RootedBinary V E X) (C : Calendar N.graph) {t : ℝ}
    {a b : V} {es fs : List E} (p : UpPath N.graph (fun _ => True) a b es)
    (q : UpPath N.graph (fun _ => True) a b fs)
    (hl : C.age a ≤ t) (hu : t < C.age b)
    (ho : ∀ v, N.graph.DReach v a → C.age v ≤ t → ¬N.graph.IsHybrid v)
    {f g : E} (hf : f ∈ es) (hg : g ∈ fs) (hfa : C.Active t f) (hga : C.Active t g) :
    f = g := by
  induction p generalizing fs f g with
  | nil a => exact False.elim (not_lt_of_ge hl hu)
  | @cons a b e es ht he rest ih =>
    cases q with
    | nil => exact False.elim (not_lt_of_ge hl hu)
    | @cons _ _ d ds htd hd qrest =>
      have hed : e = d := incoming_equal_of_indegree_le_one N
        (nonhybrid_indegree_le_one N (ho a .refl hl)) ht htd
      subst d
      by_cases hls : C.age (N.graph.source e) ≤ t
      · have hfn : f ≠ e := by
          intro h
          subst f
          exact not_lt_of_ge hls hfa.2
        have hgn : g ≠ e := by
          intro h
          subst g
          exact not_lt_of_ge hls hga.2
        have hft : f ∈ es := (List.mem_cons.mp hf).resolve_left hfn
        have hgt : g ∈ ds := (List.mem_cons.mp hg).resolve_left hgn
        apply ih qrest hls hu _ hft hgt hfa hga
        intro v hva hvage
        exact ho v (hva.tail ⟨e,rfl,ht⟩) hvage
      · have hae : C.Active t e := ⟨by simpa only [ht] using hl,lt_of_not_ge hls⟩
        have hfe : f = e := (UpPath.to_edgePath_reverse (.cons ht he rest)).active_unique
          C (List.mem_reverse.mpr hf) (List.mem_reverse.mpr List.mem_cons_self) hfa hae
        have hge : g = e := (UpPath.to_edgePath_reverse (.cons htd hd qrest)).active_unique
          C (List.mem_reverse.mpr hg) (List.mem_reverse.mpr List.mem_cons_self) hga hae
        exact hfe.trans hge.symm

/-- A younger original pair meeting persists to any older age covered by the
entire safe-past invariant. The routes themselves are arbitrary originals. -/
theorem coOccupy_persists_to_safe_age (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) (R : RouteFamily N)
    {u t : ℝ} (hut : u ≤ t) (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hmeeting : CoOccupy N R C u x y) : CoOccupy N R C t x y := by
  obtain ⟨e,hex,hey,heactive⟩ := hmeeting
  by_cases hls : C.age (N.graph.source e) ≤ t
  · obtain ⟨px,sx,hxroute,hpx,hsx⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (R.valid x) hex
    obtain ⟨py,sy,hyroute,hpy,hsy⟩ :=
      GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge (R.valid y) hey
    obtain ⟨f,hfx,hfa⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hpx hls hu
    obtain ⟨g,hgy,hga⟩ := GProgram.G5.ComponentCalendar.EdgePath.active_exists C hpy hls hu
    have hdx : N.graph.DReach (N.graph.source e) (N.leaf x) :=
      (Relation.ReflTransGen.single ⟨e,rfl,rfl⟩).trans hsx.directed
    have hdy : N.graph.DReach (N.graph.source e) (N.leaf y) :=
      (Relation.ReflTransGen.single ⟨e,rfl,rfl⟩).trans hsy.directed
    have hfg : f = g := UpPath.active_edges_equal_of_no_processed_hybrid N C
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hpx (fun _ _ => trivial))
      (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hpy (fun _ _ => trivial))
      hls hu (fun v hv hvage => shared_ancestor_not_hybrid N C B hsafe hx hy hne
        (hv.trans hdx) (hv.trans hdy) hvage)
      (List.mem_reverse.mpr hfx) (List.mem_reverse.mpr hgy) hfa hga
    subst g
    refine ⟨f,?_,?_,hfa⟩
    · rw [hxroute]
      exact List.mem_append_left _ hfx
    · rw [hyroute]
      exact List.mem_append_left _ hgy
  · exact ⟨e,hex,hey,heactive.1.trans hut,lt_of_not_ge hls⟩

/-- Contrapositive: current separation on a safe age means that these original
routes were separate at EVERY younger age, not just at the stage start. -/
theorem separated_at_safe_age_never_previously_met (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hseparate : ¬CoOccupy N R C t x y) :
    ∀ u : ℝ, u ≤ t → ¬CoOccupy N R C u x y := by
  intro u hut hm
  exact hseparate (coOccupy_persists_to_safe_age N C B R hut hu hsafe hx hy hne hm)





end GProgram.G5.SafePast

end FullContextModule31

section FullContextModule32





/-!
# Finite exponential right-germ identification, with unknown rates

New proof contribution: dot's active source-assumption-first Lean lane,
2026-10-02. A finite exponential sum's coefficients are uniquely determined
on ANY right interval [0, epsilon), without a supplied event grid, derivative
oracle, or global common rate. The proof takes finitely many equally spaced
samples strictly within that interval and proves the resulting Vandermonde
matrix nonsingular. Rates can be arbitrary distinct real numbers.

For the G5 terminal-hybrid source argument, union the two finite rate sets,
append zero coefficients at missing rates, and include the zero exponent.
Equality of survival right germs then implies equality of its constant term.
That term equals not-yet-met routing mass only after the source-specific
permanent-pair-meeting and positive-current-rate argument; no such source
interpretation is assumed or proved by this algebraic/analytic module.
-/

namespace GProgram.G5.ExponentialGerm

open scoped BigOperators
open Matrix

noncomputable def expSum {n : ℕ} (rate coeff : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, coeff i * Real.exp (rate i * s)

/-- Finite nonzero-step exponential samples have full-rank coefficient map. -/
theorem coefficient_zero_of_grid {n : ℕ} (rate coeff : Fin n → ℝ)
    (hrate : Function.Injective rate) {step : ℝ} (hstep : step ≠ 0)
    (h : ∀ j : Fin n, expSum rate coeff (step * (j.val : ℝ)) = 0) :
    coeff = 0 := by
  have hnodes : Function.Injective (fun i : Fin n => Real.exp (rate i * step)) := by
    intro i j hij
    exact hrate (mul_right_cancel₀ hstep (Real.exp_injective hij))
  apply Matrix.eq_zero_of_vecMul_eq_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)
  funext j
  change (∑ i : Fin n, coeff i * Real.exp (rate i * step) ^ j.val) = 0
  convert h j using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- An entire right germ identifies ALL coefficients, not just a derivative
at one supplied order. The sample step is constructed inside the interval. -/
theorem coefficients_eq_of_right_germ {n : ℕ} (rate c d : Fin n → ℝ)
    (hrate : Function.Injective rate) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → expSum rate c s = expSum rate d s) : c = d := by
  let step : ℝ := ε / ((n + 1 : ℕ) : ℝ)
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hstep : 0 < step := div_pos hε hn
  have hzero : c - d = 0 := by
    apply coefficient_zero_of_grid rate (c - d) hrate hstep.ne'
    intro j
    have hj : (j.val : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.lt_trans j.isLt (Nat.lt_succ_self n))
    have hlt : step * (j.val : ℝ) < ε := by
      calc
        step * (j.val : ℝ) < step * ((n + 1 : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_left hj hstep
        _ = ε := div_mul_cancel₀ ε hn.ne'
    have heq := h (step * (j.val : ℝ)) (mul_nonneg hstep.le (Nat.cast_nonneg _)) hlt
    simpa only [expSum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
      using heq
  exact sub_eq_zero.mp hzero

/-- In particular the exponent-zero coefficient is observable. No numerical
values of the other positive/negative exponents need be supplied to the
comparison. Their finite union is only a proof-level common presentation. -/
theorem constant_coefficient_eq_of_right_germ {n : ℕ} (rate c d : Fin n → ℝ)
    (hrate : Function.Injective rate) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → expSum rate c s = expSum rate d s)
    (zeroIndex : Fin n) (_hz : rate zeroIndex = 0) : c zeroIndex = d zeroIndex := by
  exact congrFun (coefficients_eq_of_right_germ rate c d hrate hε h) zeroIndex





end GProgram.G5.ExponentialGerm

end FullContextModule32

section FullContextModule33



/-!
# Exponential right germs identify different unsupplied rate supports

New proof contribution: dot's active Lean source-bridge lane, 2026-10-02.
Each law is an intrinsic finitely supported real exponent coefficient map.
No common rate list, calibrated hidden clocks, positivity, or event grid is
supplied. Equal right germs identify the whole map and its zero-rate mass.
Actual source routing/permanent-meeting interpretation remains separate.
-/

namespace GProgram.G5.ExponentialGerm

open scoped BigOperators

noncomputable def finiteExpSum (c : ℝ →₀ ℝ) (s : ℝ) : ℝ :=
  c.sum (fun rate weight => weight * Real.exp (rate * s))

theorem finite_coefficients_zero_of_right_germ (c : ℝ →₀ ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → finiteExpSum c s = 0) : c = 0 := by
  classical
  let e := (Fintype.equivFin {r : ℝ // r ∈ c.support}).symm
  let rate := fun i => (e i).val
  let coeff := fun i => c (rate i)
  have hrate : Function.Injective rate := Subtype.val_injective.comp e.injective
  have hpres (s : ℝ) : expSum rate coeff s = finiteExpSum c s := by
    change (∑ i, c (e i).val * Real.exp ((e i).val * s)) =
      ∑ r ∈ c.support, c r * Real.exp (r * s)
    rw [Fintype.sum_equiv e (fun i => c (e i).val * Real.exp ((e i).val * s))
      (fun r => c r.val * Real.exp (r.val * s)) (fun _ => rfl)]
    exact Finset.sum_attach c.support (fun r => c r * Real.exp (r * s))
  have hc : coeff = 0 := by
    apply coefficients_eq_of_right_germ rate coeff 0 hrate hε
    intro s hs hse
    rw [hpres, h s hs hse]
    simp [expSum]
  ext r
  by_cases hr : r ∈ c.support
  · have hi := congrFun hc (e.symm ⟨r, hr⟩)
    simpa [coeff, rate] using hi
  · exact Finsupp.notMem_support_iff.mp hr

theorem finite_coefficients_eq_of_right_germ (c d : ℝ →₀ ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → finiteExpSum c s = finiteExpSum d s) : c = d := by
  apply sub_eq_zero.mp
  apply finite_coefficients_zero_of_right_germ (c - d) hε
  intro s hs hse
  rw [finiteExpSum, Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _)]
  exact sub_eq_zero.mpr (h s hs hse)

theorem finite_constant_mass_eq_of_right_germ (c d : ℝ →₀ ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → finiteExpSum c s = finiteExpSum d s) : c 0 = d 0 := by
  exact congrArg (fun f : ℝ →₀ ℝ => f 0)
    (finite_coefficients_eq_of_right_germ c d hε h)





end GProgram.G5.ExponentialGerm

end FullContextModule33

section FullContextModule34




/-!
# Original calendar route-pair hazard and its exact local exponential germ

Contributor: dot, 2026-10-02. Exposure is constructed from every original
edge's actual active interval and positive edge-specific pair rates. A safe
currently separated route pair has zero ENTIRE-past exposure. Finiteness of
original node clocks supplies a right-hand event-free window. The route
functional exp(-hazard) then has its actual current-rate exponential germ.
Identifying this functional with a continuous-time source probability law is
a separate stochastic construction, not a premise hidden in this definition.
-/
namespace GProgram.G5.RouteHazard
open Nanuq.Source
open GProgram.G5
open GProgram.G5.SafePast
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- Length of this original edge's active interval below calendar age t. -/
noncomputable def exposure (G : EdgeGraph V E) (C : Calendar G) (t : ℝ) (e : E) : ℝ :=
  max 0 (min t (C.age (G.source e)) - C.age (G.target e))

/-- Actual finite original-edge overlap exposure, retaining parallel IDs. -/
noncomputable def accumulatedHazard (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (R : RouteFamily N) (x y : X) (t : ℝ) : ℝ := by
  classical
  exact ∑ e : E, if e ∈ R.edges x ∧ e ∈ R.edges y then rate e * exposure N.graph C t e else 0

noncomputable def currentPairRate (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (R : RouteFamily N) (x y : X) (t : ℝ) : ℝ := by
  classical
  exact ∑ e : E, if e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e then rate e else 0

noncomputable def routeSurvival (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (R : RouteFamily N) (x y : X) (t : ℝ) : ℝ :=
  Real.exp (-accumulatedHazard N C rate R x y t)

theorem currentPairRate_nonnegative (N : RootedBinary V E X) (C : Calendar N.graph)
    (rate : E → ℝ) (hr : ∀ e, 0 ≤ rate e) (R : RouteFamily N) (x y : X) (t : ℝ) :
    0 ≤ currentPairRate N C rate R x y t := by
  classical
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact hr e
  · exact le_refl _

/-- Strict source rates make zero current rate equivalent to true separation. -/
theorem currentPairRate_zero_iff_separated (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (hr : ∀ e, 0 < rate e)
    (R : RouteFamily N) (x y : X) (t : ℝ) :
    currentPairRate N C rate R x y t = 0 ↔ ¬CoOccupy N R C t x y := by
  classical
  have hn : ∀ e ∈ (Finset.univ : Finset E),
      0 ≤ (if e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e then rate e else 0) := by
    intro e _
    split_ifs
    · exact (hr e).le
    · exact le_refl _
  rw [currentPairRate,Finset.sum_eq_zero_iff_of_nonneg hn]
  constructor
  · intro hz hm
    obtain ⟨e,hex,hey,hea⟩ := hm
    have hez := hz e (Finset.mem_univ e)
    simp only [hex,hey,hea,and_self,if_true] at hez
    exact (hr e).ne' hez
  · intro hs e _
    have he : ¬(e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e) := by
      rintro ⟨hx,hy,ha⟩
      exact hs ⟨e,hx,hy,ha⟩
    simp only [he,if_false]

/-- Full safe-past permanence gives zero overlap duration, rather than merely
zero current occupancy, for every separated original route pair. -/
theorem separated_safe_accumulatedHazard_zero (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hs : ¬CoOccupy N R C t x y) : accumulatedHazard N C rate R x y t = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  by_cases hm : e ∈ R.edges x ∧ e ∈ R.edges y
  · have ht : t ≤ C.age (N.graph.target e) := by
      by_contra hn
      exact (separated_at_safe_age_never_previously_met N C B R hu hsafe hx hy hne hs)
        (C.age (N.graph.target e)) (le_of_lt (lt_of_not_ge hn))
        ⟨e,hm.1,hm.2,le_refl _,C.edge_older e⟩
    have he : exposure N.graph C t e = 0 := by
      apply max_eq_left
      exact sub_nonpos.mpr ((min_le_left _ _).trans ht)
    simp [hm,he]
  · simp only [hm,if_false]

theorem separated_safe_routeSurvival_one (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hs : ¬CoOccupy N R C t x y) : routeSurvival N C rate R x y t = 1 := by
  rw [routeSurvival,separated_safe_accumulatedHazard_zero N C rate B R hu hsafe hx hy hne hs]
  simp

/-- A right event-free window does not assume the unknown clock grid is observed. -/
def EndpointGap (G : EdgeGraph V E) (C : Calendar G) (t ε : ℝ) : Prop :=
  ∀ v : V, t < C.age v → t + ε ≤ C.age v

theorem positive_endpoint_gap_exists (N : RootedBinary V E X)
    (C : Calendar N.graph) (t : ℝ) : ∃ ε : ℝ, 0 < ε ∧ EndpointGap N.graph C t ε := by
  classical
  let S : Finset ℝ := (Finset.univ.image C.age).filter (fun a => t < a)
  by_cases hS : S.Nonempty
  · refine ⟨S.min' hS - t,?_,?_⟩
    · exact sub_pos.mpr (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
    · intro v hv
      have hm : C.age v ∈ S := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,hv⟩
      have hmin := Finset.min'_le S (C.age v) hm
      linarith
  · refine ⟨1,by norm_num,?_⟩
    intro v hv
    apply False.elim
    apply hS
    exact ⟨C.age v,Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩,hv⟩⟩

/-- The exact slope of original-edge exposure on a right event-free window. -/
theorem exposure_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε)
    (hu : 0 ≤ u) (huε : u < ε) (e : E) :
    exposure N.graph C (t + u) e = exposure N.graph C t e +
      if C.Active t e then u else 0 := by
  classical
  have htu : t ≤ t + u := by linarith
  by_cases hy : C.age (N.graph.target e) ≤ t
  · by_cases hs : t < C.age (N.graph.source e)
    · have hst : t + u < C.age (N.graph.source e) := by
        have hg := hgap (N.graph.source e) hs
        linarith
      simp only [exposure,min_eq_left hs.le,min_eq_left hst.le,
        max_eq_right (sub_nonneg.mpr hy),max_eq_right (sub_nonneg.mpr (hy.trans htu)),
        Calendar.Active,hy,hs,and_self,if_true]
      ring
    · have hst : C.age (N.graph.source e) ≤ t := le_of_not_gt hs
      have ha : ¬C.Active t e := fun h => hs h.2
      simp only [exposure,min_eq_right hst,min_eq_right (hst.trans htu),ha,if_false,add_zero]
  · have hyt : t < C.age (N.graph.target e) := lt_of_not_ge hy
    have hyu : t + u < C.age (N.graph.target e) := by
      have hg := hgap (N.graph.target e) hyt
      linarith
    have ht0 : min t (C.age (N.graph.source e)) - C.age (N.graph.target e) ≤ 0 :=
      sub_nonpos.mpr ((min_le_left _ _).trans hyt.le)
    have htu0 : min (t+u) (C.age (N.graph.source e)) - C.age (N.graph.target e) ≤ 0 :=
      sub_nonpos.mpr ((min_le_left _ _).trans hyu.le)
    have ha : ¬C.Active t e := fun h => hy h.1
    simp only [exposure,max_eq_left ht0,max_eq_left htu0,ha,if_false,add_zero]

/-- Actual calendar exposure produces the current-rate linear germ. -/
theorem accumulatedHazard_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (R : RouteFamily N) (x y : X)
    {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε) (hu : 0 ≤ u) (huε : u < ε) :
    accumulatedHazard N C rate R x y (t+u) = accumulatedHazard N C rate R x y t +
      currentPairRate N C rate R x y t * u := by
  classical
  rw [accumulatedHazard,accumulatedHazard,currentPairRate,Finset.sum_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [exposure_add_on_endpoint_gap N C hgap hu huε]
  by_cases hm : e ∈ R.edges x ∧ e ∈ R.edges y <;>
    by_cases ha : C.Active t e <;> simp [hm,ha] <;> ring

/-- The exponential route functional has the exact constructed local source
rate. The actual continuous-time no-merger-law interpretation remains open. -/
theorem routeSurvival_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (R : RouteFamily N) (x y : X)
    {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε) (hu : 0 ≤ u) (huε : u < ε) :
    routeSurvival N C rate R x y (t+u) = routeSurvival N C rate R x y t *
      Real.exp ((-currentPairRate N C rate R x y t) * u) := by
  rw [routeSurvival,accumulatedHazard_add_on_endpoint_gap N C rate R x y hgap hu huε,
    neg_add,Real.exp_add]
  simp only [routeSurvival,neg_mul]








end GProgram.G5.RouteHazard

end FullContextModule34

section FullContextModule35







/-!
G4 two-current-root private source compiler and observable size certificate.

The Boolean route table is explicit. A previously merged pair is one absorbing
root, so it does not receive two fresh coins at a later cell. The observation is
the A-only cherry in the rooted three-leaf restriction, after fixed positive
ordinary padding, with an ordinary three-root first pair chosen uniformly.

This proves the exact finite two-root algebra and conditional rival-wide length
certificate. It does not formalize a full source-graph admission checker, general
Kingman projectivity/pruning, the all-copy normal form, or the bounded-length
full-forest QE algorithm. Those are separate package obligations.
-/

namespace G4TwoRootSourceStopping

structure PositiveEdge where
  survival : ℝ
  positive : 0 < survival
  below_one : survival < 1

structure PositiveBigon where
  x : ℝ
  y : ℝ
  g : ℝ
  x_positive : 0 < x
  x_below_one : x < 1
  y_positive : 0 < y
  y_below_one : y < 1
  g_positive : 0 < g
  g_below_one : g < 1

def coinWeight (g : ℝ) (choice : Bool) : ℝ :=
  if choice then g else 1 - g

def pairRouteSurvival (x y : ℝ) (a b : Bool) : ℝ :=
  if a then (if b then x else 1) else (if b then 1 else y)

def bareSurvival (B : PositiveBigon) : ℝ :=
  ∑ a : Bool, ∑ b : Bool,
    coinWeight B.g a * coinWeight B.g b * pairRouteSurvival B.x B.y a b

theorem bareSurvival_eq (B : PositiveBigon) :
    bareSurvival B = B.g ^ 2 * B.x + (1 - B.g) ^ 2 * B.y +
      2 * B.g * (1 - B.g) := by
  simp [bareSurvival, coinWeight, pairRouteSurvival]
  <;> ring

theorem routing_normalized (g : ℝ) :
    (∑ a : Bool, ∑ b : Bool, coinWeight g a * coinWeight g b) = 1 := by
  simp [coinWeight]
  <;> ring

theorem bareSurvival_defect (B : PositiveBigon) :
    bareSurvival B = 1 - B.g ^ 2 * (1 - B.x) -
      (1 - B.g) ^ 2 * (1 - B.y) := by
  rw [bareSurvival_eq]
  ring

theorem bareSurvival_positive (B : PositiveBigon) : 0 < bareSurvival B := by
  rw [bareSurvival_eq]
  have hx := B.x_positive
  have hy := B.y_positive
  have hg := B.g_positive
  have hh : 0 < 1 - B.g := sub_pos.mpr B.g_below_one
  positivity

theorem bareSurvival_below_one (B : PositiveBigon) : bareSurvival B < 1 := by
  rw [bareSurvival_defect]
  have hleft : 0 < B.g ^ 2 * (1 - B.x) :=
    mul_pos (sq_pos_of_pos B.g_positive) (sub_pos.mpr B.x_below_one)
  have hright : 0 ≤ (1 - B.g) ^ 2 * (1 - B.y) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (sub_pos.mpr B.y_below_one))
  linarith

structure Cell where
  bigon : PositiveBigon
  connector : PositiveEdge

def cellSurvival (C : Cell) : ℝ :=
  bareSurvival C.bigon * C.connector.survival

theorem cellSurvival_positive (C : Cell) : 0 < cellSurvival C :=
  mul_pos (bareSurvival_positive C.bigon) C.connector.positive

theorem cellSurvival_le_bare (C : Cell) : cellSurvival C ≤ bareSurvival C.bigon := by
  dsimp [cellSurvival]
  have hp := bareSurvival_positive C.bigon
  have hq := C.connector.below_one
  nlinarith

theorem cellSurvival_below_one (C : Cell) : cellSurvival C < 1 :=
  lt_of_le_of_lt (cellSurvival_le_bare C) (bareSurvival_below_one C.bigon)

-- The merged state is absorbing. Only the unmerged state is routed twice.
def serialMerged (p q : ℝ) : ℝ := (1 - p) * 1 + p * (1 - q)
def serialUnmerged (p q : ℝ) : ℝ := p * q

theorem serial_pair_kernel (p q : ℝ) :
    serialMerged p q = 1 - serialUnmerged p q := by
  dsimp [serialMerged, serialUnmerged]
  ring

def tailSurvival : List Cell → ℝ
  | [] => 1
  | C :: rest => serialUnmerged (cellSurvival C) (tailSurvival rest)

structure PositiveChain where
  leading : PositiveEdge
  cells : List Cell

def sourceSurvival (K : PositiveChain) : ℝ :=
  serialUnmerged K.leading.survival (tailSurvival K.cells)

theorem tailSurvival_positive (cells : List Cell) : 0 < tailSurvival cells := by
  induction cells with
  | nil => simp [tailSurvival]
  | cons C rest ih =>
      exact mul_pos (cellSurvival_positive C) ih

theorem tailSurvival_le_one (cells : List Cell) : tailSurvival cells ≤ 1 := by
  induction cells with
  | nil => simp [tailSurvival]
  | cons C rest ih =>
      change cellSurvival C * tailSurvival rest ≤ 1
      have hc := cellSurvival_below_one C
      have hcp := cellSurvival_positive C
      have htp := tailSurvival_positive rest
      nlinarith

theorem sourceSurvival_positive (K : PositiveChain) : 0 < sourceSurvival K :=
  mul_pos K.leading.positive (tailSurvival_positive K.cells)

theorem sourceSurvival_below_one (K : PositiveChain) : sourceSurvival K < 1 := by
  change K.leading.survival * tailSurvival K.cells < 1
  have hp := K.leading.positive
  have ht := tailSurvival_positive K.cells
  have hlt := K.leading.below_one
  have hle := tailSurvival_le_one K.cells
  nlinarith

theorem tailSurvival_le_power (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ cells : List Cell, (∀ C ∈ cells, cellSurvival C ≤ ρ) →
      tailSurvival cells ≤ ρ ^ cells.length := by
  intro cells
  induction cells with
  | nil => intro _; simp [tailSurvival]
  | cons C rest ih =>
      intro hcells
      have hc : cellSurvival C ≤ ρ := hcells C (by simp)
      have hrest : tailSurvival rest ≤ ρ ^ rest.length :=
        ih (fun D hD => hcells D (by simp [hD]))
      have hm : cellSurvival C * tailSurvival rest ≤ ρ * ρ ^ rest.length :=
        mul_le_mul hc hrest (le_of_lt (tailSurvival_positive rest)) hρ
      simpa [tailSurvival, serialUnmerged, pow_succ, mul_comm] using hm

def UniformContractionClass (ρ : ℝ) (K : PositiveChain) : Prop :=
  ∀ C ∈ K.cells, bareSurvival C.bigon ≤ ρ

theorem sourceSurvival_le_power (ρ : ℝ) (hρ : 0 ≤ ρ)
    (K : PositiveChain) (hK : UniformContractionClass ρ K) :
    sourceSurvival K ≤ ρ ^ K.cells.length := by
  have hc : ∀ C ∈ K.cells, cellSurvival C ≤ ρ :=
    fun C hC => le_trans (cellSurvival_le_bare C) (hK C hC)
  have ht := tailSurvival_le_power ρ hρ K.cells hc
  have hp := tailSurvival_positive K.cells
  have hlead := K.leading.below_one
  change K.leading.survival * tailSurvival K.cells ≤ ρ ^ K.cells.length
  have hpad : K.leading.survival * tailSurvival K.cells ≤ tailSurvival K.cells := by
    nlinarith
  exact le_trans hpad ht

-- A-only merger before joining B forces the rooted A-cherry. With three
-- unmerged roots, exactly one of the three equally likely first pairs does so.
noncomputable def rootedACladeResponse (before after : PositiveEdge) (p : ℝ) : ℝ :=
  let r := before.survival * after.survival * p
  (1 - r) * 1 + r * (1 / 3)

theorem rootedACladeResponse_eq (before after : PositiveEdge) (p : ℝ) :
    rootedACladeResponse before after p =
      1 - (2 / 3) * before.survival * after.survival * p := by
  dsimp [rootedACladeResponse]
  ring

theorem rootedACladeResponse_injective (before after : PositiveEdge) :
    Function.Injective (rootedACladeResponse before after) := by
  intro p q h
  rw [rootedACladeResponse_eq, rootedACladeResponse_eq] at h
  have hmul : before.survival * after.survival * p =
      before.survival * after.survival * q := by linarith
  exact mul_left_cancel₀ (ne_of_gt (mul_pos before.positive after.positive)) hmul

theorem rootedACladeResponse_is_probability
    (before after : PositiveEdge) (K : PositiveChain) :
    (1 / 3 : ℝ) < rootedACladeResponse before after (sourceSurvival K) ∧
      rootedACladeResponse before after (sourceSurvival K) < 1 := by
  have hcoef : 0 < before.survival * after.survival :=
    mul_pos before.positive after.positive
  have hcoef1 : before.survival * after.survival < 1 := by
    calc
      before.survival * after.survival < before.survival * 1 :=
        mul_lt_mul_of_pos_left after.below_one before.positive
      _ = before.survival := mul_one _
      _ < 1 := before.below_one
  have hr : 0 < before.survival * after.survival * sourceSurvival K :=
    mul_pos hcoef (sourceSurvival_positive K)
  have hr1 : before.survival * after.survival * sourceSurvival K < 1 := by
    calc
      before.survival * after.survival * sourceSurvival K <
          (before.survival * after.survival) * 1 :=
        mul_lt_mul_of_pos_left (sourceSurvival_below_one K) hcoef
      _ = before.survival * after.survival := mul_one _
      _ < 1 := hcoef1
  rw [rootedACladeResponse_eq]
  constructor <;> nlinarith

-- This premise is explicitly about every rival. No target-only margin is used.
def RivalEnvelope (C : PositiveChain → Prop) (U : ℕ → ℝ) : Prop :=
  ∀ K : PositiveChain, C K → sourceSurvival K ≤ U K.cells.length

theorem uniform_contraction_envelope (ρ : ℝ) (hρ : 0 ≤ ρ) :
    RivalEnvelope (UniformContractionClass ρ) (fun n => ρ ^ n) := by
  intro K hK
  exact sourceSurvival_le_power ρ hρ K hK

theorem certified_crossing_length_bound
    (C : PositiveChain → Prop) (U : ℕ → ℝ)
    (hU : Antitone U) (henv : RivalEnvelope C U)
    (target rival : PositiveChain) (before after : PositiveEdge)
    (hrival : C rival)
    (hobs : rootedACladeResponse before after (sourceSurvival rival) =
      rootedACladeResponse before after (sourceSurvival target))
    (b : ℕ) (hcross : U b < sourceSurvival target) :
    rival.cells.length < b := by
  have heq : sourceSurvival rival = sourceSurvival target :=
    rootedACladeResponse_injective before after hobs
  by_contra hnot
  have hb : b ≤ rival.cells.length := Nat.le_of_not_gt hnot
  have hupper : sourceSurvival rival ≤ U b := le_trans (henv rival hrival) (hU hb)
  rw [heq] at hupper
  exact (not_lt_of_ge hupper) hcross

-- A zero-limit condition without relying on an exact computable-real equality
-- test. A certified interval/dovetailed search can expose one strict crossing.
def ArbitrarilySmall (U : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ b : ℕ, U b < ε

theorem positive_target_has_crossing
    (U : ℕ → ℝ) (hU : Antitone U) (hsmall : ArbitrarilySmall U)
    (target : PositiveChain) :
    ∃ b : ℕ, 0 < b ∧ U b < sourceSurvival target := by
  obtain ⟨b, hb⟩ := hsmall (sourceSurvival target) (sourceSurvival_positive target)
  refine ⟨b + 1, Nat.succ_pos b, ?_⟩
  exact lt_of_le_of_lt (hU (Nat.le_succ b)) hb

theorem observable_finite_length_certificate
    (C : PositiveChain → Prop) (U : ℕ → ℝ)
    (hU : Antitone U) (henv : RivalEnvelope C U)
    (hsmall : ArbitrarilySmall U) (target : PositiveChain)
    (before after : PositiveEdge) :
    ∃ b : ℕ, 0 < b ∧ ∀ rival : PositiveChain,
      C rival →
      rootedACladeResponse before after (sourceSurvival rival) =
        rootedACladeResponse before after (sourceSurvival target) →
      rival.cells.length < b := by
  obtain ⟨b, hpositive, hcross⟩ := positive_target_has_crossing U hU hsmall target
  exact ⟨b, hpositive, fun rival hrival hobs =>
    certified_crossing_length_bound C U hU henv target rival before after hrival hobs b hcross⟩

end G4TwoRootSourceStopping





end FullContextModule35

section FullContextModule36





/-!
# Shared-register context test for G1 marginal forest-kernel replacement

New proof contribution: dot's dedicated Lean lane, 2026-10-01.
Two live labelled input lineages have one exponential pair-merger clock.
Their unranked output forest has two states: two survivors or one merger.
The exponential waiting-time law is Mathlib's probability measure, rather than
an unproved axiom for the desired survival probability.

Context contract: the same fair parent register selects the common-bigon
population AND is retained by an exterior that can read/reuse it. This is an
exposed-register experiment, not ordinary passive gene-tree/DNA observation.
The test does not refute marginal replacement with genuinely private,
independent component coins. The accepted conditional-register contract already
retains the register, so no new failure of that accepted theorem is claimed.

No general source graph-to-kernel, grafting, root-blob preservation, source
realizability, or full G1 theorem is established by this component.
-/

namespace GProgram.G1

open ProbabilityTheory

/-- The survival event for the one pair-merger exponential holding time. -/
noncomputable def pairSurvival (rate duration : ℝ) : ℝ :=
  1 - cdf (expMeasure rate) duration

theorem pairSurvival_eq_exp {rate duration : ℝ}
    (hr : 0 < rate) (ht : 0 ≤ duration) :
    pairSurvival rate duration = Real.exp (-(rate * duration)) := by
  rw [pairSurvival, cdf_expMeasure_eq hr]
  simp only [if_pos ht]
  ring

theorem positive_bigon_pair_rates : 0 < Real.log 2 ∧ 0 < Real.log 4 := by
  exact ⟨Real.log_pos (by norm_num), Real.log_pos (by norm_num)⟩

theorem pairSurvival_log_two : pairSurvival (Real.log 2) 1 = 1 / 2 := by
  rw [pairSurvival_eq_exp positive_bigon_pair_rates.1 (by norm_num)]
  simp only [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem pairSurvival_log_four : pairSurvival (Real.log 4) 1 = 1 / 4 := by
  rw [pairSurvival_eq_exp positive_bigon_pair_rates.2 (by norm_num)]
  simp only [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-- `true` means the two original labelled forest tokens remain separate;
`false` means their one possible merger has happened. -/
noncomputable def pairForestKernel (rate duration : ℝ) (separate : Bool) : ℝ :=
  if separate then pairSurvival rate duration else 1 - pairSurvival rate duration

theorem pairForestKernel_normalized (rate duration : ℝ) :
    pairForestKernel rate duration true + pairForestKernel rate duration false = 1 := by
  simp only [pairForestKernel, Bool.false_eq_true, if_true, if_false]
  ring

theorem pairForestKernel_nonnegative {rate duration : ℝ}
    (hr : 0 < rate) (ht : 0 ≤ duration) (separate : Bool) :
    0 ≤ pairForestKernel rate duration separate := by
  cases separate
  · simp only [pairForestKernel, Bool.false_eq_true, if_false]
    rw [pairSurvival_eq_exp hr ht]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  · simp only [pairForestKernel, if_true]
    rw [pairSurvival_eq_exp hr ht]
    exact (Real.exp_pos _).le

/-- `p` is the probability that the retained original parent register is 0. -/
def registerWeight (p : ℝ) (register : Bool) : ℝ := if register then 1 - p else p

noncomputable def commonBigonConditional (rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  pairForestKernel (if register then rate1 else rate0) 1 separate

noncomputable def retainedRegisterJoint (p rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  registerWeight p register * commonBigonConditional rate0 rate1 register separate

/-- The unconditional component forest kernel, with the register marginalized. -/
noncomputable def marginalForestKernel (p rate0 rate1 : ℝ) (separate : Bool) : ℝ :=
  retainedRegisterJoint p rate0 rate1 false separate +
    retainedRegisterJoint p rate0 rate1 true separate

/-- The invalid candidate replacement draws from the marginal forest kernel
independently of the exterior's retained original register. -/
noncomputable def freshMarginalJoint (p rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  registerWeight p register * marginalForestKernel p rate0 rate1 separate

theorem retained_register_joint_normalized (p rate0 rate1 : ℝ) :
    retainedRegisterJoint p rate0 rate1 false true +
    retainedRegisterJoint p rate0 rate1 false false +
    retainedRegisterJoint p rate0 rate1 true true +
    retainedRegisterJoint p rate0 rate1 true false = 1 := by
  simp [retainedRegisterJoint, registerWeight, commonBigonConditional, pairForestKernel]
  ring

theorem retained_register_joint_nonnegative {p rate0 rate1 : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (h0 : 0 < rate0) (h1 : 0 < rate1)
    (register separate : Bool) :
    0 ≤ retainedRegisterJoint p rate0 rate1 register separate := by
  unfold retainedRegisterJoint commonBigonConditional
  apply mul_nonneg
  · cases register <;> simp only [registerWeight, Bool.false_eq_true, if_true, if_false]
    · exact hp
    · linarith
  · apply pairForestKernel_nonnegative _ (by norm_num)
    cases register <;> simp_all

theorem shared_register_exact_counterexample :
    marginalForestKernel (1 / 2) (Real.log 2) (Real.log 4) true = 3 / 8 ∧
    retainedRegisterJoint (1 / 2) (Real.log 2) (Real.log 4) false true = 1 / 4 ∧
    freshMarginalJoint (1 / 2) (Real.log 2) (Real.log 4) false true = 3 / 16 := by
  norm_num [marginalForestKernel, retainedRegisterJoint, freshMarginalJoint,
    registerWeight, commonBigonConditional, pairForestKernel,
    pairSurvival_log_two, pairSurvival_log_four]

theorem resampling_changes_exposed_context :
    retainedRegisterJoint (1 / 2) (Real.log 2) (Real.log 4) ≠
      freshMarginalJoint (1 / 2) (Real.log 2) (Real.log 4) := by
  intro heq
  have h := congrFun (congrFun heq false) true
  rw [shared_register_exact_counterexample.2.1,
    shared_register_exact_counterexample.2.2] at h
  norm_num at h

theorem register_survival_difference (p x0 x1 : ℝ) :
    p * x0 - p * (p * x0 + (1 - p) * x1) = p * (1 - p) * (x0 - x1) := by
  ring

/-- For an interior binary shared register, matching the exposed-register
survival event by marginal resampling is possible exactly when the two
conditional survival probabilities are equal. -/
theorem exposed_event_preserved_iff_equal_conditionals {p x0 x1 : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    p * x0 = p * (p * x0 + (1 - p) * x1) ↔ x0 = x1 := by
  constructor
  · intro heq
    have hzero : p * (1 - p) * (x0 - x1) = 0 := by
      rw [← register_survival_difference p x0 x1]
      exact sub_eq_zero.mpr heq
    have hpos : 0 < p * (1 - p) := mul_pos hp (by linarith)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos))
  · intro heq
    subst x1
    ring










end GProgram.G1

end FullContextModule36

section FullContextModule37





/-!
# Arbitrary-interior-weight four-root forest defect certificate

Formal algebra contribution of the dedicated Lean lane. Source equations:
FOUR-ROOT-PLACEMENT.md, Commons 3d755ef391066069d33ff4490da65f00742b7ea7.
Original G4 derivation and ownership retained.

This certifies the explicit source-polynomial defect for one independent bigon.
Generator/forest interpretation, private-randomness composition/tomography and
full common-chain comparison are separate source bridges, not assumed axioms.
-/

namespace GProgram.G4.FourRoot

noncomputable def s2 (u x y : ℝ) : ℝ := u^2*x + (1-u)^2*y + 2*u*(1-u)
noncomputable def s3 (u x y : ℝ) : ℝ :=
  u^3*x^3 + (1-u)^3*y^3 + 3*u^2*(1-u)*x + 3*u*(1-u)^2*y
noncomputable def s4 (u x y : ℝ) : ℝ :=
  u^4*x^6 + (1-u)^4*y^6 + 4*u^3*(1-u)*x^3 +
    4*u*(1-u)^3*y^3 + 6*u^2*(1-u)^2*x*y
noncomputable def ordinaryOne4 (z : ℝ) : ℝ := 1 - 9*z/5 + z^3 - z^6/5
noncomputable def one4 (u x y : ℝ) : ℝ :=
  u^4*ordinaryOne4 x + (1-u)^4*ordinaryOne4 y
noncomputable def delta (u x y : ℝ) : ℝ :=
  one4 u x y - (1 - 9*(s2 u x y)/5 + s3 u x y - s4 u x y/5)
noncomputable def defect3 (u x y : ℝ) : ℝ := s3 u x y - (s2 u x y)^3
noncomputable def A (u x : ℝ) : ℝ := u*(1-x)
noncomputable def B (u y : ℝ) : ℝ := (1-u)*(1-y)

theorem exact_defect_factorization (u x y : ℝ) :
    defect3 u x y + 5*delta u x y =
      -u*(1-u)*(A u x-B u y)^2*((1+u)*A u x+(2-u)*B u y) := by
  unfold defect3 delta one4 ordinaryOne4 s2 s3 s4 A B
  ring

theorem defect3_in_barrier_coordinates (u x y : ℝ) :
    defect3 u x y = 3*u*(1-u)*(A u x-B u y)^2 -
      ((A u x)^3+(B u y)^3-(u*A u x+(1-u)*B u y)^3) := by
  unfold defect3 s2 s3 A B
  ring

/-- The exact zero-four-root-defect stratum has a strictly negative cubic
moment defect for every positive independent bigon, without genericity. -/
theorem zero_delta_forces_negative_defect3 {u x y : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hx1 : x < 1) (hy1 : y < 1)
    (hd : delta u x y = 0) : defect3 u x y < 0 := by
  have hv : 0 < 1-u := by linarith
  have ha : 0 < A u x := mul_pos hu (by linarith)
  have hb : 0 < B u y := mul_pos hv (by linarith)
  have hq : 0 < (1+u)*A u x+(2-u)*B u y :=
    add_pos (mul_pos (by linarith) ha) (mul_pos (by linarith) hb)
  by_cases he : A u x = B u y
  · have hmean : u*B u y+(1-u)*B u y = B u y := by ring
    have hh := defect3_in_barrier_coordinates u x y
    rw [he,hmean] at hh
    have hp := pow_pos hb 3
    nlinarith
  · have hsq : 0 < (A u x-B u y)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr he)
    have hp : 0 < u*(1-u)*(A u x-B u y)^2*((1+u)*A u x+(2-u)*B u y) :=
      mul_pos (mul_pos (mul_pos hu hv) hsq) hq
    have hh := exact_defect_factorization u x y
    rw [hd] at hh
    nlinarith

theorem no_common_moment_signature {u x y : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hx1 : x < 1) (hy1 : y < 1) :
    ¬ (delta u x y = 0 ∧ 0 ≤ defect3 u x y) := by
  rintro ⟨hd,hnonneg⟩
  exact not_lt_of_ge hnonneg (zero_delta_forces_negative_defect3 hu hu1 hx1 hy1 hd)

/-- Exact rational cap-three scalar witness used by the source's exchangeable
full-forest sharpness argument. That exchangeability bridge is not proved here. -/
theorem rational_cap3_scalar_witness :
    s2 (1/2) (37/42) (5/6) = 13/14 ∧
    s3 (1/2) (37/42) (5/6) = (13/14)^3 := by
  norm_num [s2,s3]






end GProgram.G4.FourRoot

end FullContextModule37

section FullContextModule38












/-!
# Source-mode independent live-token routing to no-merger coordinates

Dedicated Sol6.1 Lean contribution. Fixed original hybrid parent IDs and one
coin per LIVE input forest root are retained. The explicit finite sum below
uses independent product routing weights; each live root goes to exactly one
parent. Earlier coalesced copy labels remain attached through LiveAncestry.
Generic arm no-merger kernels are supplied separately. Their continuous-time
Kingman/source interpretation is not assumed as the desired bigon polynomial.
-/

namespace GProgram.G4.IndependentRouting

open scoped BigOperators

noncomputable def bitWeight (u : ℝ) (bit : Bool) : ℝ := if bit then 1-u else u

noncomputable def routingWeight {n : Nat} (u : ℝ) (coin : Fin n → Bool) : ℝ :=
  ∏ i, bitWeight u (coin i)

def count0 {n : Nat} (coin : Fin n → Bool) : Nat := ∑ i, if coin i then 0 else 1
def count1 {n : Nat} (coin : Fin n → Bool) : Nat := ∑ i, if coin i then 1 else 0

/-- Private independent parent populations: each arm receives its routed live
root count, preserving the same fixed kernel at all input sizes. -/
noncomputable def privateNoMerger (n : Nat) (u : ℝ) (arm0 arm1 : Nat → ℝ) : ℝ :=
  ∑ coin : Fin n → Bool,
    routingWeight u coin * arm0 (count0 coin) * arm1 (count1 coin)

theorem sum_vectors_succ {n : Nat} (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ coin, f coin) = ∑ b : Bool, ∑ coin : Fin n → Bool, f (Fin.cons b coin) := by
  classical
  calc
    (∑ coin, f coin) = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
      ((Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

theorem sum_vectors_zero (f : (Fin 0 → Bool) → ℝ) :
    (∑ coin, f coin) = f default := by
  rw [Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

theorem count0_cons {n : Nat} (b : Bool) (coin : Fin n → Bool) :
    count0 (Fin.cons b coin) = (if b then 0 else 1) + count0 coin := by
  simp only [count0,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem count1_cons {n : Nat} (b : Bool) (coin : Fin n → Bool) :
    count1 (Fin.cons b coin) = (if b then 1 else 0) + count1 coin := by
  simp only [count1,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem count_partition {n : Nat} (coin : Fin n → Bool) :
    count0 coin + count1 coin = n := by
  unfold count0 count1
  rw [← Finset.sum_add_distrib]
  have ht : ∀ i : Fin n, (if coin i then 0 else 1) + (if coin i then 1 else 0) = 1 := by
    intro i
    cases coin i <;> rfl
  simp [ht]

theorem routingWeight_cons {n : Nat} (u : ℝ) (b : Bool) (coin : Fin n → Bool) :
    routingWeight u (Fin.cons b coin) = bitWeight u b * routingWeight u coin := by
  simp [routingWeight,Fin.prod_univ_succ]

theorem routingWeight_normalized (n : Nat) (u : ℝ) :
    (∑ coin : Fin n → Bool, routingWeight u coin) = 1 := by
  induction n with
  | zero => simp [routingWeight]
  | succ n ih =>
    rw [sum_vectors_succ]
    simp [routingWeight_cons,← Finset.mul_sum,ih,Fintype.sum_bool,bitWeight]

theorem routingWeight_nonnegative {n : Nat} {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (coin : Fin n → Bool) : 0 ≤ routingWeight u coin := by
  unfold routingWeight
  apply Finset.prod_nonneg
  intro i _
  cases coin i <;> simp [bitWeight] <;> linarith

theorem generic_two (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger 2 u a b =
      u^2*a 2*b 0+2*u*(1-u)*a 1*b 1+(1-u)^2*a 0*b 2 := by
  simp only [privateNoMerger,sum_vectors_succ,sum_vectors_zero,Fintype.sum_bool,
    routingWeight_cons,count0_cons,count1_cons]
  norm_num [bitWeight,routingWeight,count0,count1,Fin.prod_univ_zero,Fin.sum_univ_zero]
  ring

theorem generic_three (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger 3 u a b =
      u^3*a 3*b 0+3*u^2*(1-u)*a 2*b 1+
      3*u*(1-u)^2*a 1*b 2+(1-u)^3*a 0*b 3 := by
  simp only [privateNoMerger,sum_vectors_succ,sum_vectors_zero,Fintype.sum_bool,
    routingWeight_cons,count0_cons,count1_cons]
  norm_num [bitWeight,routingWeight,count0,count1,Fin.prod_univ_zero,Fin.sum_univ_zero]
  ring

theorem generic_four (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger 4 u a b =
      u^4*a 4*b 0+4*u^3*(1-u)*a 3*b 1+6*u^2*(1-u)^2*a 2*b 2+
      4*u*(1-u)^3*a 1*b 3+(1-u)^4*a 0*b 4 := by
  simp only [privateNoMerger,sum_vectors_succ,sum_vectors_zero,Fintype.sum_bool,
    routingWeight_cons,count0_cons,count1_cons]
  norm_num [bitWeight,routingWeight,count0,count1,Fin.prod_univ_zero,Fin.sum_univ_zero]
  ring

/-- Finite arm-power contract, independent of the desired bigon formula. -/
def FourRootArmLaw (arm : Nat → ℝ) (x : ℝ) : Prop :=
  arm 0 = 1 ∧ arm 1 = 1 ∧ arm 2 = x ∧ arm 3 = x^3 ∧ arm 4 = x^6

/-- The explicit exponential first-holding-clock model, with one unit-rate
unordered-pair merger hazard per live pair. Equality with the full biological
source's first-merge event remains a separate source-generator obligation. -/
noncomputable def firstHoldingKernel (k : Nat) (duration : ℝ) : ℝ :=
  if k ≤ 1 then 1 else GProgram.G1.pairSurvival (k.choose 2 : ℝ) duration

theorem firstHoldingKernel_eq_power {duration : ℝ} (ht : 0 ≤ duration) (k : Nat) :
    firstHoldingKernel k duration = (Real.exp (-duration))^(k.choose 2) := by
  by_cases hk : k ≤ 1
  · have hc : k.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [firstHoldingKernel,hk,hc]
  · have hc : 0 < (k.choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (show 2 ≤ k by omega)
    rw [firstHoldingKernel,if_neg hk,GProgram.G1.pairSurvival_eq_exp hc ht,
      ← Real.exp_nat_mul]
    congr 1
    ring

theorem exponential_four_root_arm_law {duration : ℝ} (ht : 0 ≤ duration) :
    FourRootArmLaw (fun k => firstHoldingKernel k duration) (Real.exp (-duration)) := by
  norm_num [FourRootArmLaw,firstHoldingKernel_eq_power ht,Nat.choose]

section OriginalSource

open Nanuq.Source

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable {N : RootedBinary V E X}

theorem actual_parent0_count {n : Nat} (H : GProgram.G2.OriginalHybridParents N)
    (coin : Fin n → Bool) :
    (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card = count0 coin := by
  classical
  have hcard : (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card =
      ∑ i, if H.parent (coin i) = H.parent0 then (1 : Nat) else 0 := by
    simpa using (Finset.sum_boole (R := Nat)
      (fun i : Fin n => H.parent (coin i) = H.parent0) Finset.univ).symm
  rw [hcard]
  unfold count0
  apply Finset.sum_congr rfl
  intro i _
  cases hc : coin i <;> simp [GProgram.G2.OriginalHybridParents.parent,hc,
    H.different,H.different.symm]

theorem actual_parent1_count {n : Nat} (H : GProgram.G2.OriginalHybridParents N)
    (coin : Fin n → Bool) :
    (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card = count1 coin := by
  classical
  have hcard : (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card =
      ∑ i, if H.parent (coin i) = H.parent1 then (1 : Nat) else 0 := by
    simpa using (Finset.sum_boole (R := Nat)
      (fun i : Fin n => H.parent (coin i) = H.parent1) Finset.univ).symm
  rw [hcard]
  unfold count1
  apply Finset.sum_congr rfl
  intro i _
  cases hc : coin i <;> simp [GProgram.G2.OriginalHybridParents.parent,hc,
    H.different,H.different.symm]

/-- Same original hybrid and parent IDs, same u, same two arm kernels for every
input size. Product arm kernel explicitly specifies private independent arms. -/
noncomputable def actualPrivateNoMerger (H : GProgram.G2.OriginalHybridParents N)
    (n : Nat) (u : ℝ) (a b : Nat → ℝ) : ℝ := by
  classical
  exact ∑ coin : Fin n → Bool, routingWeight u coin *
    a ((Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card) *
    b ((Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card)

theorem actualPrivateNoMerger_eq (H : GProgram.G2.OriginalHybridParents N)
    (n : Nat) (u : ℝ) (a b : Nat → ℝ) :
    actualPrivateNoMerger H n u a b = privateNoMerger n u a b := by
  classical
  unfold actualPrivateNoMerger privateNoMerger
  apply Finset.sum_congr rfl
  intro coin _
  rw [actual_parent0_count,actual_parent1_count]

/-- The desired three bigon polynomials are CONCLUSIONS of independent live-root
routing enumeration. Arm power laws and private arm independence stay explicit. -/
theorem original_source_coordinates (H : GProgram.G2.OriginalHybridParents N)
    (u x y : ℝ) (a b : Nat → ℝ) (ha : FourRootArmLaw a x) (hb : FourRootArmLaw b y) :
    actualPrivateNoMerger H 2 u a b = GProgram.G4.FourRoot.s2 u x y ∧
    actualPrivateNoMerger H 3 u a b = GProgram.G4.FourRoot.s3 u x y ∧
    actualPrivateNoMerger H 4 u a b = GProgram.G4.FourRoot.s4 u x y := by
  rcases ha with ⟨ha0,ha1,ha2,ha3,ha4⟩
  rcases hb with ⟨hb0,hb1,hb2,hb3,hb4⟩
  simp only [actualPrivateNoMerger_eq,generic_two,generic_three,generic_four,
    ha0,ha1,ha2,ha3,ha4,hb0,hb1,hb2,hb3,hb4,
    GProgram.G4.FourRoot.s2,GProgram.G4.FourRoot.s3,GProgram.G4.FourRoot.s4]
  constructor
  · ring
  constructor <;> ring

/-- Fully explicit exponential first-holding MODEL. The remaining source step
is identifying actual Kingman arm first-merge laws with this modeled clock. -/
theorem exponential_model_original_coordinates (H : GProgram.G2.OriginalHybridParents N)
    (u t0 t1 : ℝ) (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) :
    let a := fun k => firstHoldingKernel k t0
    let b := fun k => firstHoldingKernel k t1
    actualPrivateNoMerger H 2 u a b = GProgram.G4.FourRoot.s2 u (Real.exp (-t0)) (Real.exp (-t1)) ∧
    actualPrivateNoMerger H 3 u a b = GProgram.G4.FourRoot.s3 u (Real.exp (-t0)) (Real.exp (-t1)) ∧
    actualPrivateNoMerger H 4 u a b = GProgram.G4.FourRoot.s4 u (Real.exp (-t0)) (Real.exp (-t1)) := by
  exact original_source_coordinates H u _ _ _ _
    (exponential_four_root_arm_law ht0) (exponential_four_root_arm_law ht1)

end OriginalSource










end GProgram.G4.IndependentRouting

end FullContextModule38

section FullContextModule39





/-!
# All-finite-root first-merger clock bridge

Dedicated Sol6.1 source-model contribution. One independent unit-rate
exponential clock is drawn for every unordered pair of current LIVE roots.
No first merger during an arm means every pair clock exceeds its duration.
This product-measure event is proved to have the choose(n,2) survival law.
Later merger/reset dynamics and graph-to-full-process interpretation remain
separate; this theorem does not assert a recognition cutoff.
-/

namespace GProgram.G4.PairClocks

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

abbrev LivePair (n : Nat) := { s : Finset (Fin n) // s.card = 2 }

theorem livePair_card (n : Nat) : Fintype.card (LivePair n) = n.choose 2 := by
  simp [LivePair,Fintype.card_finset_len]

local instance unitClock_probability : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def pairClockMeasure (n : Nat) : Measure (LivePair n → ℝ) :=
  Measure.pi (fun _ : LivePair n => expMeasure (1 : ℝ))

def noFirstMergeEvent (n : Nat) (duration : ℝ) : Set (LivePair n → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioi duration)

theorem noFirstMergeEvent_iff {n : Nat} {duration : ℝ} (clock : LivePair n → ℝ) :
    clock ∈ noFirstMergeEvent n duration ↔ ∀ pair, duration < clock pair := by
  simp [noFirstMergeEvent,Set.mem_pi]

theorem unitClock_tail_real {duration : ℝ} (ht : 0 ≤ duration) :
    (expMeasure (1 : ℝ)).real (Set.Ioi duration) = Real.exp (-duration) := by
  rw [← Set.compl_Iic,probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real,cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1),if_pos ht]
  simp

theorem all_root_no_first_merge {duration : ℝ} (n : Nat) (ht : 0 ≤ duration) :
    (pairClockMeasure n (noFirstMergeEvent n duration)).toReal =
      (Real.exp (-duration))^(n.choose 2) := by
  rw [pairClockMeasure,noFirstMergeEvent,Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ _ : LivePair n, (expMeasure (1 : ℝ)).real (Set.Ioi duration)) = _
  simp only [unitClock_tail_real ht,Finset.prod_const,Finset.card_univ,livePair_card]

theorem product_clock_eq_holding_model {duration : ℝ} (n : Nat) (ht : 0 ≤ duration) :
    (pairClockMeasure n (noFirstMergeEvent n duration)).toReal =
      GProgram.G4.IndependentRouting.firstHoldingKernel n duration := by
  rw [all_root_no_first_merge n ht,
    GProgram.G4.IndependentRouting.firstHoldingKernel_eq_power ht]

/-- Private independent arms use an actual product measure, not an assumed
product-of-probabilities conclusion. This remains a first-merger primitive. -/
theorem private_arms_no_first_merge {t0 t1 : ℝ} (k0 k1 : Nat)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) :
    (((pairClockMeasure k0).prod (pairClockMeasure k1))
      (noFirstMergeEvent k0 t0 ×ˢ noFirstMergeEvent k1 t1)).toReal =
      GProgram.G4.IndependentRouting.firstHoldingKernel k0 t0 *
      GProgram.G4.IndependentRouting.firstHoldingKernel k1 t1 := by
  letI : IsProbabilityMeasure (pairClockMeasure k0) := by
    unfold pairClockMeasure
    infer_instance
  letI : IsProbabilityMeasure (pairClockMeasure k1) := by
    unfold pairClockMeasure
    infer_instance
  have hh := Measure.prod_prod (μ := pairClockMeasure k0) (ν := pairClockMeasure k1)
    (noFirstMergeEvent k0 t0) (noFirstMergeEvent k1 t1)
  rw [hh,ENNReal.toReal_mul,
    product_clock_eq_holding_model k0 ht0,product_clock_eq_holding_model k1 ht1]






end GProgram.G4.PairClocks

end FullContextModule39

section FullContextModule40
/- Explicit hosted4.35 API variant only: the two real nonnegative product
lemmas now have the zero-aware names ending in subscript zero. No theorem
statement or source-observation premise is changed. Pinned source unchanged. -/






/-!
# NEW path-resolved private-source observation extension

Original positive current-root cell/edge carriers and pair survival recursion
are reused. The additional observable is the COMPLETE consistently labelled
original-parent itinerary on the NO-MERGER event. Its labels are measured,
not reconstructed from passive forests. Failure records no later split coins.
This finite first-merger/absorbing pair fragment does not silently assert the
still-open full graph-to-continuous-source refinement or original passive G4.
-/
namespace GProgram.G4.PathResolved
open G4TwoRootSourceStopping
open scoped BigOperators
variable {Site : Type*} [Fintype Site] [DecidableEq Site]

abbrev Color (Site : Type*) := Site → Bool

noncomputable def itineraryMass (cells : Site → Cell) (c : Color Site) : ℝ :=
  ∏ i, coinWeight (cells i).bigon.g (c i)

noncomputable def localPairMass (C : Cell) (a b : Bool) : ℝ :=
  coinWeight C.bigon.g a * coinWeight C.bigon.g b *
    (C.connector.survival * pairRouteSurvival C.bigon.x C.bigon.y a b)

/-- The original live-pair branch likelihood. Later coins are unobserved on
failure; the all-surviving path multiplies its actual cell branch factors. -/
noncomputable def observedPair (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ := leading.survival * ∏ i, localPairMass (cells i) (c i) (d i)

noncomputable def hiddenKernel (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ := leading.survival * ∏ i,
      (cells i).connector.survival *
        pairRouteSurvival (cells i).bigon.x (cells i).bigon.y (c i) (d i)

noncomputable def measuredKernel (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ :=
  observedPair leading cells c d / (itineraryMass cells c * itineraryMass cells d)

lemma coinWeight_pos (B : PositiveBigon) (a : Bool) : 0 < coinWeight B.g a := by
  cases a <;> simp [coinWeight]
  · exact B.g_below_one
  · exact B.g_positive

lemma pairRouteSurvival_pos (B : PositiveBigon) (a b : Bool) :
    0 < pairRouteSurvival B.x B.y a b := by
  cases a <;> cases b <;> simp [pairRouteSurvival,B.x_positive,B.y_positive]

lemma itineraryMass_pos (cells : Site → Cell) (c : Color Site) :
    0 < itineraryMass cells c := by
  apply Finset.prod_pos
  intro i _
  exact coinWeight_pos (cells i).bigon (c i)

lemma itineraryMass_normalized (cells : Site → Cell) :
    (∑ c : Color Site, itineraryMass cells c) = 1 := by
  unfold itineraryMass
  rw [← Fintype.prod_sum]
  have h : ∀ i : Site, (∑ b : Bool, coinWeight (cells i).bigon.g b) = 1 := by
    intro i
    simp [coinWeight]
  simp only [h, Finset.prod_const_one]

/-- Every source itinerary has strictly positive mass, and the joint measured
no-merger likelihood is derived from cell branch factors rather than fitted. -/
theorem original_source_joint_itinerary_likelihood (leading : PositiveEdge)
    (cells : Site → Cell) (c d : Color Site) :
    observedPair leading cells c d =
      itineraryMass cells c * itineraryMass cells d * hiddenKernel leading cells c d := by
  unfold observedPair itineraryMass hiddenKernel localPairMass
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  ring

lemma localPairMass_sum (C : Cell) :
    (∑ a : Bool, ∑ b : Bool, localPairMass C a b) = cellSurvival C := by
  simp [localPairMass,cellSurvival,bareSurvival,coinWeight,pairRouteSurvival]
  ring

/-- This total agrees with the inherited absorbing original live-pair scalar
recursion. No two fresh coins are attached to a merged ancestral subtree. -/
theorem complete_joint_no_merger_mass (leading : PositiveEdge) (cells : Site → Cell) :
    (∑ c : Color Site, ∑ d : Color Site, observedPair leading cells c d) =
      leading.survival * ∏ i, cellSurvival (cells i) := by
  simp only [observedPair, ← Finset.mul_sum]
  congr 1
  simp_rw [← Fintype.prod_sum]
  rw [← Fintype.prod_sum (fun (i : Site) (a : Bool) =>
    ∑ b : Bool, localPairMass (cells i) a b)]
  simp only [localPairMass_sum]

/-- Source-faithful exact density reconstruction in the CHANGED menu. -/
theorem reconstructed_kernel_eq_original (leading : PositiveEdge)
    (cells : Site → Cell) (c d : Color Site) :
    measuredKernel leading cells c d = hiddenKernel leading cells c d := by
  rw [measuredKernel,original_source_joint_itinerary_likelihood]
  exact mul_div_cancel_left₀ _
    (ne_of_gt (mul_pos (itineraryMass_pos cells c) (itineraryMass_pos cells d)))

noncomputable def totalNoMerger (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  leading.survival * ∏ i, cellSurvival (cells i)

lemma totalNoMerger_pos (leading : PositiveEdge) (cells : Site → Cell) :
    0 < totalNoMerger leading cells :=
  mul_pos leading.positive (Finset.prod_pos (fun i _ => cellSurvival_positive (cells i)))

lemma totalNoMerger_lt_one (leading : PositiveEdge) (cells : Site → Cell) :
    totalNoMerger leading cells < 1 := by
  have hprod : (∏ i, cellSurvival (cells i)) ≤ (1 : ℝ) :=
    Finset.prod_le_one₀ (fun i _ => (cellSurvival_positive (cells i)).le)
      (fun i _ => (cellSurvival_below_one (cells i)).le)
  have hp : 0 < (∏ i : Site, cellSurvival (cells i)) :=
    Finset.prod_pos (fun i _ => cellSurvival_positive (cells i))
  have hl := leading.positive
  have hl1 := leading.below_one
  unfold totalNoMerger
  nlinarith

noncomputable def outcomeMass (leading : PositiveEdge) (cells : Site → Cell) :
    Option (Color Site × Color Site) → ℝ
  | none => 1 - totalNoMerger leading cells
  | some pair => observedPair leading cells pair.1 pair.2

lemma outcomeMass_nonneg (leading : PositiveEdge) (cells : Site → Cell)
    (outcome : Option (Color Site × Color Site)) : 0 ≤ outcomeMass leading cells outcome := by
  cases outcome with
  | none => exact (sub_pos.mpr (totalNoMerger_lt_one leading cells)).le
  | some pair =>
    unfold outcomeMass observedPair
    apply mul_nonneg leading.positive.le
    apply Finset.prod_nonneg
    intro i _
    unfold localPairMass
    exact (mul_pos (mul_pos (coinWeight_pos (cells i).bigon _) (coinWeight_pos (cells i).bigon _))
      (mul_pos (cells i).connector.positive (pairRouteSurvival_pos (cells i).bigon _ _))).le

lemma outcomeMass_normalized (leading : PositiveEdge) (cells : Site → Cell) :
    (∑ o : Option (Color Site × Color Site), outcomeMass leading cells o) = 1 := by
  rw [Fintype.sum_option]
  simp only [outcomeMass, Fintype.sum_prod_type]
  rw [complete_joint_no_merger_mass]
  unfold totalNoMerger
  ring

/-- Genuine normalized terminated pair PMF: failure is absorbing and carries
no later itinerary bits. The complete success record is retained jointly. -/
noncomputable def sourcePairPMF (leading : PositiveEdge) (cells : Site → Cell) :
    PMF (Option (Color Site × Color Site)) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (outcomeMass leading cells o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => outcomeMass_nonneg leading cells o),
      outcomeMass_normalized]
    norm_num)

theorem sourcePairPMF_joint_record (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) :
    sourcePairPMF leading cells (some (c,d)) =
      ENNReal.ofReal (itineraryMass cells c * itineraryMass cells d *
        hiddenKernel leading cells c d) := by
  simp only [sourcePairPMF,PMF.ofFintype_apply,outcomeMass]
  rw [original_source_joint_itinerary_likelihood]

/-- Every finite root count uses the existing actual product of independent
unit pair clocks. Positive source survival encodes its finite hazard duration;
this does not equate physical time and hazard time or supply a calendar. -/
theorem all_input_edge_clock_survival (edge : PositiveEdge) (n : Nat) :
    ((GProgram.G4.PairClocks.pairClockMeasure n)
      (GProgram.G4.PairClocks.noFirstMergeEvent n (-Real.log edge.survival))).toReal =
        edge.survival ^ (n.choose 2) := by
  rw [GProgram.G4.PairClocks.all_root_no_first_merge n
    (le_of_lt (neg_pos.mpr (Real.log_neg edge.positive edge.below_one))),
    neg_neg,Real.exp_log edge.positive]

/-- The complete measured no-merger law has the original absorbing live-pair
scalar recursion for a source word of ANY finite length. -/
theorem observed_mass_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) :
    (∑ c : Color (Fin (n+1)), ∑ d : Color (Fin (n+1)),
      observedPair leading (Fin.cons C rest) c d) =
      serialUnmerged (cellSurvival C)
        (∑ c : Color (Fin n), ∑ d : Color (Fin n), observedPair leading rest c d) := by
  rw [complete_joint_no_merger_mass,complete_joint_no_merger_mass]
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,serialUnmerged]
  ring

section OriginalLabels
open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable {N : RootedBinary V E X}

noncomputable def observedOriginalParents (H : Site → GProgram.G2.OriginalHybridParents N)
    (c : Color Site) : Site → E := fun i => (H i).parent (c i)

/-- Added route labels refer to the SAME original parent edges. Their genuine
observation distinguishes full bits without inventing compressed actuators. -/
theorem complete_original_parent_readout_injective
    (H : Site → GProgram.G2.OriginalHybridParents N) :
    Function.Injective (observedOriginalParents H) := by
  intro c d he
  funext i
  exact (H i).parent_injective (congrFun he i)
/-- ALL input counts, using actual ORIGINAL parent IDs and independent
finite first-merger clocks on the two original private arms. Here parent1
has x-survival and parent0 has y-survival, matching the reused true-bit table. -/
theorem original_all_input_arm_clock_likelihood
    (H : GProgram.G2.OriginalHybridParents N) (B : PositiveBigon)
    (n : Nat) (coin : Fin n → Bool) :
    let k1 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card
    let k0 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card
    (((GProgram.G4.PairClocks.pairClockMeasure k1).prod
        (GProgram.G4.PairClocks.pairClockMeasure k0))
      (GProgram.G4.PairClocks.noFirstMergeEvent k1 (-Real.log B.x) ×ˢ
       GProgram.G4.PairClocks.noFirstMergeEvent k0 (-Real.log B.y))).toReal =
      B.x ^ ((GProgram.G4.IndependentRouting.count1 coin).choose 2) *
      B.y ^ ((GProgram.G4.IndependentRouting.count0 coin).choose 2) := by
  dsimp only
  rw [GProgram.G4.IndependentRouting.actual_parent1_count H coin,
    GProgram.G4.IndependentRouting.actual_parent0_count H coin]
  rw [GProgram.G4.PairClocks.private_arms_no_first_merge _ _
      (le_of_lt (neg_pos.mpr (Real.log_neg B.x_positive B.x_below_one)))
      (le_of_lt (neg_pos.mpr (Real.log_neg B.y_positive B.y_below_one))),
    GProgram.G4.IndependentRouting.firstHoldingKernel_eq_power
      (le_of_lt (neg_pos.mpr (Real.log_neg B.x_positive B.x_below_one))),
    GProgram.G4.IndependentRouting.firstHoldingKernel_eq_power
      (le_of_lt (neg_pos.mpr (Real.log_neg B.y_positive B.y_below_one))),
    neg_neg,neg_neg,Real.exp_log B.x_positive,Real.exp_log B.y_positive]

/-- The recorded two-live-root branch survival is the special case of the
source's genuine all-input current-parent clock likelihood, not a fitted W. -/
theorem original_two_live_root_clock_branch
    (H : GProgram.G2.OriginalHybridParents N) (B : PositiveBigon) (a b : Bool) :
    let coin : Fin 2 → Bool := ![a,b]
    let k1 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card
    let k0 := (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card
    (((GProgram.G4.PairClocks.pairClockMeasure k1).prod
        (GProgram.G4.PairClocks.pairClockMeasure k0))
      (GProgram.G4.PairClocks.noFirstMergeEvent k1 (-Real.log B.x) ×ˢ
       GProgram.G4.PairClocks.noFirstMergeEvent k0 (-Real.log B.y))).toReal =
        pairRouteSurvival B.x B.y a b := by
  dsimp only
  rw [original_all_input_arm_clock_likelihood H B 2 ![a,b]]
  change B.x ^ ((GProgram.G4.IndependentRouting.count1
    (Fin.cons a (Fin.cons b (fun i : Fin 0 => Fin.elim0 i)))).choose 2) *
    B.y ^ ((GProgram.G4.IndependentRouting.count0
    (Fin.cons a (Fin.cons b (fun i : Fin 0 => Fin.elim0 i)))).choose 2) = _
  rw [GProgram.G4.IndependentRouting.count1_cons,GProgram.G4.IndependentRouting.count1_cons,
    GProgram.G4.IndependentRouting.count0_cons,GProgram.G4.IndependentRouting.count0_cons]
  cases a <;> cases b <;>
    norm_num [GProgram.G4.IndependentRouting.count0,GProgram.G4.IndependentRouting.count1,
      Fin.sum_univ_zero,pairRouteSurvival,Nat.choose]

end OriginalLabels

noncomputable def cycleDensity (p : Color Site → ℝ) (W : Color Site → Color Site → ℝ) : ℝ :=
  ∑ a : Color Site, ∑ b : Color Site, ∑ c : Color Site, ∑ d : Color Site,
    p a * p b * p c * p d * W a b * W b c * W c d * W d a

noncomputable def measuredC4 (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  cycleDensity (itineraryMass cells) (measuredKernel leading cells)

noncomputable def sourceC4 (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  cycleDensity (itineraryMass cells) (hiddenKernel leading cells)

/-- A finite rational expression in the actual one-root and two-root itinerary laws
returns hidden C4; no graph-density observation was assumed as a primitive. -/
theorem path_resolved_C4_reconstruction (leading : PositiveEdge) (cells : Site → Cell) :
    measuredC4 leading cells = sourceC4 leading cells := by
  simp only [measuredC4,sourceC4,cycleDensity]
  simp_rw [reconstructed_kernel_eq_original]

/-- The explicit two-type C4 factor, a specialization of finite weighted
edge/C4 forcing; no new graphon theorem is claimed. -/
noncomputable def bareC4 (B : PositiveBigon) : ℝ :=
  B.g^4 * B.x^4 + (1-B.g)^4 * B.y^4 +
    4*B.g^3*(1-B.g)*B.x^2 + 4*B.g*(1-B.g)^3*B.y^2 +
    4*B.g^2*(1-B.g)^2*B.x*B.y + 2*B.g^2*(1-B.g)^2

noncomputable def localCycle (C : Cell) (a b c d : Bool) : ℝ :=
  C.connector.survival^4 *
    (coinWeight C.bigon.g a * coinWeight C.bigon.g b *
      coinWeight C.bigon.g c * coinWeight C.bigon.g d *
      pairRouteSurvival C.bigon.x C.bigon.y a b *
      pairRouteSurvival C.bigon.x C.bigon.y b c *
      pairRouteSurvival C.bigon.x C.bigon.y c d *
      pairRouteSurvival C.bigon.x C.bigon.y d a)

lemma localCycle_sum (C : Cell) :
    (∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, localCycle C a b c d) =
      C.connector.survival^4 * bareC4 C.bigon := by
  simp [localCycle,bareC4,coinWeight,pairRouteSurvival]
  ring

lemma cycle_term_factor (leading : PositiveEdge) (cells : Site → Cell)
    (a b c d : Color Site) :
    itineraryMass cells a * itineraryMass cells b * itineraryMass cells c *
      itineraryMass cells d * hiddenKernel leading cells a b * hiddenKernel leading cells b c *
      hiddenKernel leading cells c d * hiddenKernel leading cells d a =
        leading.survival^4 * ∏ i, localCycle (cells i) (a i) (b i) (c i) (d i) := by
  unfold itineraryMass hiddenKernel localCycle
  simp only [Finset.prod_mul_distrib,Finset.prod_pow]
  ring

lemma sum_four_site_products (f : Site → Bool → Bool → Bool → Bool → ℝ) :
    (∑ a : Color Site, ∑ b : Color Site, ∑ c : Color Site, ∑ d : Color Site,
      ∏ i, f i (a i) (b i) (c i) (d i)) =
      ∏ i, ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f i a b c d := by
  calc
    _ = ∑ a : Color Site, ∑ b : Color Site, ∑ c : Color Site,
        ∏ i, ∑ d : Bool, f i (a i) (b i) (c i) d := by
      simp_rw [← Fintype.prod_sum]
    _ = ∑ a : Color Site, ∑ b : Color Site,
        ∏ i, ∑ c : Bool, ∑ d : Bool, f i (a i) (b i) c d := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact (Fintype.prod_sum (fun (i : Site) (c : Bool) =>
        ∑ d : Bool, f i (a i) (b i) c d)).symm
    _ = ∑ a : Color Site, ∏ i, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f i (a i) b c d := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Fintype.prod_sum (fun (i : Site) (b : Bool) =>
        ∑ c : Bool, ∑ d : Bool, f i (a i) b c d)).symm
    _ = _ := (Fintype.prod_sum (fun (i : Site) (a : Bool) =>
        ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f i a b c d)).symm

noncomputable def ordinaryScalar (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  leading.survival * ∏ i, (cells i).connector.survival

/-- Full tensor cycle density, not a separately postulated cell mark. -/
theorem sourceC4_word_factorization (leading : PositiveEdge) (cells : Site → Cell) :
    sourceC4 leading cells = (ordinaryScalar leading cells)^4 * ∏ i, bareC4 (cells i).bigon := by
  unfold sourceC4 cycleDensity
  simp_rw [cycle_term_factor]
  simp only [← Finset.mul_sum]
  rw [sum_four_site_products]
  simp only [localCycle_sum,Finset.prod_mul_distrib,Finset.prod_pow,ordinaryScalar,mul_pow]
  ring

/-- Strict weighted Gram/Cauchy inequality for every genuine positive original
binary cell. Its arm matrix cannot be constant: both arm survivals are <1. -/
theorem positive_bigon_C4_strict (B : PositiveBigon) : bareSurvival B ^ 4 < bareC4 B := by
  let g := B.g
  let h := 1-B.g
  let k00 := g*B.x^2+h
  let k01 := g*B.x+h*B.y
  let k11 := g+h*B.y^2
  let m := g^2*k00+2*g*h*k01+h^2*k11
  have hg : 0 < g := B.g_positive
  have hh : 0 < h := sub_pos.mpr B.g_below_one
  have hx2 : 0 < (B.x-1)^2 := sq_pos_of_ne_zero (by have := B.x_below_one; linarith)
  have hy2 : 0 < (B.y-1)^2 := sq_pos_of_ne_zero (by have := B.y_below_one; linarith)
  have hk : 0 < k00+k11-2*k01 := by
    have he : k00+k11-2*k01 = g*(B.x-1)^2+h*(B.y-1)^2 := by dsimp [k00,k01,k11]; ring
    rw [he]
    exact add_pos (mul_pos hg hx2) (mul_pos hh hy2)
  have hv : bareC4 B - m^2 = 2*g^3*h*(k00-k01)^2+
      g^2*h^2*(k00-k11)^2+2*g*h^3*(k01-k11)^2 := by
    dsimp [bareC4,m,k00,k01,k11,g,h]
    ring
  have hvpos : 0 < bareC4 B-m^2 := by
    rw [hv]
    have h1 : 0 ≤ 2*g^3*h*(k00-k01)^2 := by positivity
    have h2 : 0 ≤ g^2*h^2*(k00-k11)^2 := by positivity
    have h3 : 0 ≤ 2*g*h^3*(k01-k11)^2 := by positivity
    by_cases ha : k00=k01
    · have hb : k01-k11 ≠ 0 := by intro he; linarith
      have h3p : 0 < 2*g*h^3*(k01-k11)^2 := by positivity
      linarith
    · have ha' : k00-k01 ≠ 0 := sub_ne_zero.mpr ha
      have h1p : 0 < 2*g^3*h*(k00-k01)^2 := by positivity
      linarith
  have hm : bareSurvival B ^ 2 ≤ m := by
    have he : m-bareSurvival B^2 = g*h*((g*B.x+h)-(g+h*B.y))^2 := by
      rw [bareSurvival_eq]
      dsimp [m,k00,k01,k11,g,h]
      ring
    have hn : 0 ≤ g*h*((g*B.x+h)-(g+h*B.y))^2 := by positivity
    linarith
  have hm0 : 0 ≤ m := (sq_nonneg (bareSurvival B)).trans hm
  have hmul := mul_nonneg (sub_nonneg.mpr hm) (add_nonneg hm0 (sq_nonneg (bareSurvival B)))
  nlinarith

lemma ordinaryScalar_pos (leading : PositiveEdge) (cells : Site → Cell) :
    0 < ordinaryScalar leading cells :=
  mul_pos leading.positive (Finset.prod_pos (fun i _ => (cells i).connector.positive))

lemma totalNoMerger_factorization (leading : PositiveEdge) (cells : Site → Cell) :
    totalNoMerger leading cells = ordinaryScalar leading cells * ∏ i, bareSurvival (cells i).bigon := by
  unfold totalNoMerger ordinaryScalar cellSurvival
  rw [Finset.prod_mul_distrib]
  ring

/-- ANY finite nonempty private word is separated in the stronger menu. No
margin, known rival length bound or fitted hidden arm is assumed. -/
theorem sourceC4_strict_of_genuine_bigon [Nonempty Site]
    (leading : PositiveEdge) (cells : Site → Cell) :
    totalNoMerger leading cells ^ 4 < sourceC4 leading cells := by
  have hp : (∏ i, bareSurvival (cells i).bigon ^ 4) < ∏ i, bareC4 (cells i).bigon := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro i _
      exact pow_pos (bareSurvival_positive (cells i).bigon) 4
    · intro i _
      exact positive_bigon_C4_strict (cells i).bigon
    · exact Finset.univ_nonempty
  rw [Finset.prod_pow] at hp
  rw [sourceC4_word_factorization,totalNoMerger_factorization,mul_pow]
  exact mul_lt_mul_of_pos_left hp (pow_pos (ordinaryScalar_pos leading cells) 4)

noncomputable def sourceItineraryPMF (cells : Site → Cell) : PMF (Color Site) :=
  PMF.ofFintype (fun c => ENNReal.ofReal (itineraryMass cells c)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => (itineraryMass_pos cells c).le),
      itineraryMass_normalized]
    norm_num)

noncomputable def oneRootData (cells : Site → Cell) (c : Color Site) : ℝ :=
  (sourceItineraryPMF cells c).toReal

noncomputable def twoRootJointData (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ := (sourcePairPMF leading cells (some (c,d))).toReal

lemma oneRootData_eq (cells : Site → Cell) (c : Color Site) :
    oneRootData cells c = itineraryMass cells c := by
  simp only [oneRootData,sourceItineraryPMF,PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (itineraryMass_pos cells c).le

lemma twoRootJointData_eq (leading : PositiveEdge) (cells : Site → Cell) (c d : Color Site) :
    twoRootJointData leading cells c d = observedPair leading cells c d := by
  simp only [twoRootJointData,sourcePairPMF,PMF.ofFintype_apply,outcomeMass]
  exact ENNReal.toReal_ofReal (outcomeMass_nonneg leading cells (some (c,d)))

/-- A formula consuming the NORMALIZED one-root and two-current-root PMF data. -/
noncomputable def dataKernel (leading : PositiveEdge) (cells : Site → Cell)
    (c d : Color Site) : ℝ :=
  twoRootJointData leading cells c d / (oneRootData cells c * oneRootData cells d)

noncomputable def dataC4 (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  cycleDensity (oneRootData cells) (dataKernel leading cells)

noncomputable def dataPairSurvival (leading : PositiveEdge) (cells : Site → Cell) : ℝ :=
  ∑ c : Color Site, ∑ d : Color Site, twoRootJointData leading cells c d

theorem normalized_PMF_data_C4_reconstruction (leading : PositiveEdge) (cells : Site → Cell) :
    dataC4 leading cells = sourceC4 leading cells := by
  unfold dataC4 sourceC4 cycleDensity dataKernel
  simp_rw [oneRootData_eq,twoRootJointData_eq]
  change cycleDensity (itineraryMass cells) (measuredKernel leading cells) = _
  exact path_resolved_C4_reconstruction leading cells

lemma dataPairSurvival_eq (leading : PositiveEdge) (cells : Site → Cell) :
    dataPairSurvival leading cells = totalNoMerger leading cells := by
  unfold dataPairSurvival
  simp_rw [twoRootJointData_eq]
  exact complete_joint_no_merger_mass leading cells

/-- Complete success records satisfy the ACTUAL sequential live-pair branch
recursion. The leading edge is used once, and records never split merged roots. -/
theorem joint_record_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) (c d : Color (Fin (n+1))) :
    observedPair leading (Fin.cons C rest) c d =
      localPairMass C (c 0) (d 0) * observedPair leading rest (Fin.tail c) (Fin.tail d) := by
  unfold observedPair
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.tail]
  ring

/-- First merger is an absorbing OBSERVER outcome, even though the original
biological process may continue on its one opaque surviving ancestral root. -/
theorem failure_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) :
    outcomeMass leading (Fin.cons C rest) none = (1-leading.survival) +
      leading.survival * ((1-cellSurvival C) + cellSurvival C *
        (1-∏ i, cellSurvival (rest i))) := by
  simp only [outcomeMass,totalNoMerger,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring

/-- Coherent changed-menu END THEOREM: the exact measured one-root and two-root joint
itinerary laws detect ordinary/no-independent-bigon words of UNKNOWN length.
The no-bigon scalar is the positive ordinary survival, not identity or time. -/
theorem path_resolved_ordinary_detection (leading : PositiveEdge) (cells : Site → Cell) :
    dataC4 leading cells = dataPairSurvival leading cells ^ 4 ↔ IsEmpty Site := by
  rw [normalized_PMF_data_C4_reconstruction,dataPairSurvival_eq]
  rcases isEmpty_or_nonempty Site with h | h
  · letI := h
    constructor
    · intro _
      exact h
    · intro _
      simp [sourceC4_word_factorization,totalNoMerger_factorization,ordinaryScalar]
  · letI := h
    constructor
    · intro he
      have ht := sourceC4_strict_of_genuine_bigon leading cells
      rw [he] at ht
      exact False.elim ((lt_irrefl _) ht)
    · intro hi
      obtain ⟨i⟩ := h
      exact False.elim (hi.false i)

/-- No-bigon does NOT mean zero population length. Its observable pair
survival is the original strictly positive finite leading ordinary scalar. -/
theorem ordinary_no_bigon_scalar [IsEmpty Site] (leading : PositiveEdge) (cells : Site → Cell) :
    dataPairSurvival leading cells = leading.survival ∧
      dataC4 leading cells = leading.survival ^ 4 := by
  rw [dataPairSurvival_eq,normalized_PMF_data_C4_reconstruction]
  simp [totalNoMerger,sourceC4_word_factorization,ordinaryScalar]



















end GProgram.G4.PathResolved

end FullContextModule40

section FullContextModule41





/-!
# Native original-graph parent-choice compiler and stopped pair source

Work-in-progress toward complete source binding. Every selector refers only
to an actual incoming original edge. Routes are CONSTRUCTED from those local
choices and strictly older original clocks, not supplied as a desired kernel.
Native coin/clock probability and private-word observation binding follow in
this same source-development target; no complete theorem is claimed yet.
-/
namespace UnifiedLean.Source.NativeParentRouting
open Nanuq.Source
open GProgram.G5
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

abbrev Nonroot (N : RootedBinary V E X) := {v : V // v ≠ N.root}

/-- Only source-local data: one ACTUAL incoming edge selected at each nonroot.
No route law, survival identity or identifiability conclusion is a field. -/
structure IncomingSelector (N : RootedBinary V E X) where
  edge : Nonroot N → E
  target : ∀ v, N.graph.target (edge v) = v.1

lemma original_incoming_exists (N : RootedBinary V E X) {v : V} (hv : v ≠ N.root) :
    ∃ e : E, N.graph.target e = v := by
  rcases Relation.ReflTransGen.cases_tail (N.rooted v) with heq | ⟨u,_,e,_,ht⟩
  · exact False.elim (hv heq)
  · exact ⟨e,ht⟩

noncomputable def defaultSelector (N : RootedBinary V E X) : IncomingSelector N where
  edge v := Classical.choose (original_incoming_exists N v.property)
  target v := Classical.choose_spec (original_incoming_exists N v.property)

abbrev Hybrid (N : RootedBinary V E X) := {v : V // N.graph.IsHybrid v}

lemma original_parent_ordering_exists (N : RootedBinary V E X) (v : Hybrid N) :
    ∃ H : GProgram.G2.OriginalHybridParents N, H.hybrid = v.1 := by
  classical
  have hc : (Finset.univ.filter (fun e : E => N.graph.target e = v.1)).card = 2 := v.property.1
  obtain ⟨e,f,hef,hset⟩ := Finset.card_eq_two.mp hc
  have he : N.graph.target e = v.1 := by
    have hm : e ∈ Finset.univ.filter (fun e : E => N.graph.target e = v.1) := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  have hf : N.graph.target f = v.1 := by
    have hm : f ∈ Finset.univ.filter (fun e : E => N.graph.target e = v.1) := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  exact ⟨⟨v.1, v.property, e, f, he, hf, hef⟩, rfl⟩

/-- Source parameter orientation, consisting solely of BOTH actual original
incoming edge occurrences at every actual original hybrid. -/
structure OriginalParentRegistry (N : RootedBinary V E X) where
  parents : Hybrid N → GProgram.G2.OriginalHybridParents N
  original_site : ∀ v, (parents v).hybrid = v.1

noncomputable def canonicalParentRegistry (N : RootedBinary V E X) : OriginalParentRegistry N where
  parents v := Classical.choose (original_parent_ordering_exists N v)
  original_site v := Classical.choose_spec (original_parent_ordering_exists N v)

lemma registry_parent_target (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (v : Hybrid N) (b : Bool) : N.graph.target ((H.parents v).parent b) = v.1 := by
  cases b
  · exact (H.parents v).target0.trans (H.original_site v)
  · exact (H.parents v).target1.trans (H.original_site v)

/-- Current-root coins choose only their actual ORIGINAL hybrid parent. Every
nonhybrid step uses its fixed original incoming edge; root is terminal. -/
noncomputable def coinSelector (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (coin : Hybrid N → Bool) : IncomingSelector N where
  edge v := if hv : N.graph.IsHybrid v.1 then (H.parents ⟨v.1,hv⟩).parent (coin ⟨v.1,hv⟩)
    else (defaultSelector N).edge v
  target v := by
    by_cases hv : N.graph.IsHybrid v.1
    · simp only [dif_pos hv]
      exact registry_parent_target N H ⟨v.1,hv⟩ _
    · simp only [dif_neg hv]
      exact (defaultSelector N).target v

noncomputable def olderRank (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) : Nat :=
  (Finset.univ.filter (fun w : V => C.age v < C.age w)).card

lemma olderRank_edge_decreases (N : RootedBinary V E X) (C : Calendar N.graph) (e : E) :
    olderRank N C (N.graph.source e) < olderRank N C (N.graph.target e) := by
  unfold olderRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    exact (C.edge_older e).trans hw
  · intro heq
    have hm : N.graph.source e ∈ Finset.univ.filter
        (fun w : V => C.age (N.graph.target e) < C.age w) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact C.edge_older e
    rw [← heq] at hm
    simpa using hm

/-- Every traversed original edge was selected at its actual younger endpoint. -/
def RespectsSelector (N : RootedBinary V E X) (P : IncomingSelector N) (es : List E) : Prop :=
  ∀ e ∈ es, ∃ h : N.graph.target e ≠ N.root,
    P.edge ⟨N.graph.target e,h⟩ = e

lemma selector_edge_respects (N : RootedBinary V E X) (P : IncomingSelector N)
    (v : Nonroot N) : RespectsSelector N P [P.edge v] := by
  intro e he
  have h : e = P.edge v := by simpa using he
  subst e
  have ht : N.graph.target (P.edge v) ≠ N.root := by rw [P.target]; exact v.property
  refine ⟨ht,?_⟩
  congr 1
  exact Subtype.ext (P.target v)

lemma selected_original_path_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) :
    ∃ es : List E, EdgePath N.graph N.root v es ∧ RespectsSelector N P es := by
  have aux : ∀ n : Nat, ∀ w : V, olderRank N C w = n →
      ∃ es : List E, EdgePath N.graph N.root w es ∧ RespectsSelector N P es := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      by_cases hw : w = N.root
      · subst w
        exact ⟨[],EdgePath.nil _,by intro e he; simp at he⟩
      · let e := P.edge ⟨w,hw⟩
        have ht : N.graph.target e = w := P.target ⟨w,hw⟩
        have hlt : olderRank N C (N.graph.source e) < n := by
          have h := olderRank_edge_decreases N C e
          rwa [ht,hn] at h
        obtain ⟨es,hpath,hselect⟩ := ih _ hlt _ rfl
        have last : EdgePath N.graph (N.graph.source e) w [e] :=
          EdgePath.cons rfl (by rw [ht]; exact EdgePath.nil w)
        refine ⟨es++[e],hpath.append last,?_⟩
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hselect f hf
        · exact selector_edge_respects N P ⟨w,hw⟩ f hf
  exact aux (olderRank N C v) v rfl

/-- Constructed original-edge route, valid for every finite native source,
strict calendar and local original incoming-edge selector. -/
noncomputable def compiledRoute (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) : List E :=
  Classical.choose (selected_original_path_exists N C P v)

theorem compiledRoute_source_spec (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) :
    EdgePath N.graph N.root v (compiledRoute N C P v) ∧
      RespectsSelector N P (compiledRoute N C P v) :=
  Classical.choose_spec (selected_original_path_exists N C P v)

/-- ALL original-tip routes are compiled from the local current-owner coins
on the unchanged graph. Unused coin sites do not invent route segments. -/
noncomputable def compiledRouteFamily (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : X → Hybrid N → Bool) : RouteFamily N where
  edges x := compiledRoute N C (coinSelector N H (coin x)) (N.leaf x)
  valid x := (compiledRoute_source_spec N C (coinSelector N H (coin x)) (N.leaf x)).1

/-- Record ties each traversed original parent edge to the SAME original
hybrid occurrence and the current root owner's actual preassigned coin. -/
theorem compiled_original_parent_consistency (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (coin : X → Hybrid N → Bool) (x : X) {e : E}
    (he : e ∈ (compiledRouteFamily N C H coin).edges x)
    (hy : N.graph.IsHybrid (N.graph.target e)) :
    e = (H.parents ⟨N.graph.target e,hy⟩).parent (coin x ⟨N.graph.target e,hy⟩) := by
  obtain ⟨hne,hsel⟩ := (compiledRoute_source_spec N C (coinSelector N H (coin x))
    (N.leaf x)).2 e he
  simpa only [coinSelector,dif_pos hy] using hsel.symm








end UnifiedLean.Source.NativeParentRouting

end FullContextModule41

section FullContextModule42




/-!
# Original-edge stopped pair clocks

Contributor: dot, 2026-10-02. For two still-separate current roots, each ORIGINAL
edge occurrence has its own independent exponential holding clock, with the
source edge's positive rate. The ancestral population has one further clock.
Local exposure is computed from the actual graph calendar and compiled paths.
The product-measure no-first-merger probability is proved, rather than supplied
as a field of a source contract. This is the pair process up to its first merger;
it does not construct later multi-lineage merger/reset dynamics or an instrument.
-/
namespace UnifiedLean.Source.NativePairClockLaw
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- Positive constant rates of the ORIGINAL edge populations and the one
ancestral population. No probability-law identity is a structure field. -/
structure PositivePairRates (E : Type*) where
  edge : E → ℝ
  edge_pos : ∀ e, 0 < edge e
  ancestral : ℝ
  ancestral_pos : 0 < ancestral

noncomputable def pairRate (r : PositivePairRates E) : Option E → ℝ
  | none => r.ancestral
  | some e => r.edge e

lemma pairRate_pos (r : PositivePairRates E) (e : Option E) : 0 < pairRate r e := by
  cases e with
  | none => exact r.ancestral_pos
  | some e => exact r.edge_pos e

/-- The none coordinate is the ordinary ancestral population above the root;
some e retains the actual original edge ID, including parallel occurrences. -/
noncomputable def occupiedDuration (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) : Option E → ℝ
  | none => max 0 (t - C.age N.root)
  | some e => if e ∈ R.edges x ∧ e ∈ R.edges y then exposure N.graph C t e else 0

lemma occupiedDuration_nonnegative (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) (e : Option E) :
    0 ≤ occupiedDuration N C R x y t e := by
  cases e with
  | none => exact le_max_left _ _
  | some e =>
      simp only [occupiedDuration]
      split_ifs
      · exact le_max_left _ _
      · exact le_refl _

noncomputable def originalClockMeasure (r : PositivePairRates E) :
    Measure (Option E → ℝ) := Measure.pi (fun e => expMeasure (pairRate r e))

/-- Survival of all local holding clocks. A first merger makes the observer
absorbing; this event does not use coins of any post-merger descendant copies. -/
def noFirstMerger (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) : Set (Option E → ℝ) :=
  Set.univ.pi (fun e => Set.Ioi (occupiedDuration N C R x y t e))

theorem noFirstMerger_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) (clock : Option E → ℝ) :
    clock ∈ noFirstMerger N C R x y t ↔
      ∀ e, occupiedDuration N C R x y t e < clock e := by
  simp [noFirstMerger, Set.mem_pi]

lemma positive_exp_clock_tail {rate duration : ℝ}
    (hr : 0 < rate) (hd : 0 ≤ duration) :
    (expMeasure rate).real (Set.Ioi duration) = Real.exp (-(rate * duration)) := by
  letI : IsProbabilityMeasure (expMeasure rate) := isProbabilityMeasure_expMeasure hr
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic,
    ← cdf_eq_real, cdf_expMeasure_eq hr, if_pos hd]
  ring

/-- The pair survival is computed from independent original holding-time
measures. The exponential hazard is a conclusion of the product calculation. -/
theorem original_clock_no_merger_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) (t : ℝ) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      Real.exp (-(∑ e : Option E, pairRate r e * occupiedDuration N C R x y t e)) := by
  letI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  rw [originalClockMeasure, noFirstMerger, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ e : Option E, (expMeasure (pairRate r e)).real
    (Set.Ioi (occupiedDuration N C R x y t e))) = _
  simp only [positive_exp_clock_tail (pairRate_pos r _)
    (occupiedDuration_nonnegative N C R x y t _)]
  rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Finite graph overlap plus the correctly timed ancestral-population clock. -/
theorem native_hazard_decomposition (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (R : RouteFamily N) (x y : X) (t : ℝ) :
    (∑ e : Option E, pairRate r e * occupiedDuration N C R x y t e) =
      accumulatedHazard N C r.edge R x y t + r.ancestral * max 0 (t-C.age N.root) := by
  rw [Fintype.sum_option]
  simp only [pairRate, occupiedDuration]
  rw [add_comm]
  congr 1
  unfold accumulatedHazard
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

/-- Actual stopped pair law, including the ancestral population. -/
theorem original_clock_survival_eq_routeSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) (t : ℝ) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      routeSurvival N C r.edge R x y t *
        Real.exp (-(r.ancestral * max 0 (t-C.age N.root))) := by
  rw [original_clock_no_merger_probability, native_hazard_decomposition,
    neg_add, Real.exp_add, routeSurvival]

/-- Below the actual original root, the earlier exponential route functional
is exactly this source pair probability. No ancestral exposure is missing. -/
theorem below_root_original_clock_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      routeSurvival N C r.edge R x y t := by
  rw [original_clock_survival_eq_routeSurvival, max_eq_left (sub_nonpos.mpr ht)]
  simp

/-- Graph+local original-parent choices supply the routes in the probability
law. A desired survival identity was not passed to the compiler. -/
theorem compiled_original_pair_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (H : OriginalParentRegistry N)
    (coin : X → Hybrid N → Bool) (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    (originalClockMeasure r (noFirstMerger N C (compiledRouteFamily N C H coin) x y t)).toReal =
      routeSurvival N C r.edge (compiledRouteFamily N C H coin) x y t :=
  below_root_original_clock_law N C r (compiledRouteFamily N C H coin) x y ht









end UnifiedLean.Source.NativePairClockLaw

end FullContextModule42

section FullContextModule43






/-!
# Constructed positive-rate uniformized step of the ORIGINAL source state

Contributor: dot, 2026-10-02. Candidate next finite-time source-kernel gate.
Actual original edge/root populations supply CURRENT legal pairs and their
positive constant rates. A copy-cap/rate-derived global bound constructs a
normalized holding-or-merger choice law; every merger updates the existing
source forest and is encoded back into its admitted finite snapshot. This is
an internal uniformization primitive, not yet a continuous-time/calendar or
timed-path observation theorem. No desired transition law is a contract field.
-/
namespace UnifiedLean.Source.UniformizedSourceStep
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev Code (N : RootedBinary V E X) (sample : Copy → X) := AdmittedSnapshot N sample

noncomputable def state {N : RootedBinary V E X} {sample : Copy → X}
    (s : Code N sample) : State V E Copy := decodeSnapshot N.root s.val

noncomputable def originalPlace (N : RootedBinary V E X) : Option E → Location V E
  | none => .rootPopulation N.root
  | some e => .edge e

lemma originalPlace_not_node (N : RootedBinary V E X) (i : Option E) (v : V) :
    originalPlace N i ≠ .node v := by
  cases i <;> intro h <;> cases h

/-- Ordered pairs have half the population pair rate. Both orientations
encode the same unordered Kingman event; child order remains internal. -/
abbrev Choice (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :=
  Σ i : Option E, {p : Copy × Copy // p ∈ (populationRoots (state s) (originalPlace N i)).offDiag}

noncomputable instance choiceFintype (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Fintype (Choice N s) := by
  unfold Choice
  infer_instance

noncomputable def choiceRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) : ℝ := pairRate r p.1 / 2

noncomputable def totalRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : ℝ := ∑ p : Choice N s, choiceRate N r s p

noncomputable def globalRateBound (r : PositivePairRates E) : ℝ :=
  (1 + ∑ i : Option E, pairRate r i) * (1 + (Fintype.card Copy : ℝ)^2)

lemma globalRateBound_positive (r : PositivePairRates E) :
    0 < globalRateBound (Copy := Copy) r := by
  have hsum : 0 ≤ ∑ i : Option E, pairRate r i :=
    Finset.sum_nonneg (fun i _ => (pairRate_pos r i).le)
  unfold globalRateBound
  positivity

lemma totalRate_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : 0 ≤ totalRate N r s := by
  apply Finset.sum_nonneg
  intro p _
  exact div_nonneg (pairRate_pos r p.1).le (by norm_num)

/-- A genuine explicit rate bound, not an input-supplied source-size or
probability premise. The original graph/rates and copy carrier remain fixed. -/
theorem totalRate_le_globalRateBound (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    totalRate N r s ≤ globalRateBound (Copy := Copy) r := by
  have hsum : 0 ≤ ∑ i : Option E, pairRate r i :=
    Finset.sum_nonneg (fun i _ => (pairRate_pos r i).le)
  have hbound : totalRate N r s ≤
      (∑ i : Option E, pairRate r i) * (Fintype.card Copy : ℝ)^2 := by
    unfold totalRate choiceRate
    rw [Fintype.sum_sigma]
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    let pairs := (populationRoots (state s) (originalPlace N i)).offDiag
    have hc : (pairs.card : ℝ) ≤ (Fintype.card Copy : ℝ)^2 := by
      have hh := Finset.card_le_univ pairs
      simpa only [Fintype.card_prod,Nat.cast_mul,pow_two] using
        (show (pairs.card : ℝ) ≤ (Fintype.card (Copy × Copy) : ℝ) by exact_mod_cast hh)
    change (∑ _ : pairs, pairRate r i / 2) ≤ _
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    have hp := pairRate_pos r i
    nlinarith [sq_nonneg (Fintype.card Copy : ℝ)]
  unfold globalRateBound
  nlinarith [sq_nonneg (Fintype.card Copy : ℝ)]

noncomputable def choiceMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Option (Choice N s) → ℝ
  | none => 1-totalRate N r s/globalRateBound (Copy := Copy) r
  | some p => choiceRate N r s p/globalRateBound (Copy := Copy) r

lemma choiceMass_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Option (Choice N s)) :
    0 ≤ choiceMass N r s p := by
  cases p with
  | none =>
      apply sub_nonneg.mpr
      exact (div_le_one (globalRateBound_positive (Copy := Copy) r)).mpr
        (totalRate_le_globalRateBound N r s)
  | some p =>
      exact div_nonneg (div_nonneg (pairRate_pos r p.1).le (by norm_num))
        (globalRateBound_positive (Copy := Copy) r).le

lemma choiceMass_normalized (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (∑ p : Option (Choice N s), choiceMass N r s p) = 1 := by
  rw [Fintype.sum_option]
  simp only [choiceMass]
  rw [← Finset.sum_div]
  change 1-totalRate N r s/globalRateBound (Copy := Copy) r +
    totalRate N r s/globalRateBound (Copy := Copy) r = 1
  ring

noncomputable def choicePMF (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Option (Choice N s)) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (choiceMass N r s p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => choiceMass_nonnegative N r s p),
      choiceMass_normalized]
    simp)

/-- The destination is built by the inherited ACTUAL legal source merger,
with SourceValid preservation proved there, then exact finite snapshot coding. -/
noncomputable def stepDestination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Option (Choice N s) → Code N sample
  | none => s
  | some p =>
      admittedCode N sample (merge (state s) p.2.val.1 p.2.val.2)
        (merge_source_valid N sample (state s) s.property
          (population_pair_is_source_legal (state s) (originalPlace N p.1)
            (originalPlace_not_node N p.1) p.2.property))

/-- A normalized, source-valid finite-state step. Dummy holding leaves the
source unchanged; mergers preserve all original graph/sample/registry IDs. -/
noncomputable def sourceStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Code N sample) :=
  (choicePMF N r s).map (stepDestination N s)





end UnifiedLean.Source.UniformizedSourceStep

end FullContextModule43

section FullContextModule44



/-!
# Actual source-population generator after full genealogy pruning

Contributor: dot, 2026-10-02. Reuses the inherited legal visible-pair bijection
and the actual silent-merger pruning link. A projected merger is defined from
the selected genealogies themselves; no generator identity is a contract field.
This is the infinitesimal source link. A continuous-time transition semigroup,
calendar scheduler/pulse transport and entire full-source law still require
construction and integration before a whole-source projectivity theorem.
-/
namespace UnifiedLean.Source.SourceForestGeneratorIntertwining
open GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open scoped BigOperators Classical
variable {V E Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

/-- Read one whole selected genealogy using any selected label in its block.
Valid original source states prove this independent of the label choice. -/
noncomputable def viewBlockTree (v : SelectedView V E Copy) (A : Finset Copy) :
    Option (Genealogy Copy) :=
  if h : A.Nonempty then v.genealogy (Classical.choose h) else none

noncomputable def projectedMerge (v : SelectedView V E Copy) (A B : Finset Copy) :
    SelectedView V E Copy where
  genealogy x := if x ∈ A ∪ B then
    Genealogy.joinPruned (viewBlockTree v A) (viewBlockTree v B) else v.genealogy x
  population := v.population
  register := v.register

lemma selectedGenealogy_at_block (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a x : Copy} (ha : a ∈ s.live)
    (hx : x ∈ selectedBlock s keep a) :
    (selectedView s keep).genealogy x = (s.genealogy a).prune keep := by
  obtain ⟨hxkeep,hxa⟩ := (selectedBlock_eq_fiber s hs keep ha x).mp hx
  simp only [selectedView,selectedGenealogy,if_pos hxkeep,hxa]

lemma viewBlockTree_source (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a : Copy} (ha : a ∈ s.live)
    (hA : (selectedBlock s keep a).Nonempty) :
    viewBlockTree (selectedView s keep) (selectedBlock s keep a) =
      (s.genealogy a).prune keep := by
  rw [viewBlockTree,dif_pos hA]
  exact selectedGenealogy_at_block s hs keep ha (Classical.choose_spec hA)

/-- A visible original legal merger induces exactly the genealogy graft on
its two selected blocks, regardless of the original representative IDs. -/
theorem selectedView_merge_visible (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {a b : Copy} (hm : LegalMerge s a b)
    (hA : (selectedBlock s keep a).Nonempty)
    (hB : (selectedBlock s keep b).Nonempty) :
    selectedView (merge s a b) keep =
      projectedMerge (selectedView s keep) (selectedBlock s keep a) (selectedBlock s keep b) := by
  apply SelectedView.ext
  · funext x
    change selectedGenealogy (merge s a b) keep x =
      if x ∈ selectedBlock s keep a ∪ selectedBlock s keep b then
        Genealogy.joinPruned (viewBlockTree (selectedView s keep) (selectedBlock s keep a))
          (viewBlockTree (selectedView s keep) (selectedBlock s keep b))
      else selectedGenealogy s keep x
    rw [viewBlockTree_source s hs keep hm.first_live hA,
      viewBlockTree_source s hs keep hm.second_live hB]
    by_cases hx : x ∈ keep
    · have hxA : x ∈ selectedBlock s keep a ↔ s.ancestor x = a := by
        rw [selectedBlock_eq_fiber s hs keep hm.first_live x]
        simp only [hx,true_and]
      have hxB : x ∈ selectedBlock s keep b ↔ s.ancestor x = b := by
        rw [selectedBlock_eq_fiber s hs keep hm.second_live x]
        simp only [hx,true_and]
      simp only [selectedGenealogy,if_pos hx,Finset.mem_union,hxA,hxB]
      by_cases hb : s.ancestor x = b
      · simp [merge,hb,Genealogy.prune]
      · by_cases ha : s.ancestor x = a
        · simp [merge,hb,ha,Genealogy.prune]
        · simp [merge,hb,ha]
    · have hxA : x ∉ selectedBlock s keep a := by
        intro h
        exact hx ((Finset.mem_inter.mp h).2)
      have hxB : x ∉ selectedBlock s keep b := by
        intro h
        exact hx ((Finset.mem_inter.mp h).2)
      simp [selectedGenealogy,hx,hxA,hxB]
  · exact selectedLocation_merge_unchanged s keep hm
  · rfl

noncomputable def sourceIncrement (s : State V E Copy) (keep : Finset Copy)
    (f : SelectedView V E Copy → ℝ) (p : Copy × Copy) : ℝ :=
  f (selectedView (merge s p.1 p.2) keep) - f (selectedView s keep)

noncomputable def projectedIncrement (s : State V E Copy) (keep : Finset Copy)
    (f : SelectedView V E Copy → ℝ) (p : Finset Copy × Finset Copy) : ℝ :=
  f (projectedMerge (selectedView s keep) p.1 p.2) - f (selectedView s keep)

noncomputable def originalPopulationGenerator (s : State V E Copy)
    (keep : Finset Copy) (place : Location V E) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (rate/2) * ∑ p ∈ (populationRoots s place).offDiag, sourceIncrement s keep f p

noncomputable def selectedPopulationGenerator (s : State V E Copy)
    (keep : Finset Copy) (place : Location V E) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (rate/2) * ∑ p ∈ (selectedActiveBlocks s keep (populationRoots s place)).offDiag,
    projectedIncrement s keep f p

lemma visible_offDiag_subset (s : State V E Copy) (keep active : Finset Copy) :
    (visibleActiveRoots s keep active).offDiag ⊆ active.offDiag := by
  intro p hp
  rcases Finset.mem_offDiag.mp hp with ⟨ha,hb,hne⟩
  exact Finset.mem_offDiag.mpr
    ⟨(Finset.mem_filter.mp ha).1,(Finset.mem_filter.mp hb).1,hne⟩

/-- All source-legal population pairs participate. Invisible pairs cancel
because actual pruning makes their whole forest/population/register increment
zero; visible pairs then use the inherited unique legal pair preimage. -/
theorem actual_population_generator_intertwining (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (place : Location V E) (hplace : ∀ v, place ≠ Location.node v)
    (rate : ℝ) (f : SelectedView V E Copy → ℝ) :
    originalPopulationGenerator s keep place rate f =
      selectedPopulationGenerator s keep place rate f := by
  unfold originalPopulationGenerator selectedPopulationGenerator
  congr 1
  have hrestrict :
      (∑ p ∈ (populationRoots s place).offDiag, sourceIncrement s keep f p) =
        ∑ p ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag,
          sourceIncrement s keep f p := by
    symm
    apply Finset.sum_subset (visible_offDiag_subset s keep (populationRoots s place))
    intro p hp hv
    have hm := population_pair_is_source_legal s place hplace hp
    have hi : ¬(selectedBlock s keep p.1).Nonempty ∨
        ¬(selectedBlock s keep p.2).Nonempty := by
      by_contra hn
      push Not at hn
      apply hv
      obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp hp
      exact Finset.mem_offDiag.mpr
        ⟨Finset.mem_filter.mpr ⟨ha,hn.1⟩,Finset.mem_filter.mpr ⟨hb,hn.2⟩,hne⟩
    exact silent_merger_readout_increment_zero s hs keep hm hi f
  rw [hrestrict]
  trans ∑ p ∈ (visibleActiveRoots s keep (populationRoots s place)).offDiag,
    projectedIncrement s keep f (pairMap (selectedBlock s keep) p)
  · apply Finset.sum_congr rfl
    intro p hp
    have hm := visible_population_pair_is_source_legal s keep place hplace hp
    obtain ⟨ha,hb,_⟩ := Finset.mem_offDiag.mp hp
    unfold sourceIncrement projectedIncrement pairMap
    rw [selectedView_merge_visible s hs keep hm
      (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2]
  · exact projected_pair_sum _ _
      (selectedBlock_injective_on_visibleActive s hs keep (populationRoots s place)
        (populationRoots_subset_live s place)) (projectedIncrement s keep f)




end UnifiedLean.Source.SourceForestGeneratorIntertwining

end FullContextModule44

section FullContextModule45


/-!
# Intrinsic selected-view generator for the full original population catalogue

Contributor: dot, 2026-10-02. Selected active blocks are reconstructed from
selected genealogies and their original population IDs, rather than looked up
through hidden original representative IDs. The derived generator is therefore
an intrinsic function of the pruned view. This fills the actual generator
factor-through gate for arbitrary finite copy panels; full finite-time kernels,
calendar/pulse scheduling and stochastic source projectivity remain separate.
-/
namespace UnifiedLean.Source.SourceForestIntrinsicGenerator
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable [DecidableEq Copy] [Fintype Copy]

/-- Reads the selected CURRENT block from the INTERNAL pruned genealogy of
any retained original label, retaining its ORIGINAL population ID. -/
noncomputable def viewPopulationBlocks (v : SelectedView V E Copy)
    (keep : Finset Copy) (place : Location V E) : Finset (Finset Copy) :=
  (keep.filter (fun x => v.population x = some place)).image
    (fun x => Genealogy.optionLeaves (v.genealogy x))

lemma selected_view_block_leaves (s : State V E Copy) (keep : Finset Copy)
    {x : Copy} (hx : x ∈ keep) :
    Genealogy.optionLeaves ((selectedView s keep).genealogy x) =
      selectedBlock s keep (s.ancestor x) := by
  simp only [selectedView,selectedGenealogy,if_pos hx,Genealogy.prune_leaves,selectedBlock]

/-- The old full-state catalogue is exactly reconstructible from the selected
view. Hidden original representatives do not enter the projected generator. -/
theorem selected_active_blocks_eq_intrinsic (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (place : Location V E) :
    selectedActiveBlocks s keep (populationRoots s place) =
      viewPopulationBlocks (selectedView s keep) keep place := by
  ext A
  unfold selectedActiveBlocks viewPopulationBlocks
  constructor
  · intro h
    obtain ⟨l,hl,hA⟩ := Finset.mem_image.mp h
    obtain ⟨hpop,hvis⟩ := Finset.mem_filter.mp hl
    obtain ⟨hlive,hlplace⟩ := Finset.mem_filter.mp hpop
    obtain ⟨x,hx⟩ := hvis
    obtain ⟨hxkeep,hxa⟩ := (selectedBlock_eq_fiber s hs keep hlive x).mp hx
    apply Finset.mem_image.mpr
    refine ⟨x,Finset.mem_filter.mpr ⟨hxkeep,?_⟩,?_⟩
    · simp only [selectedView,selectedLocation,if_pos hxkeep,copyLocation,hxa,hlplace]
    · rw [selected_view_block_leaves s keep hxkeep,hxa]
      exact hA
  · intro h
    obtain ⟨x,hx,hA⟩ := Finset.mem_image.mp h
    obtain ⟨hxkeep,hxpop⟩ := Finset.mem_filter.mp hx
    have hlive : s.ancestor x ∈ s.live := hs.ancestor_live x
    have hlplace : s.location (s.ancestor x) = place := by
      exact Option.some.inj (by simpa only
        [selectedView,selectedLocation,if_pos hxkeep,copyLocation] using hxpop)
    have hvis : (selectedBlock s keep (s.ancestor x)).Nonempty :=
      ⟨x,(selectedBlock_eq_fiber s hs keep hlive x).mpr ⟨hxkeep,rfl⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨s.ancestor x,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hlive,hlplace⟩,hvis⟩,?_⟩
    rw [selected_view_block_leaves s keep hxkeep] at hA
    exact hA

noncomputable def viewPopulationGenerator (v : SelectedView V E Copy)
    (keep : Finset Copy) (place : Location V E) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (rate/2) * ∑ p ∈ (viewPopulationBlocks v keep place).offDiag,
    (f (projectedMerge v p.1 p.2) - f v)

/-- Infinitesimal factor-through in the actual source state and its intrinsic
selected pruned view, for every forest/population/register readout. -/
theorem original_population_generator_factors_through_view (s : State V E Copy)
    (hs : Valid s) (keep : Finset Copy) (place : Location V E)
    (hplace : ∀ v, place ≠ Location.node v) (rate : ℝ)
    (f : SelectedView V E Copy → ℝ) :
    originalPopulationGenerator s keep place rate f =
      viewPopulationGenerator (selectedView s keep) keep place rate f := by
  rw [actual_population_generator_intertwining s hs keep place hplace rate f]
  unfold selectedPopulationGenerator viewPopulationGenerator projectedIncrement
  rw [selected_active_blocks_eq_intrinsic s hs keep place]

/-- ORIGINAL edge occurrences plus the retained ORIGINAL ancestral population.
No physical source is contracted, and rates remain one assignment per source. -/
noncomputable def nativeSourceGenerator (root : V) (s : State V E Copy)
    (keep : Finset Copy) (edgeRate : E → ℝ) (ancestralRate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (∑ e : E, originalPopulationGenerator s keep (.edge e) (edgeRate e) f) +
    originalPopulationGenerator s keep (.rootPopulation root) ancestralRate f

noncomputable def intrinsicSourceGenerator (root : V) (v : SelectedView V E Copy)
    (keep : Finset Copy) (edgeRate : E → ℝ) (ancestralRate : ℝ)
    (f : SelectedView V E Copy → ℝ) : ℝ :=
  (∑ e : E, viewPopulationGenerator v keep (.edge e) (edgeRate e) f) +
    viewPopulationGenerator v keep (.rootPopulation root) ancestralRate f

/-- All original source populations simultaneously. Multiple original copies,
including invisible live representatives, are supported by the actual state. -/
theorem native_source_generator_intertwining (root : V) (s : State V E Copy)
    (hs : Valid s) (keep : Finset Copy) (edgeRate : E → ℝ) (ancestralRate : ℝ)
    (f : SelectedView V E Copy → ℝ) :
    nativeSourceGenerator root s keep edgeRate ancestralRate f =
      intrinsicSourceGenerator root (selectedView s keep) keep edgeRate ancestralRate f := by
  unfold nativeSourceGenerator intrinsicSourceGenerator
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    exact original_population_generator_factors_through_view s hs keep (.edge e)
      (fun v h => by cases h) _ f
  · exact original_population_generator_factors_through_view s hs keep (.rootPopulation root)
      (fun v h => by cases h) _ f

/-- Explicit native-source wrapper uses the inherited original graph and
copy-to-original-tip sample assignment. It assumes only its genuine proved
source-state invariant, not a generator/kernel equation. -/
theorem original_source_valid_generator_intertwining [Fintype X]
    (N : RootedBinary V E X) (sample : Copy → X) (s : State V E Copy)
    (hs : SourceValid N sample s) (keep : Finset Copy)
    (edgeRate : E → ℝ) (ancestralRate : ℝ) (f : SelectedView V E Copy → ℝ) :
    nativeSourceGenerator N.root s keep edgeRate ancestralRate f =
      intrinsicSourceGenerator N.root (selectedView s keep) keep edgeRate ancestralRate f :=
  native_source_generator_intertwining N.root s hs.forest keep edgeRate ancestralRate f





end UnifiedLean.Source.SourceForestIntrinsicGenerator

end FullContextModule45

section FullContextModule46





/-!
# Actual normalized source step bound to its original forest generator

Contributor: dot, 2026-10-02. The uniformized finite PMF is connected to the
existing original forest/population/register generator, including source-valid
snapshot encoding after each real merger. This is the source operator instance
needed before matrix-exponential/finite-time transport; calendar-compatible
reachability and timed-path observations remain separate.
-/
namespace UnifiedLean.Source.SourceStepGeneratorBinding
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestGeneratorIntertwining
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open MeasureTheory
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance codeMeasurable {N : RootedBinary V E X} {sample : Copy → X} :
    MeasurableSpace (Code N sample) := ⊤
local instance choiceMeasurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : MeasurableSpace (Option (Choice N s)) := ⊤

lemma choicePMF_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Option (Choice N s)) :
    (choicePMF N r s p).toReal = choiceMass N r s p := by
  simp only [choicePMF,PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (choiceMass_nonnegative N r s p)]

/-- Actual PMF expectation, not a separate fitted finite weighted table. -/
theorem sourceStep_expectation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (F : Code N sample → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * F d) =
      ∑ p : Option (Choice N s), choiceMass N r s p * F (stepDestination N s p) := by
  have hm : Measurable (stepDestination N s) := measurable_of_countable _
  have hf : Measurable F := measurable_of_countable _
  calc
    _ = ∫ d, F d ∂(sourceStep N r s).toMeasure := by
      rw [PMF.integral_eq_sum]
      simp only [smul_eq_mul]
    _ = ∫ p, F (stepDestination N s p) ∂(choicePMF N r s).toMeasure := by
      rw [sourceStep,← PMF.toMeasure_map (stepDestination N s) (choicePMF N r s) hm,integral_map hm.aemeasurable hf.aestronglyMeasurable]
    _ = _ := by
      rw [PMF.integral_eq_sum]
      simp only [smul_eq_mul,choicePMF_real]

/-- A real source merger is encoded/decoded without changing its complete
selected INTERNAL view. Original graph/sample/registry IDs remain fixed. -/
lemma merged_destination_selectedView (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (p : Choice N s) :
    selectedView (state (stepDestination N s (some p))) keep =
      selectedView (merge (state s) p.2.val.1 p.2.val.2) keep := by
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  let hs := merge_source_valid N sample (state s) s.property hm
  exact decode_encode_selectedView N.root (merge (state s) p.2.val.1 p.2.val.2) hs.forest keep

/-- The actual weighted source choices have the EXACT inherited generator
increment, with no posterior/refitted source or assumed generator field. -/
theorem actual_choice_increment_eq_native_generator (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (f : SelectedView V E Copy → ℝ) :
    (∑ p : Choice N s, choiceRate N r s p *
      (f (selectedView (state (stepDestination N s (some p))) keep) -
        f (selectedView (state s) keep))) =
      nativeSourceGenerator N.root (state s) keep r.edge r.ancestral f := by
  simp_rw [merged_destination_selectedView]
  unfold choiceRate
  rw [Fintype.sum_sigma,Fintype.sum_option]
  unfold nativeSourceGenerator originalPopulationGenerator sourceIncrement
  simp only [pairRate,originalPlace]
  rw [add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro e _
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_attach ((populationRoots (state s) (.edge e)).offDiag)
      (fun p : Copy × Copy => f (selectedView (merge (state s) p.1 p.2) keep) -
        f (selectedView (state s) keep))
  · rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_attach ((populationRoots (state s) (.rootPopulation N.root)).offDiag)
      (fun p : Copy × Copy => f (selectedView (merge (state s) p.1 p.2) keep) -
        f (selectedView (state s) keep))

/-- Explicit finite-step expectation is the current readout plus its actual
source-generator increment divided by the PROVED global uniformization rate. -/
theorem sourceStep_expectation_eq_generator (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (f : SelectedView V E Copy → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * f (selectedView (state d) keep)) =
      f (selectedView (state s) keep) +
        nativeSourceGenerator N.root (state s) keep r.edge r.ancestral f /
          globalRateBound (Copy := Copy) r := by
  rw [sourceStep_expectation,Fintype.sum_option]
  simp only [choiceMass]
  rw [show stepDestination N s none = s from rfl]
  rw [← actual_choice_increment_eq_native_generator N r s keep f]
  have hpos := globalRateBound_positive (Copy := Copy) r
  have hsum : (∑ p : Choice N s, choiceRate N r s p *
      (f (selectedView (state (stepDestination N s (some p))) keep) -
        f (selectedView (state s) keep))) =
      (∑ p : Choice N s, choiceRate N r s p *
        f (selectedView (state (stepDestination N s (some p))) keep)) -
      totalRate N r s * f (selectedView (state s) keep) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,totalRate]
  rw [hsum]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  ring

/-- The constructed normalized source PMF's entire selected-view expectation
is intrinsic to that view. This is the actual finite-step source binding for
the existing infinitesimal G2 transport, not yet a time/calendar theorem. -/
theorem sourceStep_selected_expectation_intrinsic (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (keep : Finset Copy) (f : SelectedView V E Copy → ℝ) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * f (selectedView (state d) keep)) =
      f (selectedView (state s) keep) +
        intrinsicSourceGenerator N.root (selectedView (state s) keep) keep r.edge r.ancestral f /
          globalRateBound (Copy := Copy) r := by
  rw [sourceStep_expectation_eq_generator,
    native_source_generator_intertwining N.root (state s) s.property.forest keep r.edge r.ancestral f]






end UnifiedLean.Source.SourceStepGeneratorBinding

end FullContextModule46

section FullContextModule47


/-!
# Rectangular projection through finite matrix exponentials

Contributor: dot (OpenAI), 2026-10-02.
This conditional linear-algebra adapter reuses mathlib's exponential series,
`SemiconjBy.exp_right`, and finite block-matrix algebra. It is for the actual
finite-source generator/projection instance; no source law,
stochasticity, hidden graph budget or observed-process equivalence is assumed
proved merely by constructing these matrices. No novelty of this standard
matrix principle is claimed. Frozen100 is unchanged; this is next-version work.
-/
namespace UnifiedLean.Source.MatrixProjectionExponential
open Matrix NormedSpace
open scoped Matrix.Norms.Operator
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The ordinary block-diagonal additive map; no fitted stochastic kernel. -/
def diagonalPairHom : (Matrix m m ℝ × Matrix n n ℝ) →+
    Matrix (m ⊕ n) (m ⊕ n) ℝ where
  toFun p := fromBlocks p.1 0 0 p.2
  map_zero' := fromBlocks_zero
  map_add' p q := by simp [fromBlocks_add]

omit [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
lemma diagonalPairHom_continuous : Continuous
    (diagonalPairHom : (Matrix m m ℝ × Matrix n n ℝ) →
      Matrix (m ⊕ n) (m ⊕ n) ℝ) :=
  continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd

/-- Unequal finite block sizes are allowed. The inherited power identity and
continuous additive pushforward of the convergent exponential series suffice. -/
theorem exp_fromBlocks_diagonal (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    exp (fromBlocks A 0 0 B) = fromBlocks (exp A) 0 0 (exp B) := by
  have hA := exp_series_hasSum_exp' (𝕂 := ℚ) A
  have hB := exp_series_hasSum_exp' (𝕂 := ℚ) B
  have hs := (hA.prodMk hB).map diagonalPairHom diagonalPairHom_continuous
  change HasSum (fun k : ℕ => fromBlocks ((k.factorial⁻¹ : ℚ) • A ^ k) 0 0
    ((k.factorial⁻¹ : ℚ) • B ^ k)) (fromBlocks (exp A) 0 0 (exp B)) at hs
  have ht : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℚ) • (fromBlocks A 0 0 B) ^ k)
      (fromBlocks (exp A) 0 0 (exp B)) := by
    simpa only [fromBlocks_diagonal_pow, fromBlocks_smul, smul_zero] using hs
  rw [exp_eq_tsum_rat]
  exact ht.tsum_eq

/-- Actual rectangular generator identity transports through the exponential.
The identity A*P=P*B is an explicit hypothesis that source integration must
PROVE from the admitted original-source generator and its chosen projection. -/
theorem rectangular_exp_intertwining (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (P : Matrix m n ℝ) (h : A * P = P * B) :
    exp A * P = P * exp B := by
  let C : Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks 0 P 0 0
  let D : Matrix (m ⊕ n) (m ⊕ n) ℝ := fromBlocks A 0 0 B
  have hd : SemiconjBy C D D := by
    change C * D = D * C
    simp only [C, D, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [h]
  have he := hd.exp_right
  change C * exp D = exp D * C at he
  rw [show exp D = fromBlocks (exp A) 0 0 (exp B) from exp_fromBlocks_diagonal A B] at he
  have hp := congrArg Matrix.toBlocks₁₂ he
  simpa only [C, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
    toBlocks_fromBlocks₁₂] using hp.symm

/-- Arbitrary real duration; nonnegative durations/stochastic generators are
additional source hypotheses, not needed by this algebraic implication. -/
theorem rectangular_scaled_exp_intertwining (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (P : Matrix m n ℝ) (h : A * P = P * B) (t : ℝ) :
    exp (t • A) * P = P * exp (t • B) := by
  apply rectangular_exp_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, h]

omit [DecidableEq m] [DecidableEq n] in
/-- Two already established pulse/interval kernel identities compose in order.
This does not itself establish any natural biological pulse identity. -/
theorem rectangular_product_intertwining
    (A₁ A₂ : Matrix m m ℝ) (B₁ B₂ : Matrix n n ℝ) (P : Matrix m n ℝ)
    (h₁ : A₁ * P = P * B₁) (h₂ : A₂ * P = P * B₂) :
    (A₁ * A₂) * P = P * (B₁ * B₂) := by
  rw [Matrix.mul_assoc, h₂, ← Matrix.mul_assoc, h₁, Matrix.mul_assoc]





end UnifiedLean.Source.MatrixProjectionExponential

end FullContextModule47

section FullContextModule48




/-!
# Derived finite selected-view projection of the ACTUAL source step

Contributor: dot, 2026-10-02. The target carrier is the actual finite range of
source-valid code views. Equality of projected source step laws is DERIVED from
the concrete source generator binding. Choosing a representative defines the
projected row, and its independence of that choice is proved. No source law or
matrix-intertwining identity is an assumption field. Stochastic finite-time and
calendar/timed observation connections are later gates.
-/
namespace UnifiedLean.Source.SourceFiniteProjection
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open Matrix
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev SelectedIndex (N : RootedBinary V E X) (sample : Copy → X) (keep : Finset Copy) :=
  {v : SelectedView V E Copy // ∃ s : Code N sample, selectedView (state s) keep = v}

noncomputable def projection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : SelectedIndex N sample keep :=
  ⟨selectedView (state s) keep,⟨s,rfl⟩⟩

noncomputable instance selectedIndexFintype (N : RootedBinary V E X)
    (sample : Copy → X) (keep : Finset Copy) : Fintype (SelectedIndex N sample keep) :=
  Fintype.ofSurjective (projection N keep) (by
    intro v
    obtain ⟨s,hs⟩ := v.property
    exact ⟨s,Subtype.ext hs⟩)

noncomputable def representative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) : Code N sample :=
  Classical.choose v.property

lemma representative_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    selectedView (state (representative N keep v)) keep = v.val :=
  Classical.choose_spec v.property

lemma map_probability_real {A B : Type*} [Fintype A] (p : PMF A) (phi : A → B) (b : B) :
    ((p.map phi) b).toReal = ∑ a : A, (p a).toReal * if phi a = b then 1 else 0 := by
  classical
  rw [PMF.map_apply,tsum_fintype,ENNReal.toReal_sum (by
    intro a _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : phi a = b
  · simp only [if_pos h.symm,if_pos h,mul_one]
  · simp only [if_neg (Ne.symm h),if_neg h,ENNReal.toReal_zero,mul_zero]

noncomputable def projectedStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample) :
    PMF (SelectedIndex N sample keep) :=
  (sourceStep N r s).map (projection N keep)

lemma projectedStep_real (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample)
    (v : SelectedIndex N sample keep) :
    (projectedStep N r keep s v).toReal =
      ∑ d : Code N sample, (sourceStep N r s d).toReal *
        if selectedView (state d) keep = v.val then 1 else 0 := by
  rw [projectedStep,map_probability_real]
  apply Finset.sum_congr rfl
  intro d _
  have h : projection N keep d = v ↔ selectedView (state d) keep = v.val :=
    Subtype.ext_iff
  simp only [h]

/-- The target row is genuinely independent of all hidden representative
choices because its ACTUAL source PMF expectation factors through the view. -/
theorem projectedStep_eq_of_same_view (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s t : Code N sample)
    (h : selectedView (state s) keep = selectedView (state t) keep) :
    projectedStep N r keep s = projectedStep N r keep t := by
  apply PMF.ext
  intro v
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [projectedStep_real,projectedStep_real]
  let f : SelectedView V E Copy → ℝ := fun q => if q = v.val then 1 else 0
  change (∑ d : Code N sample, (sourceStep N r s d).toReal * f (selectedView (state d) keep)) =
    ∑ d : Code N sample, (sourceStep N r t d).toReal * f (selectedView (state d) keep)
  rw [sourceStep_selected_expectation_intrinsic,sourceStep_selected_expectation_intrinsic,h]

noncomputable def selectedStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    PMF (SelectedIndex N sample keep) :=
  projectedStep N r keep (representative N keep v)

/-- Exact whole selected-state probability law for one actual source step. -/
theorem source_step_projection_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (s : Code N sample) :
    projectedStep N r keep s = selectedStep N r keep (projection N keep s) := by
  apply projectedStep_eq_of_same_view
  exact (representative_view N keep (projection N keep s)).symm

noncomputable def sourceTransition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Matrix (Code N sample) (Code N sample) ℝ :=
  fun s t => (sourceStep N r s t).toReal

noncomputable def selectedTransition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Matrix (SelectedIndex N sample keep) (SelectedIndex N sample keep) ℝ :=
  fun s t => (selectedStep N r keep s t).toReal

noncomputable def projectionMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) : Matrix (Code N sample) (SelectedIndex N sample keep) ℝ :=
  fun s v => if projection N keep s = v then 1 else 0

/-- Concrete original-source matrix identity, derived from the actual law;
it is the missing INSTANCE for the existing conditional exponential adapter. -/
theorem actual_source_transition_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) :
    sourceTransition N (sample := sample) r * projectionMatrix N (sample := sample) keep =
      projectionMatrix N (sample := sample) keep * selectedTransition N (sample := sample) r keep := by
  ext s v
  simp only [Matrix.mul_apply,sourceTransition,selectedTransition,projectionMatrix]
  have h := congrArg (fun p : PMF (SelectedIndex N sample keep) => (p v).toReal)
    (source_step_projection_law N r keep s)
  rw [projectedStep,map_probability_real] at h
  have hleft :
      (∑ a : Code N sample, (sourceStep N r s a).toReal *
        (if projection N keep a = v then 1 else 0)) =
      (∑ a : Code N sample, (sourceStep N r s a).toReal *
        (@ite ℝ (projection N keep a = v) (Classical.propDecidable _) 1 0)) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : projection N keep a = v
    · simp only [if_pos ha]
    · simp only [if_neg ha]
  calc
    _ = _ := hleft
    _ = ((selectedStep N r keep (projection N keep s)) v).toReal := h
    _ = _ := by simp





end UnifiedLean.Source.SourceFiniteProjection

end FullContextModule48

section FullContextModule49
/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Pi

/-!
Type class for finitely enumerable types. The property is stronger
than `Fintype` in that it assigns each element a rank in a finite
enumeration.
-/

@[expose] public section


universe u v

open Finset

/-- `FinEnum α` means that `α` is finite and can be enumerated in some order,
  i.e. `α` has an explicit bijection with `Fin n` for some n. -/
class FinEnum (α : Sort*) where
  /-- `FinEnum.card` is the cardinality of the `FinEnum` -/
  card : ℕ
  /-- `FinEnum.Equiv` states that type `α` is in bijection with `Fin card`,
  the size of the `FinEnum` -/
  equiv : α ≃ Fin card
  [decEq : DecidableEq α]

attribute [instance_reducible, instance 100] FinEnum.decEq

namespace FinEnum

variable {α : Type u} {β : α → Type v}

/-- transport a `FinEnum` instance across an equivalence -/
@[instance_reducible]
def ofEquiv (α) {β} [FinEnum α] (h : β ≃ α) : FinEnum β where
  card := card α
  equiv := h.trans (equiv)
  decEq := (h.trans (equiv)).decidableEq

/-- create a `FinEnum` instance from an exhaustive list without duplicates -/
@[instance_reducible]
def ofNodupList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) (h' : List.Nodup xs) :
    FinEnum α where
  card := xs.length
  equiv :=
    ⟨fun x => ⟨xs.idxOf x, by rw [List.idxOf_lt_length_iff]; apply h⟩, xs.get, fun x => by simp,
      fun i => by ext; simp [h'.idxOf_getElem]⟩

/-- create a `FinEnum` instance from an exhaustive list; duplicates are removed -/
@[instance_reducible]
def ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) : FinEnum α :=
  ofNodupList xs.dedup (by simp [*]) (List.nodup_dedup _)

lemma card_ofList [DecidableEq α] (xs : List α) (h : ∀ x : α, x ∈ xs) :
    (FinEnum.ofList xs h).card = xs.dedup.length := rfl

/-- create an exhaustive list of the values of a given type -/
def toList (α) [FinEnum α] : List α :=
  (List.finRange (card α)).map equiv.symm

open Function

@[simp]
theorem mem_toList [FinEnum α] (x : α) : x ∈ toList α := by
  simp only [toList, List.mem_map, List.mem_finRange, true_and]; exists equiv x; simp

@[simp]
theorem nodup_toList [FinEnum α] : List.Nodup (toList α) := by
  simp only [toList]; apply List.Nodup.map <;> [apply Equiv.injective; apply List.nodup_finRange]

/-- create a `FinEnum` instance using a surjection -/
@[instance_reducible]
def ofSurjective {β} (f : β → α) [DecidableEq α] [FinEnum β] (h : Surjective f) : FinEnum α :=
  ofList ((toList β).map f) (by intro; simpa using h _)

/-- create a `FinEnum` instance using an injection -/
@[instance_reducible]
noncomputable def ofInjective {α β} (f : α → β) [DecidableEq α] [FinEnum β] (h : Injective f) :
    FinEnum α :=
  ofList ((toList β).filterMap (partialInv f))
    (by
      intro x
      simp only [mem_toList, true_and, List.mem_filterMap]
      use f x
      simp only [h, Function.partialInv_left])

instance _root_.ULift.instFinEnum [FinEnum α] : FinEnum (ULift α) :=
  ⟨card α, Equiv.ulift.trans equiv⟩

@[simp]
theorem card_ulift [FinEnum (ULift α)] [FinEnum α] : card (ULift α) = card α :=
  Fin.equiv_iff_eq.mp ⟨equiv.symm.trans Equiv.ulift |>.trans equiv⟩

section ULift
variable [FinEnum α] (a : α) (a' : ULift α) (i : Fin (card α))

@[simp] lemma equiv_up : equiv (ULift.up a) = equiv a := rfl
@[simp] lemma equiv_down : equiv a'.down = equiv a' := rfl
@[simp] lemma up_equiv_symm : ULift.up (equiv.symm i) = (equiv (α := ULift α)).symm i := rfl
@[simp] lemma down_equiv_symm : ((equiv (α := ULift α)).symm i).down = equiv.symm i := rfl

end ULift

instance pempty : FinEnum PEmpty :=
  ofList [] fun x => PEmpty.elim x

@[simp] lemma card_pempty : FinEnum.card PEmpty = 0 := rfl

instance empty : FinEnum Empty :=
  ofList [] fun x => Empty.elim x

@[simp] lemma card_empty : FinEnum.card Empty = 0 := rfl

instance punit : FinEnum PUnit :=
  ofList [PUnit.unit] fun x => by simp

@[simp] lemma card_punit : FinEnum.card PUnit = 1 := rfl

instance prod {β} [FinEnum α] [FinEnum β] : FinEnum (α × β) :=
  ofList (toList α ×ˢ toList β) fun x => by cases x; simp

instance sum {β} [FinEnum α] [FinEnum β] : FinEnum (α ⊕ β) :=
  ofList ((toList α).map Sum.inl ++ (toList β).map Sum.inr) fun x => by cases x <;> simp

instance fin {n} : FinEnum (Fin n) :=
  ofList (List.finRange _) (by simp)

@[simp]
theorem card_fin {n} [FinEnum (Fin n)] : card (Fin n) = n := Fin.equiv_iff_eq.mp ⟨equiv.symm⟩

instance Quotient.enum [FinEnum α] (s : Setoid α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    FinEnum (Quotient s) :=
  FinEnum.ofSurjective Quotient.mk'' fun x => Quotient.inductionOn x fun x => ⟨x, rfl⟩

/-- enumerate all finite sets of a given type -/
def Finset.enum [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | x :: xs => do
    let r ← Finset.enum xs
    [r, insert x r]

@[simp, grind =]
theorem Finset.mem_enum [DecidableEq α] (s : Finset α) (xs : List α) :
    s ∈ Finset.enum xs ↔ ∀ x ∈ s, x ∈ xs := by
  induction xs generalizing s with
  | nil => simp [enum, eq_empty_iff_forall_notMem]
  | cons x xs ih =>
      simp only [enum, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
        List.not_mem_nil, or_false, ih]
      refine ⟨by aesop, fun hs => ⟨s.erase x, ?_⟩⟩
      simp only [or_iff_not_imp_left] at hs
      simp +contextual [eq_comm (a := s), or_iff_not_imp_left, hs]

instance Finset.finEnum [FinEnum α] : FinEnum (Finset α) :=
  ofList (Finset.enum (toList α)) (by simp)

instance Subtype.finEnum [FinEnum α] (p : α → Prop) [DecidablePred p] : FinEnum { x // p x } :=
  ofList ((toList α).filterMap fun x => if h : p x then some ⟨_, h⟩ else none)
    (by rintro ⟨x, h⟩; simpa)

instance (β : α → Type v) [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Sigma β) :=
  ofList ((toList α).flatMap fun a => (toList (β a)).map <| Sigma.mk a)
    (by intro x; cases x; simp)

instance PSigma.finEnum [FinEnum α] [∀ a, FinEnum (β a)] : FinEnum (Σ' a, β a) :=
  FinEnum.ofEquiv _ (Equiv.psigmaEquivSigma _)

instance PSigma.finEnumPropLeft {α : Prop} {β : α → Type v} [∀ a, FinEnum (β a)] [Decidable α] :
    FinEnum (Σ' a, β a) :=
  if h : α then ofList ((toList (β h)).map <| PSigma.mk h) fun ⟨a, Ba⟩ => by simp
  else ofList [] fun ⟨a, _⟩ => (h a).elim

instance PSigma.finEnumPropRight {β : α → Prop} [FinEnum α] [∀ a, Decidable (β a)] :
    FinEnum (Σ' a, β a) :=
  FinEnum.ofEquiv { a // β a }
    ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨_, _⟩ => rfl, fun ⟨_, _⟩ => rfl⟩

instance PSigma.finEnumPropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] :
    FinEnum (Σ' a, β a) :=
  if h : ∃ a, β a then ofList [⟨h.fst, h.snd⟩] (by simp)
  else ofList [] fun a => (h ⟨a.fst, a.snd⟩).elim

instance [DecidableEq α] (xs : List α) : FinEnum { x : α // x ∈ xs } := ofList xs.attach (by simp)

instance (priority := 100) [FinEnum α] : Fintype α where
  elems := univ.map equiv.symm.toEmbedding
  complete := by intros; simp

/-- The enumeration merely adds an ordering, leaving the cardinality as is. -/
theorem card_eq_fintypeCard {α : Type u} [FinEnum α] [Fintype α] : card α = Fintype.card α :=
  Fintype.truncEquivFin α |>.inductionOn (fun h ↦ Fin.equiv_iff_eq.mp ⟨equiv.symm.trans h⟩)

/-- Any two enumerations of the same type have the same length. -/
theorem card_unique {α : Type u} (e₁ e₂ : FinEnum α) : e₁.card = e₂.card :=
  calc _
  _ = _ := @card_eq_fintypeCard _ e₁ inferInstance
  _ = _ := Fintype.card_congr' rfl
  _ = _ := @card_eq_fintypeCard _ e₂ inferInstance |>.symm

/-- A type indexable by `Fin 0` is empty and vice versa. -/
theorem card_eq_zero_iff {α : Type u} [FinEnum α] : card α = 0 ↔ IsEmpty α :=
  Eq.congr_left card_eq_fintypeCard |>.trans Fintype.card_eq_zero_iff

/-- Any enumeration of an empty type has length 0. -/
theorem card_eq_zero {α : Type u} [FinEnum α] [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.mpr ‹_›

/-- A type indexable by `Fin n` with positive `n` is inhabited and vice versa. -/
theorem card_pos_iff {α : Type u} [FinEnum α] : 0 < card α ↔ Nonempty α :=
  card_eq_fintypeCard (α := α) ▸ Fintype.card_pos_iff

/-- Any non-empty enumeration has more than one element. -/
lemma card_pos {α : Type*} [FinEnum α] [Nonempty α] : 0 < card α :=
  card_pos_iff.mpr ‹_›

/-- No non-empty enumeration has 0 elements. -/
lemma card_ne_zero {α : Type*} [FinEnum α] [Nonempty α] : card α ≠ 0 := card_pos.ne'

/-- Any enumeration of a type with unique inhabitant has length 1. -/
theorem card_eq_one (α : Type u) [FinEnum α] [Unique α] : card α = 1 :=
  card_eq_fintypeCard.trans <| Fintype.card_eq_one_iff_nonempty_unique.mpr ⟨‹_›⟩

instance [IsEmpty α] : Unique (FinEnum α) where
  default := ⟨0, Equiv.equivOfIsEmpty α (Fin 0)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_zero
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
      exact congrArg (α ≃ Fin ·) <| card_eq_zero
    · funext x
      exact ‹IsEmpty α›.elim x

/-- An empty type has a trivial enumeration. Not registered as an instance, to make sure that there
aren't two definitionally differing instances around. -/
@[instance_reducible]
def ofIsEmpty [IsEmpty α] : FinEnum α := default

instance [Unique α] : Unique (FinEnum α) where
  default := ⟨1, Equiv.ofUnique α (Fin 1)⟩
  uniq e := by
    change FinEnum.mk e.1 e.2 = _
    congr 1
    · exact card_eq_one α
    · refine heq_of_cast_eq ?_ (Subsingleton.allEq _ _)
      exact congrArg (α ≃ Fin ·) <| card_eq_one α
    · subsingleton

/-- A type with unique inhabitant has a trivial enumeration. Not registered as an instance, to make
sure that there aren't two definitionally differing instances around. -/
@[instance_reducible]
def ofUnique [Unique α] : FinEnum α := default

instance : FinEnum UInt8 where
  card := 2 ^ 8
  equiv := ⟨UInt8.toFin, UInt8.ofFin, by intro x; simp, by intro x; simp⟩

instance : FinEnum UInt16 where
  card := 2 ^ 16
  equiv := ⟨UInt16.toFin, UInt16.ofFin, by intro x; simp, by intro x; simp⟩

instance : FinEnum UInt32 where
  card := 2 ^ 32
  equiv := ⟨UInt32.toFin, UInt32.ofFin, by intro x; simp, by intro x; simp⟩

instance : FinEnum UInt64 where
  card := 2 ^ 64
  equiv := ⟨UInt64.toFin, UInt64.ofFin, by intro x; simp, by intro x; simp⟩

instance : FinEnum Int8 where
  card := 2 ^ 8
  equiv := ⟨BitVec.toFin ∘ Int8.toBitVec, Int8.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

instance : FinEnum Int16 where
  card := 2 ^ 16
  equiv := ⟨BitVec.toFin ∘ Int16.toBitVec, Int16.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

instance : FinEnum Int32 where
  card := 2 ^ 32
  equiv := ⟨BitVec.toFin ∘ Int32.toBitVec, Int32.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

instance : FinEnum Int64 where
  card := 2 ^ 64
  equiv := ⟨BitVec.toFin ∘ Int64.toBitVec, Int64.ofBitVec ∘ BitVec.ofFin,
    by intro x; simp, by intro x; simp⟩

instance (n : ℕ) : FinEnum (BitVec n) where
  card := 2 ^ n
  equiv := ⟨BitVec.toFin, BitVec.ofFin, by intro x; simp, by intro x; simp⟩

@[simp, grind =] lemma card_UInt8 : card UInt8 = 2 ^ 8 := rfl
@[simp, grind =] lemma card_UInt16 : card UInt16 = 2 ^ 16 := rfl
@[simp, grind =] lemma card_UInt32 : card UInt32 = 2 ^ 32 := rfl
@[simp, grind =] lemma card_UInt64 : card UInt64 = 2 ^ 64 := rfl
@[simp, grind =] lemma card_Int8 : card Int8 = 2 ^ 8 := rfl
@[simp, grind =] lemma card_Int16 : card Int16 = 2 ^ 16 := rfl
@[simp, grind =] lemma card_Int32 : card Int32 = 2 ^ 32 := rfl
@[simp, grind =] lemma card_Int64 : card Int64 = 2 ^ 64 := rfl
@[simp, grind =] lemma card_bitVec (n : ℕ) : card (BitVec n) = 2 ^ n := rfl

end FinEnum

namespace List
variable {α : Type*} [FinEnum α] {β : α → Type*} [∀ a, FinEnum (β a)]
open FinEnum

theorem mem_pi_toList (xs : List α)
    (f : ∀ a, a ∈ xs → β a) : f ∈ pi xs fun x => toList (β x) :=
  (mem_pi _ _).mpr fun _ _ ↦ mem_toList _

/-- enumerate all functions whose domain and range are finitely enumerable -/
def Pi.enum (β : α → Type*) [∀ a, FinEnum (β a)] : List (∀ a, β a) :=
  (pi (toList α) fun x => toList (β x)).map (fun f x => f x (mem_toList _))

theorem Pi.mem_enum (f : ∀ a, β a) :
    f ∈ Pi.enum β := by simpa [Pi.enum] using ⟨fun a _ => f a, mem_pi_toList _ _, rfl⟩

instance Pi.finEnum : FinEnum (∀ a, β a) :=
  ofList (Pi.enum _) fun _ => Pi.mem_enum _

instance pfunFinEnum (p : Prop) [Decidable p] (α : p → Type) [∀ hp, FinEnum (α hp)] :
    FinEnum (∀ hp : p, α hp) :=
  if hp : p then
    ofList ((toList (α hp)).map fun x _ => x) (by intro x; simpa using ⟨x hp, rfl⟩)
  else ofList [fun hp' => (hp hp').elim] (by simp [funext_iff, hp])

end List

end FullContextModule49

section FullContextModule50




/-!
Executable enumeration of the actual finite original-source snapshots and
full selected views. Contributor: dot, 2026-10-10, continuing the accepted
G7 compiler formalization and the existing finite genealogy encoding.

The input carriers have explicit FinEnum instances; the numbered original
Fin carriers supply these without a source-size assumption. Tree enumeration
uses the proved original-copy height cap. Source validity is decided from
finite forest predicates and the proved vertex-count reachability algorithm.
No validity oracle, arbitrary finite-state replacement, or choice of a source
representative is an input. This is the executable state/index layer for the
population-split coefficient compiler, not its complete coefficient theorem.
-/
namespace GProgram.G7.EffectiveSourceEnumeration
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteGenealogyEncoding UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

instance boolEnumeration : FinEnum Bool :=
  FinEnum.ofList [false, true] (by intro b; cases b <;> simp)

instance optionEnumeration {A : Type*} [FinEnum A] : FinEnum (Option A) :=
  FinEnum.ofList (none :: (FinEnum.toList A).map some) (by
    intro a; cases a <;> simp)

instance treeCodeEnumeration : (n : Nat) → FinEnum (TreeCode Copy n)
  | 0 => inferInstanceAs (FinEnum Copy)
  | n+1 => by
      letI := treeCodeEnumeration n
      exact inferInstanceAs (FinEnum (Copy ⊕ (TreeCode Copy n × TreeCode Copy n)))

instance wellLabelledDecidable : (t : Genealogy Copy) → Decidable t.WellLabelled
  | .leaf _ => isTrue trivial
  | .graft a b => by
      letI := wellLabelledDecidable a
      letI := wellLabelledDecidable b
      exact inferInstanceAs (Decidable (a.WellLabelled ∧ b.WellLabelled ∧
        Disjoint a.leaves b.leaves))

abbrev AdmissibleTreeCode (Copy : Type*) [DecidableEq Copy] [Fintype Copy] :=
  {c : TreeCode Copy (Fintype.card Copy) // (decodeTree _ c).WellLabelled}

def decodeAdmissibleTree (c : AdmissibleTreeCode Copy) : WellLabelledTree Copy :=
  ⟨decodeTree _ c.val, c.property⟩

theorem decodeAdmissibleTree_surjective :
    Function.Surjective (decodeAdmissibleTree (Copy := Copy)) := by
  intro t
  let h := (wellLabelled_height_below_copy_cap t.val t.property).le
  let c := encodeTree (Fintype.card Copy) t.val h
  have hc : (decodeTree (Fintype.card Copy) c).WellLabelled := by
    simpa only [c, decode_encode] using t.property
  exact ⟨⟨c,hc⟩, Subtype.ext (decode_encode _ _ _)⟩

/-- Exhaustive, deduplicated bounded-code enumeration of the existing trees. -/
instance treeEnumeration : FinEnum (WellLabelledTree Copy) :=
  FinEnum.ofSurjective decodeAdmissibleTree decodeAdmissibleTree_surjective

instance locationEnumeration : FinEnum (Location V E) :=
  FinEnum.ofEquiv (V ⊕ (E ⊕ V)) locationEquiv

def snapshotEncoding : Snapshot V E Copy ≃
    (Finset Copy × (Copy → Copy) × (Copy → Option (WellLabelledTree Copy)) ×
      (Copy → Option (Location V E)) × (V → Bool)) where
  toFun s := (s.live,s.ancestor,s.genealogy,s.population,s.register)
  invFun s := ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equality is fieldwise; it does not search the large snapshot enumeration. -/
instance snapshotDecidableEq : DecidableEq (Snapshot V E Copy) := fun a b =>
  decidable_of_iff (a.live = b.live ∧ a.ancestor = b.ancestor ∧
    a.genealogy = b.genealogy ∧ a.population = b.population ∧ a.register = b.register)
    ⟨fun h => Snapshot.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2,
     fun h => by cases h; exact ⟨rfl,rfl,rfl,rfl,rfl⟩⟩

instance snapshotEnumeration : FinEnum (Snapshot V E Copy) :=
  FinEnum.ofEquiv _ snapshotEncoding

/-- Same inherited decoder, with an executable body rather than a
noncomputable declaration marker. -/
def decode (root : V) (s : Snapshot V E Copy) : State V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := match s.genealogy l with
    | some t => t.val
    | none => .leaf l
  location l := match s.population l with
    | some p => p
    | none => .node root
  register := s.register
  history := []

theorem decode_eq (root : V) (s : Snapshot V E Copy) :
    decode root s = decodeSnapshot root s := rfl

def forestValidDecidable (s : State V E Copy) : Decidable (Valid s) :=
  decidable_of_iff
    ((∀ x, s.ancestor x ∈ s.live) ∧
     (∀ l ∈ s.live, s.ancestor l = l) ∧
     (∀ l ∈ s.live, ∀ x, x ∈ (s.genealogy l).leaves ↔ s.ancestor x = l) ∧
     (∀ l ∈ s.live, (s.genealogy l).WellLabelled))
    ⟨fun h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2⟩,
     fun h => ⟨h.ancestor_live,h.representative,h.leaf_fiber,h.wellLabelled⟩⟩

def directedReachDecidable (G : EdgeGraph V E) (a b : V) : Decidable (G.DReach a b) := by
  letI : DecidableRel G.DStep := fun x y =>
    inferInstanceAs (Decidable (∃ e, G.source e = x ∧ G.target e = y))
  exact GProgram.G7.FiniteReachability.decideReach G.DStep a b

def descendsDecidable (N : RootedBinary V E X) (p : Location V E) (x : X) :
    Decidable (DescendsTo N p x) := by
  letI : DecidableRel N.graph.DReach := directedReachDecidable N.graph
  cases p with
  | node v => exact inferInstanceAs (Decidable (N.graph.DReach v (N.leaf x)))
  | edge e => exact inferInstanceAs
      (Decidable (N.graph.DReach (N.graph.target e) (N.leaf x)))
  | rootPopulation r => exact inferInstanceAs
      (Decidable (r = N.root ∧ N.graph.DReach r (N.leaf x)))

def sourceValidDecidable (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) : Decidable (SourceValid N sample s) := by
  letI := forestValidDecidable s
  letI : DecidablePred (fun x => DescendsTo N (copyLocation s x) (sample x)) :=
    fun x => descendsDecidable N (copyLocation s x) (sample x)
  exact decidable_of_iff
    (Valid s ∧ ∀ x, DescendsTo N (copyLocation s x) (sample x))
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.forest,h.original_descendant⟩⟩

/-- The original admitted snapshot subtype is enumerated, with its exact
SourceValid predicate decided by the explicit bounded graph algorithm. -/
instance codeEnumeration (N : RootedBinary V E X) (sample : Copy → X) :
    FinEnum (Code N sample) := by
  letI : DecidablePred (fun s : Snapshot V E Copy =>
      SourceValid N sample (decodeSnapshot N.root s)) :=
    fun s => sourceValidDecidable N sample (decode N.root s)
  exact inferInstanceAs (FinEnum {s : Snapshot V E Copy //
    SourceValid N sample (decodeSnapshot N.root s)})

def view (root : V) (s : Snapshot V E Copy) (keep : Finset Copy) :
    SelectedView V E Copy where
  genealogy x := if x ∈ keep then ((decode root s).genealogy (s.ancestor x)).prune keep
    else none
  population x := if x ∈ keep then some (copyLocation (decode root s) x) else none
  register := s.register

theorem view_eq (root : V) (s : Snapshot V E Copy) (keep : Finset Copy) :
    view root s keep = selectedView (decodeSnapshot root s) keep := rfl

instance viewDecidableEq : DecidableEq (SelectedView V E Copy) := fun a b =>
  decidable_of_iff (a.genealogy = b.genealogy ∧ a.population = b.population ∧
    a.register = b.register)
    ⟨fun h => SelectedView.ext h.1 h.2.1 h.2.2,
     fun h => by cases h; exact ⟨rfl,rfl,rfl⟩⟩

def project (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (s : Code N sample) : SelectedIndex N sample keep :=
  ⟨view N.root s.val keep, ⟨s,rfl⟩⟩

instance selectedEnumeration (N : RootedBinary V E X) (sample : Copy → X)
    (keep : Finset Copy) : FinEnum (SelectedIndex N sample keep) :=
  FinEnum.ofSurjective (project N keep) (by
    intro v
    obtain ⟨s,hs⟩ := v.property
    exact ⟨s,Subtype.ext hs⟩)

/-- Finite existential search uses the executable enumeration rather than
the legacy noncomputable Fintype instance for source snapshots. -/
def enumeratedExistsDecidable {A : Type*} [FinEnum A] (p : A → Prop)
    [DecidablePred p] : Decidable (∃ a, p a) :=
  decidable_of_iff (∃ a ∈ FinEnum.toList A, p a)
    ⟨fun ⟨a,_,h⟩ => ⟨a,h⟩,fun ⟨a,h⟩ => ⟨a,FinEnum.mem_toList a,h⟩⟩

/-- List.choose performs the first successful finite test. Its proof argument
only certifies that the explicit exhaustive search cannot fail. -/
def findRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) : Code N sample :=
  List.choose (fun s => view N.root s.val keep = v.val)
    (FinEnum.toList (Code N sample)) (by
      obtain ⟨s,hs⟩ := v.property
      exact ⟨s,FinEnum.mem_toList s,hs⟩)

theorem findRepresentative_view (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    selectedView (state (findRepresentative N keep v)) keep = v.val := by
  rw [state, ← view_eq]
  unfold findRepresentative
  exact List.choose_property
    (fun s : Code N sample => view N.root s.val keep = v.val)
    (FinEnum.toList (Code N sample)) (by
      obtain ⟨s,hs⟩ := v.property
      exact ⟨s,FinEnum.mem_toList s,hs⟩)

theorem project_findRepresentative (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (v : SelectedIndex N sample keep) :
    projection N keep (findRepresentative N keep v) = v :=
  Subtype.ext (findRepresentative_view N keep v)

end GProgram.G7.EffectiveSourceEnumeration

end FullContextModule50

section FullContextModule51



/-!
# Constructed source finite-time Poisson-mixture kernel and selected transport

Contributor: dot, 2026-10-02. Iterates the actual normalized original-source
step and mixes with the library Poisson count at the derived positive global
rate. The resulting PMF is a genuine finite-time kernel construction, and its
selected internal-state transport is proved from the actual one-step law.
Identification with source exponential holding times, semigroup/clock-rate
independence, calendar-compatible initialization/agenda, timed-path observation
and the unranked quotient remain explicit gates before full original-law claims.
-/
namespace UnifiedLean.Source.SourcePoissonKernel
open Nanuq.Source ProbabilityTheory
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sourceIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Nat → Code N sample → PMF (Code N sample)
  | 0,s => PMF.pure s
  | k+1,s => (sourceStep N r s).bind (sourceIteration N r k)

noncomputable def selectedIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Nat → SelectedIndex N sample keep → PMF (SelectedIndex N sample keep)
  | 0,s => PMF.pure s
  | k+1,s => (selectedStep N r keep s).bind (selectedIteration N r keep k)

/-- All finite iterations of the ACTUAL source PMF preserve the same selected
whole-state law, not just one scalar or an assumed transition matrix identity. -/
theorem source_iteration_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (k : Nat) (s : Code N sample) :
    (sourceIteration N r k s).map (projection N keep) =
      selectedIteration N r keep k (projection N keep s) := by
  induction k generalizing s with
  | zero => simp [sourceIteration,selectedIteration,PMF.pure_map]
  | succ k ih =>
      rw [sourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (sourceStep N r s).bind (selectedIteration N r keep k ∘ projection N keep) = _
      rw [← PMF.bind_map]
      change (projectedStep N r keep s).bind (selectedIteration N r keep k) = _
      rw [source_step_projection_law]
      rfl

noncomputable def globalClockRate (r : PositivePairRates E) : ℝ≥0 :=
  ⟨globalRateBound (Copy := Copy) r,(globalRateBound_positive (Copy := Copy) r).le⟩

noncomputable def countPMF (rate : ℝ≥0) : PMF Nat := (poissonMeasure rate).toPMF

noncomputable def sourceTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) : PMF (Code N sample) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind
    (fun k => sourceIteration N r k s)

noncomputable def selectedTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ≥0)
    (s : SelectedIndex N sample keep) : PMF (SelectedIndex N sample keep) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind
    (fun k => selectedIteration N r keep k s)

/-- Genuine normalized Poisson/source-step mixture, with exact selected-state
law. No phenotype readout, time-compatible source epoch or observed-law equality
is supplied as a premise hidden in this construction. -/
theorem constructed_source_time_kernel_projection (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (projection N keep) =
      selectedTimeKernel N r keep t (projection N keep s) := by
  rw [sourceTimeKernel,selectedTimeKernel,PMF.map_bind]
  simp_rw [source_iteration_projection]



end UnifiedLean.Source.SourcePoissonKernel

end FullContextModule51

section FullContextModule52


/-!
# Actual source generator/projection instance through matrix exponentials

Contributor: dot, 2026-10-02. The source matrices are built from the normalized
ORIGINAL source PMF, its copy/rate-derived uniformization constant and the
proved finite selected-view projection. Generator intertwining is derived,
then the prior rectangular exponential adapter is instantiated. This is exact
finite-time ALGEBRA; identifying these exponentials as the full calendar-driven
biological law and timed observer requires stochastic/source temporal binding.
-/
namespace UnifiedLean.Source.SourceGeneratorExponential
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.MatrixProjectionExponential
open Matrix NormedSpace
open scoped Classical Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def sourceGeneratorMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Matrix (Code N sample) (Code N sample) ℝ :=
  globalRateBound (Copy := Copy) r • (sourceTransition N (sample := sample) r - 1)

noncomputable def selectedGeneratorMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    Matrix (SelectedIndex N sample keep) (SelectedIndex N sample keep) ℝ :=
  globalRateBound (Copy := Copy) r • (selectedTransition N (sample := sample) r keep - 1)

/-- The required source instance is proved from its actual transition law;
there is no generator/projection equation field in the source input. -/
theorem actual_source_generator_matrix_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) :
    sourceGeneratorMatrix N (sample := sample) r * projectionMatrix N (sample := sample) keep =
      projectionMatrix N (sample := sample) keep * selectedGeneratorMatrix N (sample := sample) r keep := by
  unfold sourceGeneratorMatrix selectedGeneratorMatrix
  rw [Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  rw [Matrix.sub_mul,Matrix.mul_sub,Matrix.one_mul,Matrix.mul_one,
    actual_source_transition_intertwining N r keep]

/-- Actual-source rectangular finite-time algebra, not an assumed source
semigroup identity. Nonnegative durations/stochasticity and calendar epochs
are further explicit source gates; the algebra itself holds for every realt. -/
theorem actual_source_exponential_projection (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (t : ℝ) :
    exp (t • sourceGeneratorMatrix N (sample := sample) r) * projectionMatrix N (sample := sample) keep =
      projectionMatrix N (sample := sample) keep * exp (t • selectedGeneratorMatrix N (sample := sample) r keep) :=
  rectangular_scaled_exp_intertwining _ _ _
    (actual_source_generator_matrix_intertwining N r keep) t



end UnifiedLean.Source.SourceGeneratorExponential

end FullContextModule52

section FullContextModule53



/-!
# Actual source Poisson kernel equals its generator exponential

Contributor: dot, 2026-10-02. This connects the two constructed finite-time
objects: the genuine PMF obtained from original source steps and Poisson counts,
and the original-generator matrix exponential. Positivity/normalization follow
from the PMF, rather than being assumed for the exponential. Calendar-compatible
initialization, the physical exponential-clock path law, timed observations and
unranked genealogy quotient remain the original temporal source assembly gate.
-/
namespace UnifiedLean.Source.SourcePoissonExponential
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source ProbabilityTheory MeasureTheory Matrix NormedSpace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma bind_probability_real {A B : Type*} (p : PMF A) (f : A → PMF B) (b : B) :
    ((p.bind f) b).toReal = ∑' a, (p a).toReal * (f a b).toReal := by
  rw [PMF.bind_apply,ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (f a) b))]
  simp only [ENNReal.toReal_mul]

lemma source_iteration_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s d : Code N sample) :
    (sourceIteration N r k s d).toReal = (sourceTransition N r ^ k) s d := by
  induction k generalizing s with
  | zero =>
      simp only [sourceIteration,pow_zero,PMF.pure_apply,Matrix.one_apply]
      by_cases h : d = s
      · simp [h]
      · simp [h,Ne.symm h]
  | succ k ih =>
      rw [sourceIteration,bind_probability_real,tsum_fintype,pow_succ',Matrix.mul_apply]
      simp_rw [ih]
      rfl

lemma countPMF_real (rate : ℝ≥0) (k : Nat) :
    (countPMF rate k).toReal = Real.exp (-(rate : ℝ)) * (rate : ℝ)^k / k.factorial := by
  rw [countPMF,Measure.toPMF_apply,poissonMeasure_singleton,ENNReal.toReal_ofReal (by positivity)]

/-- Standard exponential-series identity instantiated later at the ACTUAL
source transition matrix. Neither stochasticity nor any desired source row
identity is a premise of this algebraic calculation. -/
lemma poisson_matrix_entry {I : Type*} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℝ) (a : ℝ) (s d : I) :
    (∑' k : Nat, (Real.exp (-a) * a^k / k.factorial) * (K^k) s d) =
      (exp (a • (K-1))) s d := by
  let entry : Matrix I I ℝ →+ ℝ :=
    {toFun := fun M => M s d, map_zero' := rfl, map_add' := by intros; rfl}
  have he := (exp_series_hasSum_exp' (𝕂 := ℝ) (a • K)).map entry (by
    change Continuous (fun M : Matrix I I ℝ => M s d)
    fun_prop)
  change HasSum (fun k : Nat => (((k.factorial : ℝ)⁻¹) • (a • K)^k) s d)
    ((exp (a • K)) s d) at he
  have hh : HasSum (fun k : Nat => (Real.exp (-a) * a^k / k.factorial) * (K^k) s d)
      (Real.exp (-a) * (exp (a • K)) s d) := by
    simpa only [Function.comp_apply,entry,AddMonoidHom.coe_mk,smul_pow,
      Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      using he.mul_left (Real.exp (-a))
  have hscalar : exp ((-a) • (1 : Matrix I I ℝ)) = Real.exp (-a) • (1 : Matrix I I ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one,← Real.exp_eq_exp_ℝ] using
      (algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix I I ℝ) (-a)).symm
  have hcomm : Commute ((-a) • (1 : Matrix I I ℝ)) (a • K) :=
    (Commute.one_left K).smul_left (-a) |>.smul_right a
  have hsum : a • (K-1) = (-a) • (1 : Matrix I I ℝ) + a • K := by
    simp only [smul_sub,neg_smul]
    abel
  rw [hh.tsum_eq,hsum,exp_add_of_commute hcomm,hscalar,Matrix.smul_mul,Matrix.one_mul]
  rfl

/-- Equality of the GENUINE normalized original-source finite-time PMF and
its proved original-generator exponential, for every nonnegative duration. -/
theorem source_time_kernel_eq_exponential (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample) :
    (sourceTimeKernel N r t s d).toReal =
      (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d := by
  rw [sourceTimeKernel,bind_probability_real]
  simp_rw [countPMF_real,source_iteration_probability]
  rw [poisson_matrix_entry]
  apply congrArg (fun M : Matrix (Code N sample) (Code N sample) ℝ => (exp M) s d)
  simp only [sourceGeneratorMatrix,smul_smul,NNReal.coe_mul]
  congr 1
  change globalRateBound (Copy := Copy) r * (t : ℝ) = (t : ℝ) * globalRateBound (Copy := Copy) r
  exact mul_comm _ _





end UnifiedLean.Source.SourcePoissonExponential

end FullContextModule53

section FullContextModule54


/-!
# Actual finite-source stochastic epoch semigroup

Contributor: dot, 2026-10-02. The constructed original-source PMF is a genuine
continuous-time transition semigroup on its fixed finite admitted carrier.
Identity and temporal composition are proved via its already-derived generator
exponential. Positivity/row normalization of that exponential are consequences
of the actual PMF. This is an epoch law; the finite original calendar agenda,
exponential holding-clock path binding and timed/unranked readout still require
source assembly, and no copied target equation is supplied as input.
-/
namespace UnifiedLean.Source.SourceEpochSemigroup
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source Matrix NormedSpace
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma pmf_sum_real {A : Type*} [Fintype A] (p : PMF A) : ∑ a : A, (p a).toReal = 1 := by
  have h : (∑ a : A, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)] at hr
  simpa only [ENNReal.toReal_one] using hr

/-- Normalization is inherited from a constructed probability distribution;
it is not assumed as a matrix or source contract field. -/
theorem actual_source_exponential_stochastic (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) :
    (∀ s d : Code N sample, 0 ≤ (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d) ∧
      (∀ s : Code N sample, (∑ d : Code N sample,
        (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d) = 1) := by
  constructor
  · intro s d
    rw [← source_time_kernel_eq_exponential]
    exact ENNReal.toReal_nonneg
  · intro s
    simp_rw [← source_time_kernel_eq_exponential]
    exact pmf_sum_real _

/-- The source kernel starts at the actual supplied admitted state. -/
theorem actual_source_time_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : sourceTimeKernel N r 0 s = PMF.pure s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [source_time_kernel_eq_exponential]
  simp only [NNReal.coe_zero,zero_smul,exp_zero,Matrix.one_apply,PMF.pure_apply]
  by_cases h : d = s
  · simp [h]
  · simp [h,Ne.symm h]

/-- Full admitted-state Chapman--Kolmogorov law of the ORIGINAL source
kernel, derived from its actual PMF/generator instance. -/
theorem actual_source_time_add (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t u : ℝ≥0) (s : Code N sample) :
    sourceTimeKernel N r (t+u) s =
      (sourceTimeKernel N r t s).bind (fun d => sourceTimeKernel N r u d) := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,tsum_fintype]
  simp_rw [source_time_kernel_eq_exponential]
  change (exp (((t+u : ℝ≥0) : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d =
    (exp ((t : ℝ) • sourceGeneratorMatrix N (sample := sample) r) *
      exp ((u : ℝ) • sourceGeneratorMatrix N (sample := sample) r)) s d
  rw [NNReal.coe_add,add_smul,NormedSpace.exp_add_of_commute
    ((Commute.refl (sourceGeneratorMatrix N (sample := sample) r)).smul_left (t : ℝ)
      |>.smul_right (u : ℝ))]




end UnifiedLean.Source.SourceEpochSemigroup

end FullContextModule54

section FullContextModule55



/-!
# Calendar-compatible ORIGINAL source epoch locations

Contributor: dot, 2026-10-02. The inherited SourceValid invariant is spatial;
this module adds the actual temporal invariant needed for physical epoch
assembly, and derives its preservation under actual merger/finite-code steps.
Future sampled tip nodes may be dormant until their original node age. Original
edge IDs and the actual ancestral root are retained. The initialized full
vertex agenda and clock/path identification are subsequent source obligations.
-/
namespace UnifiedLean.Source.SourceCalendarCompatibility
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Compatibility on a whole half-open epoch [a,b). Node locations are
unactivated future samples; no merger occurs at a node. -/
def LocationInEpoch (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) : Location V E → Prop
  | .node v => b ≤ C.age v
  | .edge e => C.age (N.graph.target e) ≤ a ∧ b ≤ C.age (N.graph.source e)
  | .rootPopulation v => v = N.root ∧ C.age N.root ≤ a

def EpochCompatible (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) (s : State V E Copy) : Prop :=
  ∀ x : Copy, LocationInEpoch N C a b (copyLocation s x)

/-- An admitted original edge occupied during this epoch is physically active
at every strictly interior time, using the original older-side convention. -/
theorem epoch_edge_active (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b t : ℝ} {s : State V E Copy} (hs : EpochCompatible N C a b s)
    {x : Copy} {e : E} (hx : copyLocation s x = .edge e)
    (ha : a ≤ t) (hb : t < b) : C.Active t e := by
  have hh := hs x
  rw [hx] at hh
  exact ⟨hh.1.trans ha,hb.trans_le hh.2⟩

/-- SourceValid's root identity is inherited, not an extra guard invented here.
The temporal part is supplied by the actual epoch locations. -/
theorem epoch_merge_compatible (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {s : State V E Copy} (hs : EpochCompatible N C a b s)
    {l m : Copy} (hm : LegalMerge s l m) :
    EpochCompatible N C a b (merge s l m) := by
  intro x
  rw [merge_population_preserved s hm]
  exact hs x

lemma encode_epoch_compatible (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} (s : State V E Copy) (hs : SourceValid N sample s)
    (hc : EpochCompatible N C a b s) :
    EpochCompatible N C a b (state (admittedCode N sample s hs)) := by
  intro x
  rw [show copyLocation (state (admittedCode N sample s hs)) x = copyLocation s x from
    decode_encode_copyLocation N.root s hs.forest x]
  exact hc x

/-- Every ACTUAL holding or merger destination stays in the same physical
calendar epoch. Snapshot encoding cannot insert a temporally invalid location. -/
theorem actual_step_destination_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) (p : Option (Choice N s)) :
    EpochCompatible N C a b (state (stepDestination N s p)) := by
  cases p with
  | none => exact hs
  | some p =>
      let hm := GProgram.SourceForestKingmanPopulationProjection.population_pair_is_source_legal
        (state s) (originalPlace N p.1) (originalPlace_not_node N p.1) p.2.property
      let hv := merge_source_valid N sample (state s) s.property hm
      exact encode_epoch_compatible N C _ hv (epoch_merge_compatible N C hs hm)

/-- Temporal compatibility is a support theorem for the genuine normalized
source step, derived from its actual destinations. -/
theorem actual_source_step_epoch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (r : PositivePairRates E) (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) {d : Code N sample}
    (hd : d ∈ (sourceStep N r s).support) : EpochCompatible N C a b (state d) := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  exact actual_step_destination_epoch N C s hs p

/-- Every finite actual-source iteration retains the physical epoch. -/
theorem actual_source_iteration_epoch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (r : PositivePairRates E) (k : Nat) (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r k s).support) : EpochCompatible N C a b (state d) := by
  induction k generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      simpa only [he] using hs
  | succ k ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (actual_source_step_epoch_support N C r s hs hm) hdm

/-- The entire continuous-time Poisson PMF has physical epoch support when
initialized in that epoch. No desired active-location law is assumed. -/
theorem actual_source_time_epoch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a b : ℝ} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (hs : EpochCompatible N C a b (state s)) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : EpochCompatible N C a b (state d) := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_source_iteration_epoch_support N C r k s hs hk

/-- Real initial samples at their original leaves, including serial samples
that are dormant until their own supplied age. -/
theorem initial_calendar_compatible (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) {a b : ℝ}
    (h : ∀ x : Copy, b ≤ C.age (N.leaf (sample x))) :
    EpochCompatible N C a b (initial N sample register) := h

/-- Actual original vertex ages, with coincident unrelated nodes deduplicated.
The finite chronology is generated from these ages, not supplied as a desired law. -/
noncomputable def originalDates (N : RootedBinary V E X) (C : Calendar N.graph) : Finset ℝ :=
  Finset.univ.image C.age

lemma originalDates_nonempty (N : RootedBinary V E X) (C : Calendar N.graph) :
    (originalDates N C).Nonempty := by
  exact ⟨C.age N.root,Finset.mem_image.mpr ⟨N.root,Finset.mem_univ _,rfl⟩⟩

noncomputable def firstOriginalDate (N : RootedBinary V E X) (C : Calendar N.graph) : ℝ :=
  (originalDates N C).min' (originalDates_nonempty N C)

lemma firstOriginalDate_le (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    firstOriginalDate N C ≤ C.age v :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)

/-- Temporal initialization is derived from the finite original graph/calendar.
The first node boundary itself is processed by the later actual vertex agenda. -/
theorem actual_initial_calendar_boundary (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) :
    EpochCompatible N C (firstOriginalDate N C) (firstOriginalDate N C)
      (state (admittedCode N sample (initial N sample register)
        (initial_source_valid N sample register))) := by
  exact encode_epoch_compatible N C _ (initial_source_valid N sample register)
    (initial_calendar_compatible N C sample register (fun x => firstOriginalDate_le N C _))






end UnifiedLean.Source.SourceCalendarCompatibility

end FullContextModule55

section FullContextModule56



/-!
# Original-current-root pulse transported to the intrinsic selected view

Contributor: dot, 2026-10-02. The visible owner/block correspondence is derived
from the actual SourceForest invariant. Current-root coins are transported by
that equivalence; they are not assigned independently per selected original
copy. The deterministic original hybrid pulse commutes with whole-genealogy,
original-population and shared-register pruning. Natural Bernoulli measure
transport and calendar/continuous-time composition are subsequent gates.
-/
namespace UnifiedLean.Source.SourceForestPulseTransport
open Nanuq.Source GProgram.SourceForest GProgram.SourceForestKingmanProjection
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev VisibleAtNode (s : State V E Copy) (keep : Finset Copy) (node : V) :=
  { l : AtNode s node // (selectedBlock s keep l.val).Nonempty }

abbrev ViewBlockAtNode (v : SelectedView V E Copy) (keep : Finset Copy) (node : V) :=
  { A : Finset Copy // A ∈ viewPopulationBlocks v keep (.node node) }

noncomputable def ownerToBlock (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (l : VisibleAtNode s keep node) :
    ViewBlockAtNode (selectedView s keep) keep node := by
  refine ⟨selectedBlock s keep l.val.val,?_⟩
  rw [← selected_active_blocks_eq_intrinsic s hs keep (.node node)]
  exact Finset.mem_image.mpr ⟨l.val.val,Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr l.val.property,l.property⟩,rfl⟩

lemma ownerToBlock_injective (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) :
    Function.Injective (ownerToBlock s hs keep node) := by
  intro l m h
  apply Subtype.ext
  apply Subtype.ext
  exact selectedBlock_injective_on_visible s hs keep
    (Finset.mem_filter.mpr ⟨l.val.property.1,l.property⟩)
    (Finset.mem_filter.mpr ⟨m.val.property.1,m.property⟩)
    (congrArg Subtype.val h)

lemma ownerToBlock_surjective (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) :
    Function.Surjective (ownerToBlock s hs keep node) := by
  intro A
  have hA := (Finset.ext_iff.mp (selected_active_blocks_eq_intrinsic s hs keep (.node node)) A.val).mpr A.property
  obtain ⟨l,hl,heq⟩ := Finset.mem_image.mp hA
  obtain ⟨hpop,hvis⟩ := Finset.mem_filter.mp hl
  refine ⟨⟨⟨l,Finset.mem_filter.mp hpop⟩,hvis⟩,?_⟩
  exact Subtype.ext heq

/-- The two finite coin-index sets are actually equivalent. Visible current
representatives need not lie in the selected original sample panel. -/
noncomputable def visibleOwnerEquiv (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) :
    VisibleAtNode s keep node ≃ ViewBlockAtNode (selectedView s keep) keep node :=
  Equiv.ofBijective (ownerToBlock s hs keep node)
    ⟨ownerToBlock_injective s hs keep node,ownerToBlock_surjective s hs keep node⟩

/-- Projected current-root parent pulse. Coin is indexed by the whole current
selected block, so two selected copies in one genealogy cannot split. -/
noncomputable def projectedPulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) (coin : ViewBlockAtNode v keep H.hybrid → Bool) :
    SelectedView V E Copy where
  genealogy := v.genealogy
  population x := if h : x ∈ keep ∧ v.population x = some (.node H.hybrid) then
    some (.edge (H.parent (coin ⟨Genealogy.optionLeaves (v.genealogy x),
      Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
    else v.population x
  register := v.register

noncomputable def inducedBlockCoin (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (coin : AtNode s node → Bool) :
    ViewBlockAtNode (selectedView s keep) keep node → Bool :=
  fun A => coin ((visibleOwnerEquiv s hs keep node).symm A).val

lemma inducedBlockCoin_at_owner (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (coin : AtNode s node → Bool)
    (l : VisibleAtNode s keep node) :
    inducedBlockCoin s hs keep node coin (ownerToBlock s hs keep node l) = coin l.val := by
  change coin (((visibleOwnerEquiv s hs keep node).symm
    ((visibleOwnerEquiv s hs keep node) l)).val) = _
  rw [Equiv.symm_apply_apply]

lemma original_selected_location_at_pulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (coin : AtNode s H.hybrid → Bool) {x : Copy}
    (hx : x ∈ keep) (hp : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid) :
    selectedLocation (pulse H s coin) keep x =
      some (.edge (H.parent (coin ⟨s.ancestor x,hp⟩))) := by
  rw [selectedLocation,if_pos hx]
  change some ((pulse H s coin).location (s.ancestor x)) = _
  rw [pulse_routes_current_ancestor H s coin ⟨s.ancestor x,hp⟩]

lemma original_selected_location_outside_pulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (keep : Finset Copy) (coin : AtNode s H.hybrid → Bool) {x : Copy}
    (hx : x ∈ keep) (hp : ¬(s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid)) :
    selectedLocation (pulse H s coin) keep x = selectedLocation s keep x := by
  rw [selectedLocation,if_pos hx,selectedLocation,if_pos hx]
  change some ((if h : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid
    then .edge (H.parent (coin ⟨s.ancestor x,h⟩)) else s.location (s.ancestor x))) = _
  rw [dif_neg hp]
  rfl

/-- Exact commutation for the EXISTING original source pulse. The induced
coin map is constructed, rather than a desired pulse law supplied as a field. -/
theorem original_pulse_selected_view {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (coin : AtNode s H.hybrid → Bool) :
    selectedView (pulse H s coin) keep = projectedPulse H (selectedView s keep) keep
      (inducedBlockCoin s hs keep H.hybrid coin) := by
  apply SelectedView.ext
  · rfl
  · funext x
    change selectedLocation (pulse H s coin) keep x = _
    by_cases hx : x ∈ keep
    · by_cases hn : s.location (s.ancestor x) = .node H.hybrid
      · have hp : s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid :=
          ⟨hs.ancestor_live x,hn⟩
        let l : VisibleAtNode s keep H.hybrid :=
          ⟨⟨s.ancestor x,hp⟩,⟨x,(selectedBlock_eq_fiber s hs keep hp.1 x).mpr ⟨hx,rfl⟩⟩⟩
        have hv : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) := by
          simp [selectedView,selectedLocation,copyLocation,hx,hn]
        rw [original_selected_location_at_pulse H s hs keep coin hx hp]
        change some (.edge (H.parent (coin ⟨s.ancestor x,hp⟩))) =
          (if h : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) then
            some (.edge (H.parent (inducedBlockCoin s hs keep H.hybrid coin
              ⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
                Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
          else (selectedView s keep).population x)
        rw [dif_pos hv]
        have hA : (⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
            Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr hv,rfl⟩⟩ :
            ViewBlockAtNode (selectedView s keep) keep H.hybrid) =
            ownerToBlock s hs keep H.hybrid l := by
          apply Subtype.ext
          exact selected_view_block_leaves s keep hx
        rw [hA,inducedBlockCoin_at_owner]
      · have hp : ¬(s.ancestor x ∈ s.live ∧ s.location (s.ancestor x) = .node H.hybrid) :=
          fun h => hn h.2
        have hv : ¬(x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid)) := by
          simp only [selectedView,selectedLocation,if_pos hx,copyLocation]
          intro h
          exact hn (Option.some.inj h.2)
        rw [original_selected_location_outside_pulse H s keep coin hx hp]
        change (selectedView s keep).population x =
          (if h : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) then
            some (.edge (H.parent (inducedBlockCoin s hs keep H.hybrid coin
              ⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
                Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
          else (selectedView s keep).population x)
        rw [dif_neg hv]
    · have hv : ¬(x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid)) :=
        fun h => hx h.1
      change selectedLocation (pulse H s coin) keep x =
        (if h : x ∈ keep ∧ (selectedView s keep).population x = some (.node H.hybrid) then
          some (.edge (H.parent (inducedBlockCoin s hs keep H.hybrid coin
            ⟨Genealogy.optionLeaves ((selectedView s keep).genealogy x),
              Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr h,rfl⟩⟩)))
        else (selectedView s keep).population x)
      rw [dif_neg hv]
      simp only [selectedView,selectedLocation,if_neg hx]
  · rfl





end UnifiedLean.Source.SourceForestPulseTransport

end FullContextModule56

section FullContextModule57




/-!
# Natural original-current-root Bernoulli pulse under selected-label pruning

Contributor: dot, 2026-10-02. The library Bernoulli product measure is indexed
by the EXISTING actual live tokens at the ORIGINAL hybrid. Restricting to the
visible tokens and reindexing through the proved owner/block equivalence gives
exactly the natural selected-root Bernoulli law. With deterministic source pulse
commutation, the entire selected genealogy/population/register output measure
is equal. No fitted projected pulse or desired-law premise is supplied.
Calendar/continuous-time composition and full stochastic source law remain
separate. UnitInterval endpoints are supported by this general primitive;
admitted strict source parameters select its interior.
-/
namespace UnifiedLean.Source.SourceForestPulseMeasure
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open UnifiedLean.Source.SourceForestPulseTransport
open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable def bitMeasure (gamma : unitInterval) : Measure Bool :=
  bernoulliMeasure true false gamma

noncomputable def independentCoinMeasure (Site : Type*) [Fintype Site]
    (gamma : unitInterval) : Measure (Site → Bool) :=
  Measure.pi (fun _ : Site => bitMeasure gamma)

instance bitMeasure_probability (gamma : unitInterval) :
    IsProbabilityMeasure (bitMeasure gamma) := by
  unfold bitMeasure
  infer_instance

instance independentCoinMeasure_probability (Site : Type*) [Fintype Site]
    (gamma : unitInterval) : IsProbabilityMeasure (independentCoinMeasure Site gamma) := by
  unfold independentCoinMeasure
  infer_instance

/-- Exact current-root marginalization is a standard product-measure theorem;
extra original live-owner coins are neither refitted nor independently redrawn. -/
theorem coin_restriction_measurePreserving {Site : Type*} [Fintype Site]
    (gamma : unitInterval) (visible : Site → Prop) [DecidablePred visible] :
    MeasurePreserving (fun c : Site → Bool => fun l : {l // visible l} => c l.val)
      (independentCoinMeasure Site gamma)
      (independentCoinMeasure {l // visible l} gamma) := by
  have h1 := measurePreserving_piEquivPiSubtypeProd (fun _ : Site => bitMeasure gamma) visible
  have h2 := measurePreserving_fst
    (μ := Measure.pi (fun _ : {l // visible l} => bitMeasure gamma))
    (ν := Measure.pi (fun _ : {l // ¬ visible l} => bitMeasure gamma))
  exact h2.comp h1

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- The actual current original representative coin law transports to the
intrinsic selected current-block law. No selected representative ID is assumed. -/
theorem induced_original_coin_measurePreserving (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (node : V) (gamma : unitInterval) :
    MeasurePreserving (inducedBlockCoin s hs keep node)
      (independentCoinMeasure (AtNode s node) gamma)
      (independentCoinMeasure (ViewBlockAtNode (selectedView s keep) keep node) gamma) := by
  have h1 := coin_restriction_measurePreserving gamma
    (fun l : AtNode s node => (selectedBlock s keep l.val).Nonempty)
  unfold independentCoinMeasure at h1 ⊢
  have he : (⇑(MeasurableEquiv.piCongrLeft
        (fun _ : ViewBlockAtNode (selectedView s keep) keep node => Bool)
        (visibleOwnerEquiv s hs keep node))) =
      (fun c : VisibleAtNode s keep node → Bool =>
        fun A : ViewBlockAtNode (selectedView s keep) keep node =>
          c ((visibleOwnerEquiv s hs keep node).symm A)) := by
    funext c A
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have h2 := measurePreserving_piCongrLeft
      (fun _ : ViewBlockAtNode (selectedView s keep) keep node => bitMeasure gamma)
      (visibleOwnerEquiv s hs keep node)
  rw [he] at h2
  exact h2.comp h1

/-- Mathematical output carriers have the discrete sigma algebra. This is
source-state measure encoding, not a physical observation/instrument claim. -/
local instance selectedView_measurable : MeasurableSpace (SelectedView V E Copy) := ⊤

noncomputable def originalPulseLaw {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy)
    (keep : Finset Copy) (gamma : unitInterval) : Measure (SelectedView V E Copy) :=
  (independentCoinMeasure (AtNode s H.hybrid) gamma).map
    (fun coin => selectedView (pulse H s coin) keep)

noncomputable def selectedPulseLaw {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) (gamma : unitInterval) : Measure (SelectedView V E Copy) :=
  (independentCoinMeasure (ViewBlockAtNode v keep H.hybrid) gamma).map
    (fun coin => projectedPulse H v keep coin)

/-- Whole selected output law at the actual original hybrid, arbitrary finite
copy panel and arbitrary natural coin parameter. CURRENT block coins are used;
already coalesced selected original copies are never given independent bits. -/
theorem actual_original_hybrid_pulse_projectivity {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (gamma : unitInterval) :
    originalPulseLaw H s keep gamma = selectedPulseLaw H (selectedView s keep) keep gamma := by
  let c := inducedBlockCoin s hs keep H.hybrid
  let out := fun q => projectedPulse H (selectedView s keep) keep q
  have hc : Measurable c := (induced_original_coin_measurePreserving s hs keep H.hybrid gamma).measurable
  have hout : Measurable out := measurable_of_countable out
  have hfun : (fun coin => selectedView (pulse H s coin) keep) = out ∘ c := by
    funext coin
    exact original_pulse_selected_view H s hs keep coin
  unfold originalPulseLaw selectedPulseLaw
  rw [hfun,← Measure.map_map hout hc]
  rw [(induced_original_coin_measurePreserving s hs keep H.hybrid gamma).map_eq]




end UnifiedLean.Source.SourceForestPulseMeasure

end FullContextModule57

section FullContextModule58


/-!
# Same original shared-register pulse under selected genealogy pruning

Contributor: dot, 2026-10-02. COMMON inheritance uses the retained ORIGINAL
hybrid register in both full and selected internal source state. The pulse
commutes deterministically with pruning. It does not marginally replace that
register or claim exterior data/instrumentation access. Random register
initialization and continuous-time/calendar composition remain separate.
-/
namespace UnifiedLean.Source.SourceForestCommonPulse
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseTransport
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def selectedCommonPulse {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (v : SelectedView V E Copy)
    (keep : Finset Copy) : SelectedView V E Copy :=
  projectedPulse H v keep (fun _ => v.register H.hybrid)

/-- Every current selected block sees the SAME original stored register;
there is no re-coin per copy or fresh marginal component replacement. -/
theorem actual_common_pulse_pruning {N : RootedBinary V E X}
    (H : GProgram.G2.OriginalHybridParents N) (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) :
    selectedView (commonPulse H s) keep = selectedCommonPulse H (selectedView s keep) keep := by
  rw [commonPulse,original_pulse_selected_view H s hs keep]
  unfold selectedCommonPulse
  congr 1


end UnifiedLean.Source.SourceForestCommonPulse

end FullContextModule58

section FullContextModule59




/-!
# Actual finite original-node boundary kernels

Contributor: dot, 2026-10-02. Encodes the inherited actual edge exits, ordinary
indegree-one entries, ancestral root entry, CURRENT live-owner independent
Bernoulli pulse, and same-original-register COMMON pulse as finite source PMFs.
No target kernel/readout equality is an input field. The independent-pulse
selected law reuses the already-proved actual product-measure transport.
Calendar ordering and finite-time composition are subsequent original-source
assembly obligations. Selected genealogy/population/register views are internal.
-/
namespace UnifiedLean.Source.SourceBoundaryKernels
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseTransport
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Each operation names a genuine ORIGINAL source operation; ordinary entries
retain the inherited indegree-one legality requirement. -/
inductive BoundaryOperation (N : RootedBinary V E X)
  | exit (edge : E)
  | ordinary (edge : E) (degree : N.graph.inDegree (N.graph.target edge) = 1)
  | root
  | independent (parents : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
  | common (parents : GProgram.G2.OriginalHybridParents N)

noncomputable def exitCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Code N sample :=
  admittedCode N sample (exitEdge N (state s) e) (exitEdge_source_valid N sample _ s.property e)

noncomputable def ordinaryCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Code N sample :=
  admittedCode N sample (enterEdge N (state s) e) (enterEdge_source_valid N sample _ s.property e)

noncomputable def rootCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Code N sample :=
  admittedCode N sample (enterRoot N (state s)) (enterRoot_source_valid N sample _ s.property)

noncomputable def pulseCode {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) : Code N sample :=
  admittedCode N sample (pulse H (state s) coin) (pulse_source_valid H sample _ s.property coin)

noncomputable def currentCoinPMF (Site : Type*) [Fintype Site]
    (gamma : unitInterval) : PMF (Site → Bool) := (independentCoinMeasure Site gamma).toPMF

/-- Exactly CURRENT AtNode owners, not independently re-coined original copies. -/
noncomputable def independentPulseKernel {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (s : Code N sample) : PMF (Code N sample) :=
  (currentCoinPMF (AtNode (state s) H.hybrid) gamma).map (pulseCode H s)

noncomputable def boundaryKernel (N : RootedBinary V E X) {sample : Copy → X}
    (op : BoundaryOperation N) (s : Code N sample) : PMF (Code N sample) :=
  match op with
  | .exit e => PMF.pure (exitCode N s e)
  | .ordinary e _ => PMF.pure (ordinaryCode N s e)
  | .root => PMF.pure (rootCode N s)
  | .independent H gamma => independentPulseKernel H gamma s
  | .common H => PMF.pure (pulseCode H s (fun _ => (state s).register H.hybrid))

noncomputable def transportView (v : SelectedView V E Copy) (f : Location V E → Location V E) :
    SelectedView V E Copy :=
  ⟨v.genealogy,fun x => (v.population x).map f,v.register⟩

/-- Actual population transport commutes with full selected INTERNAL view. -/
theorem actual_population_transport_view (s : State V E Copy) (keep : Finset Copy)
    (f : Location V E → Location V E) (event : SourceEvent V E Copy) :
    selectedView (transport s (f ∘ s.location) event) keep = transportView (selectedView s keep) f := by
  apply SelectedView.ext
  · rfl
  · funext x
    by_cases hx : x ∈ keep <;> simp [selectedView,selectedLocation,transportView,
      transport,copyLocation,hx,Function.comp_apply]
  · rfl

noncomputable def exitLocation (N : RootedBinary V E X) (e : E) (p : Location V E) : Location V E :=
  if p = .edge e then .node (N.graph.source e) else p
noncomputable def ordinaryLocation (N : RootedBinary V E X) (e : E) (p : Location V E) : Location V E :=
  if p = .node (N.graph.target e) then .edge e else p
noncomputable def rootLocation (N : RootedBinary V E X) (p : Location V E) : Location V E :=
  if p = .node N.root then .rootPopulation N.root else p

lemma exitCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (e : E) :
    selectedView (state (exitCode N s e)) keep =
      transportView (selectedView (state s) keep) (exitLocation N e) := by
  rw [show selectedView (state (exitCode N s e)) keep = selectedView (exitEdge N (state s) e) keep from
    decode_encode_selectedView N.root _ (exitEdge_source_valid N sample _ s.property e).forest keep]
  exact actual_population_transport_view _ keep (exitLocation N e) (.edgeExit e)

lemma ordinaryCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (e : E) :
    selectedView (state (ordinaryCode N s e)) keep =
      transportView (selectedView (state s) keep) (ordinaryLocation N e) := by
  rw [show selectedView (state (ordinaryCode N s e)) keep = selectedView (enterEdge N (state s) e) keep from
    decode_encode_selectedView N.root _ (enterEdge_source_valid N sample _ s.property e).forest keep]
  exact actual_population_transport_view _ keep (ordinaryLocation N e) (.ordinaryEntry e)

lemma rootCode_view (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) :
    selectedView (state (rootCode N s)) keep =
      transportView (selectedView (state s) keep) (rootLocation N) := by
  rw [show selectedView (state (rootCode N s)) keep = selectedView (enterRoot N (state s)) keep from
    decode_encode_selectedView N.root _ (enterRoot_source_valid N sample _ s.property).forest keep]
  exact actual_population_transport_view _ keep (rootLocation N) (.rootEntry N.root)

lemma pulseCode_view {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy)
    (coin : AtNode (state s) H.hybrid → Bool) :
    selectedView (state (pulseCode H s coin)) keep = selectedView (pulse H (state s) coin) keep :=
  decode_encode_selectedView N.root _ (pulse_source_valid H sample _ s.property coin).forest keep

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

/-- The constructed finite-code PMF has precisely the existing ACTUAL original
current-owner product-measure pulse output, not a fitted selected distribution. -/
theorem independent_pulse_kernel_view_measure {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (gamma : unitInterval)
    (s : Code N sample) (keep : Finset Copy) :
    ((independentPulseKernel H gamma s).map (fun d => selectedView (state d) keep)).toMeasure =
      selectedPulseLaw H (selectedView (state s) keep) keep gamma := by
  rw [independentPulseKernel,PMF.map_comp]
  have hfun : (fun d : Code N sample => selectedView (state d) keep) ∘ pulseCode H s =
      (fun coin => selectedView (pulse H (state s) coin) keep) := by
    funext coin
    exact pulseCode_view H s keep coin
  rw [hfun,← PMF.toMeasure_map _ _ (measurable_of_countable _),
    currentCoinPMF,Measure.toPMF_toMeasure]
  exact actual_original_hybrid_pulse_projectivity H (state s) s.property.forest keep gamma

/-- Even when invisible source roots exist, the same original-register COMMON
pulse preserves the complete selected view through actual finite source coding. -/
theorem common_boundary_kernel_view {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) (keep : Finset Copy) :
    (boundaryKernel N (.common H) s).map (fun d => selectedView (state d) keep) =
      PMF.pure (selectedCommonPulse H (selectedView (state s) keep) keep) := by
  rw [boundaryKernel,PMF.pure_map,pulseCode_view]
  congr 1
  exact actual_common_pulse_pruning H (state s) s.property.forest keep





end UnifiedLean.Source.SourceBoundaryKernels

end FullContextModule59

section FullContextModule60


/-!
# Whole-law finite original boundary projection

Contributor: dot, 2026-10-02. Each actual original boundary kernel factors
through the same intrinsic pruned genealogy/population/register view. The
representative-independent row is derived from actual deterministic source
transport and current-owner Bernoulli measure transport, not stipulated. This
connects original node operations to the finite-state epoch projectivity gate.
-/
namespace UnifiedLean.Source.SourceBoundaryProjection
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceForestCommonPulse
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance viewMeasurable : MeasurableSpace (SelectedView V E Copy) := ⊤

lemma pmf_map_injective {A B : Type*} (f : A → B) (hf : Function.Injective f)
    {p q : PMF A} (h : p.map f = q.map f) : p = q := by
  apply PMF.ext
  intro a
  have ha := congrArg (fun z : PMF B => z (f a)) h
  simpa only [PMF.map_apply,hf.eq_iff,tsum_ite_eq'] using ha

/-- Whole original boundary PMF output depends only on the actual selected
internal view, including the original register needed by COMMON operations. -/
theorem boundary_kernel_view_eq_of_same_view (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N)
    (s t : Code N sample) (h : selectedView (state s) keep = selectedView (state t) keep) :
    (boundaryKernel N op s).map (fun d => selectedView (state d) keep) =
      (boundaryKernel N op t).map (fun d => selectedView (state d) keep) := by
  cases op with
  | exit e => simp only [boundaryKernel,PMF.pure_map,exitCode_view,h]
  | ordinary e degree => simp only [boundaryKernel,PMF.pure_map,ordinaryCode_view,h]
  | root => simp only [boundaryKernel,PMF.pure_map,rootCode_view,h]
  | common H => rw [common_boundary_kernel_view,common_boundary_kernel_view,h]
  | independent H gamma =>
      apply PMF.toMeasure_injective
      change ((independentPulseKernel H gamma s).map _).toMeasure =
        ((independentPulseKernel H gamma t).map _).toMeasure
      rw [independent_pulse_kernel_view_measure,independent_pulse_kernel_view_measure,h]

noncomputable def projectedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s : Code N sample) :
    PMF (SelectedIndex N sample keep) :=
  (boundaryKernel N op s).map (projection N keep)

/-- Exact row independence of hidden original representatives, derived from
all actual boundary source laws. -/
theorem projected_boundary_eq_of_same_view (N : RootedBinary V E X)
    {sample : Copy → X} (keep : Finset Copy) (op : BoundaryOperation N)
    (s t : Code N sample) (h : selectedView (state s) keep = selectedView (state t) keep) :
    projectedBoundary N keep op s = projectedBoundary N keep op t := by
  apply pmf_map_injective Subtype.val Subtype.val_injective
  simp only [projectedBoundary,PMF.map_comp]
  exact boundary_kernel_view_eq_of_same_view N keep op s t h

noncomputable def selectedBoundary (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (v : SelectedIndex N sample keep) :
    PMF (SelectedIndex N sample keep) :=
  projectedBoundary N keep op (representative N keep v)

/-- Actual original-node kernel projects to a genuine normalized selected row. -/
theorem actual_boundary_projection (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (op : BoundaryOperation N) (s : Code N sample) :
    projectedBoundary N keep op s = selectedBoundary N keep op (projection N keep s) := by
  apply projected_boundary_eq_of_same_view
  exact (representative_view N keep (projection N keep s)).symm




end UnifiedLean.Source.SourceBoundaryProjection

end FullContextModule60

section FullContextModule61



/-!
# Coherent original epoch + node program probability transport

Contributor: dot, 2026-10-02. Composes the CONSTRUCTED actual source interval
and node kernels, including current-owner independent and same-register COMMON
pulses, as genuine normalized PMFs. The entire pruned-state output law is proved
for every finite operation program, hence any later physically compiled calendar
program. No per-step intertwining or desired whole-law field is a source input.
The actual calendar compiler, physical holding-clock path identification,
separate smaller-copy carrier and final passive/unranked observation admission
remain the original source assembly obligations.
-/
namespace UnifiedLean.Source.SourceProgramTransport
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryProjection
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

inductive ProgramStep (N : RootedBinary V E X)
  | interval (duration : ℝ≥0)
  | boundary (operation : BoundaryOperation N)

noncomputable def sourceProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (s : Code N sample) : PMF (Code N sample) :=
  match op with
  | .interval t => sourceTimeKernel N r t s
  | .boundary b => boundaryKernel N b s

noncomputable def selectedProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (v : SelectedIndex N sample keep) : PMF (SelectedIndex N sample keep) :=
  match op with
  | .interval t => selectedTimeKernel N r keep t v
  | .boundary b => selectedBoundary N keep b v

/-- Both step kinds bind to actual original source operations with DERIVED
whole selected-state laws. -/
theorem actual_program_step_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (projection N keep) =
      selectedProgramStep N r keep op (projection N keep s) := by
  cases op with
  | interval t => exact constructed_source_time_kernel_projection N r keep t s
  | boundary b => exact actual_boundary_projection N keep b s

noncomputable def sourceProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → Code N sample → PMF (Code N sample)
  | [],s => PMF.pure s
  | op :: ops,s => (sourceProgramStep N r op s).bind (sourceProgram N r ops)

noncomputable def selectedProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    List (ProgramStep N) → SelectedIndex N sample keep → PMF (SelectedIndex N sample keep)
  | [],v => PMF.pure v
  | op :: ops,v => (selectedProgramStep N r keep op v).bind (selectedProgram N r keep ops)

/-- End-to-end PMF transport of the actual finite original operation program.
Independent routing uses CURRENT roots; COMMON retains the SAME original
register across the entire program. -/
theorem actual_source_program_projection (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) :
    (sourceProgram N r ops s).map (projection N keep) =
      selectedProgram N r keep ops (projection N keep s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,selectedProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [sourceProgram,PMF.map_bind]
      simp_rw [ih]
      change (sourceProgramStep N r op s).bind
        (selectedProgram N r keep ops ∘ projection N keep) = _
      rw [← PMF.bind_map,actual_program_step_projection]
      rfl

/-- Any actually selected-state-dependent endpoint readout preserves its whole
probability law. Physical/biological readout and unranked quotient binding are
not smuggled into this statement as an observed-law equality assumption. -/
theorem actual_program_endpoint_law {Obs : Type*}
    (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (ops : List (ProgramStep N))
    (s : Code N sample) (readout : SelectedIndex N sample keep → Obs) :
    (sourceProgram N r ops s).map (readout ∘ projection N keep) =
      (selectedProgram N r keep ops (projection N keep s)).map readout := by
  rw [← PMF.map_comp,actual_source_program_projection]




end UnifiedLean.Source.SourceProgramTransport

end FullContextModule61

section FullContextModule62





/-!
# ORIGINAL graph/calendar compiler to concrete source operation programs

Contributor: dot, 2026-10-02. The agenda is constructed from sorted deduplicated
ORIGINAL vertex ages. All original edge exits at a boundary precede all node
entries/pulses at that boundary; parallel edge IDs are retained. Nonhybrid
nonroot entry indegree one is derived from the actual RootedBinary degrees.
Independent pulses use actual current live-owner PMFs and COMMON reuses the
original register. Physical location preservation through the full generated
agenda, exponential holding-clock path binding and final observation assembly
are still separate source obligations, not premises inserted into this compiler.
-/
namespace UnifiedLean.Source.SourceCalendarCompiler
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma nonhybrid_nonroot_indegree_one (N : RootedBinary V E X) (v : V)
    (hr : v ≠ N.root) (hh : ¬ N.graph.IsHybrid v) : N.graph.inDegree v = 1 := by
  by_cases ht : ∃ x : X, N.leaf x = v
  · obtain ⟨x,hx⟩ := ht
    rw [← hx]
    exact (N.leaf_degrees x).1
  · have htip : ∀ x : X, N.leaf x ≠ v := fun x hx => ht ⟨x,hx⟩
    rcases N.internal_degrees v hr htip with ht | hy
    · exact ht.1
    · exact False.elim (hh hy)

/-- Only source parameters are supplied: one original parent ordering per
actual hybrid, one Bernoulli parameter and one COMMON/independent flag. -/
noncomputable def originalNodeOperation (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) : BoundaryOperation N :=
  if hr : v = N.root then .root
  else if hh : N.graph.IsHybrid v then
    if common ⟨v,hh⟩ then .common (H.parents ⟨v,hh⟩)
    else .independent (H.parents ⟨v,hh⟩) (gamma ⟨v,hh⟩)
  else .ordinary ((defaultSelector N).edge ⟨v,hr⟩) (by
    rw [(defaultSelector N).target]
    exact nonhybrid_nonroot_indegree_one N v hr hh)

/-- The compiled node operation refers to the SAME original node and actual
incoming parent edges, with ordinary-entry legality derived from N's degrees. -/
theorem original_node_is_actual_operation (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) :
    (originalNodeOperation N H gamma common v = .root ∧ v = N.root) ∨
    (∃ hy : Hybrid N, hy.val = v ∧ (H.parents hy).hybrid = v ∧
      (originalNodeOperation N H gamma common v = .common (H.parents hy) ∨
       originalNodeOperation N H gamma common v = .independent (H.parents hy) (gamma hy))) ∨
    (∃ e : E, N.graph.target e = v ∧ ∃ hd : N.graph.inDegree (N.graph.target e) = 1,
      originalNodeOperation N H gamma common v = .ordinary e hd) := by
  by_cases hr : v = N.root
  · exact Or.inl ⟨by simp [originalNodeOperation,hr],hr⟩
  · by_cases hh : N.graph.IsHybrid v
    · refine Or.inr (Or.inl ⟨⟨v,hh⟩,rfl,H.original_site _,?_⟩)
      cases hc : common ⟨v,hh⟩ <;> simp [originalNodeOperation,hr,hh,hc]
    · refine Or.inr (Or.inr ⟨(defaultSelector N).edge ⟨v,hr⟩,
        (defaultSelector N).target _,by
          rw [(defaultSelector N).target]
          exact nonhybrid_nonroot_indegree_one N v hr hh,?_⟩)
      simp [originalNodeOperation,hr,hh]

noncomputable def sortedOriginalDates (N : RootedBinary V E X) (C : Calendar N.graph) : List ℝ :=
  (originalDates N C).sort (· ≤ ·)

noncomputable def boundaryOperations (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (a : ℝ) : List (ProgramStep N) :=
  ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList.map
    (fun e => .boundary (.exit e))) ++
  ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
    (fun v => .boundary (originalNodeOperation N H gamma common v)))

noncomputable def calendarTail (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : ℝ → List ℝ → List (ProgramStep N)
  | _,[] => []
  | a,b::bs => .interval (Real.toNNReal (b-a)) ::
      (boundaryOperations N C H gamma common b ++ calendarTail N C H gamma common b bs)

noncomputable def compiledCalendarProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : List (ProgramStep N) :=
  match sortedOriginalDates N C with
  | [] => []
  | a::as => boundaryOperations N C H gamma common a ++ calendarTail N C H gamma common a as

/-- Every ORIGINAL vertex date is represented; unrelated equal ages share one
boundary. Sorting creates no new source ages. -/
theorem original_date_scheduled (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    C.age v ∈ sortedOriginalDates N C := by
  simp only [sortedOriginalDates,Finset.mem_sort]
  exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩

/-- Actual source chronology is nondecreasing and original dates are unique. -/
theorem original_dates_ordered (N : RootedBinary V E X) (C : Calendar N.graph) :
    (sortedOriginalDates N C).Pairwise (· ≤ ·) ∧ (sortedOriginalDates N C).Nodup := by
  exact ⟨Finset.pairwise_sort _ _,Finset.sort_nodup _ _⟩

/-- Constructed graph/calendar program has the already-proved whole selected
internal-state PMF law. Temporal location admission is not inferred merely
from this probability transport identity. -/
theorem compiled_original_program_projection (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) :
    (sourceProgram N r (compiledCalendarProgram N C H gamma common) s).map (projection N keep) =
      selectedProgram N r keep (compiledCalendarProgram N C H gamma common) (projection N keep s) :=
  actual_source_program_projection N r keep _ s






end UnifiedLean.Source.SourceCalendarCompiler

end FullContextModule62

section FullContextModule63


/-!
# Actual original-node/location movements of compiled boundary kernels

Contributor: dot, 2026-10-02. Establishes the location facts needed to admit the
constructed graph/calendar agenda physically. The formulas are derived from
existing actual source operations and exact snapshot decoding. CURRENT owners,
original parent edge IDs, root identity and outside-node invariance are retained;
there is no supplied desired location/clock law field.
-/
namespace UnifiedLean.Source.SourceBoundaryLocations
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma exitCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (exitCode N s e)) x = exitLocation N e (copyLocation (state s) x) := by
  rw [show copyLocation (state (exitCode N s e)) x = copyLocation (exitEdge N (state s) e) x from
    decode_encode_copyLocation N.root _ (exitEdge_source_valid N sample _ s.property e).forest x]
  rfl

lemma ordinaryCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (ordinaryCode N s e)) x = ordinaryLocation N e (copyLocation (state s) x) := by
  rw [show copyLocation (state (ordinaryCode N s e)) x = copyLocation (enterEdge N (state s) e) x from
    decode_encode_copyLocation N.root _ (enterEdge_source_valid N sample _ s.property e).forest x]
  rfl

lemma rootCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (x : Copy) :
    copyLocation (state (rootCode N s)) x = rootLocation N (copyLocation (state s) x) := by
  rw [show copyLocation (state (rootCode N s)) x = copyLocation (enterRoot N (state s)) x from
    decode_encode_copyLocation N.root _ (enterRoot_source_valid N sample _ s.property).forest x]
  rfl

/-- A parent pulse changes only CURRENT roots at its actual original hybrid. -/
theorem actual_pulse_code_location {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (state s) H.hybrid → Bool) (x : Copy) :
    (copyLocation (state s) x = .node H.hybrid → ∃ b : Bool,
      copyLocation (state (pulseCode H s coin)) x = .edge (H.parent b)) ∧
    (copyLocation (state s) x ≠ .node H.hybrid →
      copyLocation (state (pulseCode H s coin)) x = copyLocation (state s) x) := by
  rw [show copyLocation (state (pulseCode H s coin)) x = copyLocation (pulse H (state s) coin) x from
    decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property coin).forest x]
  constructor
  · intro hx
    let owner : AtNode (state s) H.hybrid :=
      ⟨(state s).ancestor x,⟨s.property.forest.ancestor_live x,hx⟩⟩
    refine ⟨coin owner,?_⟩
    exact pulse_routes_current_ancestor H (state s) coin owner
  · intro hx
    have hp : ¬ ((state s).ancestor x ∈ (state s).live ∧
        (state s).location ((state s).ancestor x) = .node H.hybrid) := fun h => hx h.2
    simp only [copyLocation,pulse,transport,dif_neg hp]

/-- A node boundary leaves every other location untouched; at the node it
enters a genuine incoming original edge, or the original ancestral root. -/
def NodeMovement (N : RootedBinary V E X) (v : V)
    (old new : Location V E) : Prop :=
  if old = .node v then
    if v = N.root then new = .rootPopulation N.root
    else ∃ e : E, N.graph.target e = v ∧ new = .edge e
  else new = old

lemma parent_move_is_node_movement (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (hy : Hybrid N) (hr : hy.val ≠ N.root)
    {old new : Location V E}
    (hp : (old = .node (H.parents hy).hybrid → ∃ b : Bool, new = .edge ((H.parents hy).parent b)) ∧
      (old ≠ .node (H.parents hy).hybrid → new = old)) : NodeMovement N hy.val old new := by
  unfold NodeMovement
  by_cases hn : old = .node hy.val
  · rw [if_pos hn,if_neg hr]
    obtain ⟨b,hb⟩ := hp.1 (by rw [H.original_site]; exact hn)
    exact ⟨(H.parents hy).parent b,registry_parent_target N H hy b,hb⟩
  · rw [if_neg hn]
    exact hp.2 (by rw [H.original_site]; exact hn)

/-- All positive-mass actual compiled node destinations satisfy the physical
original-parent movement, including both routing regimes and repeated samples. -/
theorem actual_original_node_kernel_movement (N : RootedBinary V E X)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) (x : Copy) :
    NodeMovement N v (copyLocation (state s) x) (copyLocation (state d) x) := by
  by_cases hr : v = N.root
  · simp only [originalNodeOperation,dif_pos hr,boundaryKernel,PMF.mem_support_pure_iff] at hd
    subst d
    rw [rootCode_copyLocation]
    subst v
    unfold NodeMovement rootLocation
    by_cases hn : copyLocation (state s) x = .node N.root <;> simp [hn]
  · by_cases hh : N.graph.IsHybrid v
    · cases hc : common ⟨v,hh⟩ with
      | false =>
          simp only [originalNodeOperation,dif_neg hr,dif_pos hh,hc,Bool.false_eq_true,
            if_false,boundaryKernel,independentPulseKernel] at hd
          obtain ⟨coin,_,hcoin⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
          rw [← hcoin]
          exact parent_move_is_node_movement N H ⟨v,hh⟩ hr
            (actual_pulse_code_location (H.parents ⟨v,hh⟩) s coin x)
      | true =>
          simp only [originalNodeOperation,dif_neg hr,dif_pos hh,hc,if_true,
            boundaryKernel,PMF.mem_support_pure_iff] at hd
          subst d
          exact parent_move_is_node_movement N H ⟨v,hh⟩ hr
            (actual_pulse_code_location (H.parents ⟨v,hh⟩) s _ x)
    · simp only [originalNodeOperation,dif_neg hr,dif_neg hh,
        boundaryKernel,PMF.mem_support_pure_iff] at hd
      subst d
      rw [ordinaryCode_copyLocation]
      let e := (defaultSelector N).edge ⟨v,hr⟩
      have he : N.graph.target e = v := (defaultSelector N).target _
      change NodeMovement N v (copyLocation (state s) x) (ordinaryLocation N e (copyLocation (state s) x))
      unfold NodeMovement ordinaryLocation
      rw [he]
      by_cases hn : copyLocation (state s) x = .node v
      · rw [if_pos hn,if_pos hn,if_neg hr]
        exact ⟨e,he,rfl⟩
      · simp only [if_neg hn]





end UnifiedLean.Source.SourceBoundaryLocations

end FullContextModule63

section FullContextModule64


/-!
# Derived original agenda timing facts

Contributor: dot, 2026-10-02. Closes the compiler's arithmetic admission:
sorted deduplicated original dates are strictly increasing, every consecutive
interval uses its exact positive original age difference (not clamping), and
the original root is the maximal original boundary. These facts feed full
calendar-location preservation, not a substitute for that source obligation.
-/
namespace UnifiedLean.Source.SourceCalendarTiming
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

theorem original_dates_strict (N : RootedBinary V E X) (C : Calendar N.graph) :
    (sortedOriginalDates N C).Pairwise (· < ·) := by
  exact (Finset.sortedLT_sort (originalDates N C)).pairwise

theorem actual_consecutive_duration (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {pre post : List ℝ}
    (h : sortedOriginalDates N C = pre ++ a :: b :: post) :
    a < b ∧ (Real.toNNReal (b-a) : ℝ) = b-a := by
  have hp := original_dates_strict N C
  rw [h,List.pairwise_append] at hp
  have hab : a < b := (List.pairwise_cons.mp hp.2.1).1 b (by simp)
  exact ⟨hab,Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)⟩

/-- No original vertex lies temporally above the original root. -/
theorem original_root_latest (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) :
    C.age v ≤ C.age N.root := C.age_le_of_directed (N.rooted v)

/-- The last ORIGINAL date is the actual supplied root age, not a replacement
empty exterior or an assumed stopping age. -/
theorem last_original_date_is_root (N : RootedBinary V E X) (C : Calendar N.graph) :
    (originalDates N C).max' (originalDates_nonempty N C) = C.age N.root := by
  apply le_antisymm
  · obtain ⟨v,_,hv⟩ := Finset.mem_image.mp
      ((originalDates N C).max'_mem (originalDates_nonempty N C))
    rw [← hv]
    exact original_root_latest N C v
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨N.root,Finset.mem_univ _,rfl⟩)

/-- The compiled sequence begins at the actual earliest original node age. -/
theorem first_compiled_date_is_initial_boundary (N : RootedBinary V E X) (C : Calendar N.graph) :
    (sortedOriginalDates N C)[0]'(by
      rw [sortedOriginalDates,Finset.length_sort]
      exact Finset.card_pos.mpr (originalDates_nonempty N C)) = firstOriginalDate N C := by
  exact Finset.sorted_zero_eq_min'





end UnifiedLean.Source.SourceCalendarTiming

end FullContextModule64

section FullContextModule65



/-!
# Physical calendar support of actual original boundary batches

Contributor: dot, 2026-10-02. Reuses actual source exits/current-node kernels
and derives source temporal support instead of treating SourceValid as calendar
admission. Every original edge/node ID at a date is processed by the compiled
batch, with original parent edges and retained registers. Full sorted-agenda
induction and exponential-clock path/readout binding follow this boundary gate.
-/
namespace UnifiedLean.Source.SourceCalendarPhysicalSupport
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def BoundaryReady (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop := EpochCompatible N C a a s

def AfterExits (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop :=
  BoundaryReady N C a s ∧ ∀ x : Copy, ∀ e : E, copyLocation s x = .edge e → a < C.age (N.graph.source e)

def AfterNodes (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ)
    (s : State V E Copy) : Prop :=
  AfterExits N C a s ∧ ∀ x : Copy, ∀ v : V, copyLocation s x = .node v → a < C.age v

lemma exit_preserves_ready (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a : ℝ} (s : Code N sample) (e : E)
    (he : C.age (N.graph.source e) = a) (hs : BoundaryReady N C a (state s)) :
    BoundaryReady N C a (state (exitCode N s e)) := by
  intro x
  rw [exitCode_copyLocation]
  unfold exitLocation
  by_cases hp : copyLocation (state s) x = .edge e
  · rw [if_pos hp]
    change a ≤ C.age (N.graph.source e)
    rw [he]
  · rw [if_neg hp]
    exact hs x

lemma exit_removes_edge (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (exitCode N s e)) x ≠ .edge e := by
  rw [exitCode_copyLocation]
  unfold exitLocation
  split_ifs with h
  · intro hh
    cases hh
  · exact h

lemma exit_never_creates_edge (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e f : E) (x : Copy)
    (h : copyLocation (state s) x ≠ .edge f) :
    copyLocation (state (exitCode N s e)) x ≠ .edge f := by
  rw [exitCode_copyLocation]
  unfold exitLocation
  split_ifs
  · intro hh
    cases hh
  · exact h

/-- All actual compiled exit operations are performed, with no original edge
reintroduced by a later exit. No source state is spatially refitted. -/
theorem exit_list_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) {a : ℝ} (es done : List E)
    (he : ∀ e ∈ es, C.age (N.graph.source e) = a) (s : Code N sample)
    (hs : BoundaryReady N C a (state s))
    (hno : ∀ x : Copy, ∀ e ∈ done, copyLocation (state s) x ≠ .edge e)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).support) :
    BoundaryReady N C a (state d) ∧
      ∀ x : Copy, ∀ e ∈ done ++ es, copyLocation (state d) x ≠ .edge e := by
  induction es generalizing done s with
  | nil =>
      have hds : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      exact ⟨hs,by simpa using hno⟩
  | cons e es ih =>
      have hdest : d ∈ (sourceProgram N r (es.map (fun e => .boundary (.exit e))) (exitCode N s e)).support := by
        simpa only [List.map_cons,sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind] using hd
      have hready := exit_preserves_ready N C s e (he e (by simp)) hs
      have hdone : ∀ x : Copy, ∀ f ∈ done ++ [e], copyLocation (state (exitCode N s e)) x ≠ .edge f := by
        intro x f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact exit_never_creates_edge N s e f x (hno x f hf)
        · have hfe : f = e := by simpa using hf
          subst f
          exact exit_removes_edge N s e x
      have h := ih (done ++ [e]) (fun f hf => he f (List.mem_cons_of_mem e hf))
        (exitCode N s e) hready hdone hdest
      refine ⟨h.1,?_⟩
      intro x f hf
      apply h.2 x f
      simpa only [List.append_assoc,List.singleton_append] using hf

/-- Processing precisely all ORIGINAL edges that end at a makes every
remaining edge population strictly active above a. -/
theorem actual_exit_batch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList.map
        (fun e => .boundary (.exit e))) s).support) : AfterExits N C a (state d) := by
  let es := (Finset.univ.filter (fun e : E => C.age (N.graph.source e) = a)).toList
  have hh := exit_list_support N C r es [] (by
    intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2) s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x e hp
  have hbound := hh.1 x
  rw [hp] at hbound
  have hne : C.age (N.graph.source e) ≠ a := by
    intro he
    have hm : e ∈ es := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    exact hh.2 x e (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound.2).resolve_right hne.symm

lemma node_move_preserves_after_exits (N : RootedBinary V E X) (C : Calendar N.graph)
    {a : ℝ} {v : V} (hv : C.age v = a) {old new : Location V E}
    (hready : LocationInEpoch N C a a old)
    (hstrict : ∀ e : E, old = .edge e → a < C.age (N.graph.source e))
    (hm : NodeMovement N v old new) :
    LocationInEpoch N C a a new ∧
      (∀ e : E, new = .edge e → a < C.age (N.graph.source e)) := by
  unfold NodeMovement at hm
  by_cases hn : old = .node v
  · rw [if_pos hn] at hm
    by_cases hr : v = N.root
    · rw [if_pos hr] at hm
      subst new
      refine ⟨⟨rfl,?_⟩,?_⟩
      · rw [← hr,hv]
      · intro e he
        cases he
    · rw [if_neg hr] at hm
      obtain ⟨e,he,hnew⟩ := hm
      subst new
      have ht : C.age (N.graph.target e) = a := by rw [he,hv]
      have ho : a < C.age (N.graph.source e) := by simpa only [ht] using C.edge_older e
      refine ⟨⟨ht.le,ho.le⟩,?_⟩
      intro f hf
      have heq : e = f := Location.edge.inj hf
      simpa only [← heq] using ho
  · rw [if_neg hn] at hm
    subst new
    exact ⟨hready,hstrict⟩

lemma node_move_never_creates_node (N : RootedBinary V E X) {v u : V} {old new : Location V E}
    (hm : NodeMovement N v old new) (hu : old ≠ .node u) : new ≠ .node u := by
  unfold NodeMovement at hm
  by_cases hn : old = .node v
  · rw [if_pos hn] at hm
    split_ifs at hm
    · rw [hm]
      intro h
      cases h
    · obtain ⟨e,_,he⟩ := hm
      rw [he]
      intro h
      cases h
  · rw [if_neg hn] at hm
    simpa only [hm] using hu

lemma node_move_removes_node (N : RootedBinary V E X) {v : V} {old new : Location V E}
    (hm : NodeMovement N v old new) : new ≠ .node v := by
  by_cases hn : old = .node v
  · unfold NodeMovement at hm
    rw [if_pos hn] at hm
    split_ifs at hm
    · rw [hm]
      intro h
      cases h
    · obtain ⟨e,_,he⟩ := hm
      rw [he]
      intro h
      cases h
  · exact node_move_never_creates_node N hm hn

/-- The actual node PMF retains physical active locations and eliminates its
own pending original node, for all current-root Bernoulli/Common outcomes. -/
theorem actual_node_after_exits (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} {a : ℝ} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (hv : C.age v = a) (s : Code N sample)
    (hs : AfterExits N C a (state s)) {d : Code N sample}
    (hd : d ∈ (boundaryKernel N (originalNodeOperation N H gamma common v) s).support) :
    AfterExits N C a (state d) ∧ ∀ x : Copy, copyLocation (state d) x ≠ .node v := by
  have hm := fun x => actual_original_node_kernel_movement N H gamma common v s hd x
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro x
    exact (node_move_preserves_after_exits N C hv (hs.1 x) (hs.2 x) (hm x)).1
  · intro x
    exact (node_move_preserves_after_exits N C hv (hs.1 x) (hs.2 x) (hm x)).2
  · intro x
    exact node_move_removes_node N (hm x)

lemma sourceProgram_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (xs ys : List (ProgramStep N)) (s : Code N sample) :
    sourceProgram N r (xs ++ ys) s = (sourceProgram N r xs s).bind (sourceProgram N r ys) := by
  induction xs generalizing s with
  | nil => simp only [List.nil_append,sourceProgram,PMF.pure_bind]
  | cons op xs ih =>
      change ((sourceProgramStep N r op s).bind (sourceProgram N r (xs ++ ys))) =
        ((sourceProgramStep N r op s).bind (sourceProgram N r xs)).bind (sourceProgram N r ys)
      rw [PMF.bind_bind]
      congr 1
      funext d
      exact ih d

/-- All original node operations at a boundary are processed; a later node
entry/pulse cannot reintroduce an already processed pending node. -/
theorem node_list_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {a : ℝ} (vs done : List V)
    (hv : ∀ v ∈ vs, C.age v = a) (s : Code N sample)
    (hs : AfterExits N C a (state s))
    (hno : ∀ x : Copy, ∀ v ∈ done, copyLocation (state s) x ≠ .node v)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (vs.map (fun v =>
      .boundary (originalNodeOperation N H gamma common v))) s).support) :
    AfterExits N C a (state d) ∧
      ∀ x : Copy, ∀ v ∈ done ++ vs, copyLocation (state d) x ≠ .node v := by
  induction vs generalizing done s with
  | nil =>
      have hds : d = s := by simpa only [List.map_nil,sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      exact ⟨hs,by simpa using hno⟩
  | cons v vs ih =>
      change d ∈ ((boundaryKernel N (originalNodeOperation N H gamma common v) s).bind
        (sourceProgram N r (vs.map (fun v => .boundary (originalNodeOperation N H gamma common v))))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hh := actual_node_after_exits N C H gamma common v (hv v (by simp)) s hs hm
      have hdone : ∀ x : Copy, ∀ u ∈ done ++ [v], copyLocation (state m) x ≠ .node u := by
        intro x u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact node_move_never_creates_node N
            (actual_original_node_kernel_movement N H gamma common v s hm x) (hno x u hu)
        · have huv : u = v := by simpa using hu
          subst u
          exact hh.2 x
      have h := ih (done ++ [v]) (fun u hu => hv u (List.mem_cons_of_mem v hu)) m hh.1 hdone hdm
      refine ⟨h.1,?_⟩
      intro x u hu
      apply h.2 x u
      simpa only [List.append_assoc,List.singleton_append] using hu

/-- After all ORIGINAL current-date nodes, remaining pending nodes are
strictly in the future. All independent/Common outcomes are included. -/
theorem actual_node_batch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : AfterExits N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      ((Finset.univ.filter (fun v : V => C.age v = a)).toList.map
        (fun v => .boundary (originalNodeOperation N H gamma common v))) s).support) :
    AfterNodes N C a (state d) := by
  let vs := (Finset.univ.filter (fun v : V => C.age v = a)).toList
  have hh := node_list_support N C H gamma common r vs [] (by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hv)).2) s hs (by simp) hd
  refine ⟨hh.1,?_⟩
  intro x v hp
  have hbound := hh.1.1 x
  rw [hp] at hbound
  have hne : C.age v ≠ a := by
    intro hv
    have hm : v ∈ vs := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
    exact hh.2 x v (by simpa using hm) hp
  exact (lt_or_eq_of_le hbound).resolve_right hne.symm

/-- Physical source support of the COMPLETE constructed original date batch:
all actual edge exits first, then all actual node entries/pulses. -/
theorem actual_original_boundary_batch_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (a : ℝ) (s : Code N sample)
    (hs : BoundaryReady N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (boundaryOperations N C H gamma common a) s).support) :
    AfterNodes N C a (state d) := by
  rw [boundaryOperations,sourceProgram_append] at hd
  obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_node_batch_support N C H gamma common r a m
    (actual_exit_batch_support N C r a s hs hm) hdm





end UnifiedLean.Source.SourceCalendarPhysicalSupport

end FullContextModule65

section FullContextModule66


/-!
# Initialized ORIGINAL graph/calendar agenda has physical source support

Contributor: dot, 2026-10-02. Initializes actual original sample copies at their
original tips and executes the constructed full sorted original-date agenda.
The entire PMF support is calendar-compatible across intervals/boundaries, and
every final copy occupies the SAME original ancestral population. None of these
location/initialization facts is passed as a desired source-law field. Physical
exponential-clock path identification and final unranked/timed observation
binding remain subsequent original-source obligations.
-/
namespace UnifiedLean.Source.SourceInitializedCalendar
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Completeness of a generated future-date tail, not a stochastic law field. -/
def FutureComplete (N : RootedBinary V E X) (C : Calendar N.graph) (a : ℝ) (dates : List ℝ) : Prop :=
  ∀ v : V, a < C.age v → C.age v ∈ dates

def finalDate : ℝ → List ℝ → ℝ
  | a,[] => a
  | _,b::bs => finalDate b bs

lemma after_nodes_to_epoch (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {s : State V E Copy} (hs : AfterNodes N C a s)
    (gap : ∀ v : V, a < C.age v → b ≤ C.age v) : EpochCompatible N C a b s := by
  intro x
  have hr := hs.1.1 x
  cases hp : copyLocation s x with
  | node v => exact gap v (hs.2 x v hp)
  | edge e =>
      rw [hp] at hr
      exact ⟨hr.1,gap (N.graph.source e) (hs.1.2 x e hp)⟩
  | rootPopulation v =>
      rw [hp] at hr
      exact hr

lemma epoch_to_next_ready (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : ℝ} {s : State V E Copy} (hs : EpochCompatible N C a b s) (hab : a ≤ b) :
    BoundaryReady N C b s := by
  intro x
  have h := hs x
  cases hp : copyLocation s x with
  | node v =>
      rw [hp] at h
      exact h
  | edge e =>
      rw [hp] at h
      exact ⟨h.1.trans hab,h.2⟩
  | rootPopulation v =>
      rw [hp] at h
      exact ⟨h.1,h.2.trans hab⟩

/-- Every whole sorted-agenda tail preserves physical calendar support.
Future completeness is obtained from the original finite date set below. -/
theorem actual_calendar_tail_support (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (dates : List ℝ) (a : ℝ)
    (hfuture : FutureComplete N C a dates) (hordered : dates.Pairwise (· < ·))
    (hafter : ∀ b ∈ dates, a < b) (s : Code N sample)
    (hs : AfterNodes N C a (state s)) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (calendarTail N C H gamma common a dates) s).support) :
    AfterNodes N C (finalDate a dates) (state d) ∧ ∀ v : V, C.age v ≤ finalDate a dates := by
  induction dates generalizing a s with
  | nil =>
      have hds : d = s := by simpa only [calendarTail,sourceProgram,PMF.mem_support_pure_iff] using hd
      subst d
      refine ⟨hs,?_⟩
      intro v
      by_contra hv
      exact List.not_mem_nil (hfuture v (lt_of_not_ge hv))
  | cons b bs ih =>
      have hab : a < b := hafter b (by simp)
      have hbs := List.pairwise_cons.mp hordered
      have hgap : ∀ v : V, a < C.age v → b ≤ C.age v := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v hv) with he | he
        · exact he.ge
        · exact (hbs.1 _ he).le
      have hepoch := after_nodes_to_epoch N C hs hgap
      change d ∈ ((sourceTimeKernel N r (Real.toNNReal (b-a)) s).bind
        (sourceProgram N r (boundaryOperations N C H gamma common b ++
          calendarTail N C H gamma common b bs))).support at hd
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      have hmepoch := actual_source_time_epoch_support N C r (Real.toNNReal (b-a)) s hepoch hm
      rw [sourceProgram_append] at hdm
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdm
      have hzphysical := actual_original_boundary_batch_support N C H gamma common r b m
        (epoch_to_next_ready N C hmepoch hab.le) hz
      have hnext : FutureComplete N C b bs := by
        intro v hv
        rcases List.mem_cons.mp (hfuture v (hab.trans hv)) with he | he
        · exact False.elim ((ne_of_gt hv) he)
        · exact he
      exact ih b hnext hbs.2 hbs.1 z hzphysical hdz

/-- Actual source initialization uses original sampled tip IDs and the supplied
ORIGINAL register, never a refitted/pruned physical source. -/
noncomputable def initialCode (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) : Code N sample :=
  admittedCode N sample (initial N sample register) (initial_source_valid N sample register)

/-- Exact support of the complete initialized ORIGINAL graph/calendar program.
All remaining current genealogies occupy the actual supplied root population. -/
theorem initialized_original_calendar_ancestral_support (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (compiledCalendarProgram N C H gamma common)
      (initialCode N sample register)).support) :
    ∀ x : Copy, copyLocation (state d) x = .rootPopulation N.root := by
  have hne : sortedOriginalDates N C ≠ [] := by
    intro h
    have hm := original_date_scheduled N C N.root
    rw [h] at hm
    exact List.not_mem_nil hm
  obtain ⟨a,dates,heq⟩ := List.exists_cons_of_ne_nil hne
  have hfirst : a = firstOriginalDate N C := by
    have h := first_compiled_date_is_initial_boundary N C
    simpa only [heq,List.getElem_cons_zero] using h
  have hordered := original_dates_strict N C
  rw [heq] at hordered
  have hp := List.pairwise_cons.mp hordered
  have hfuture : FutureComplete N C a dates := by
    intro v hv
    have hm := original_date_scheduled N C v
    rw [heq] at hm
    rcases List.mem_cons.mp hm with he | he
    · exact False.elim ((ne_of_gt hv) he)
    · exact he
  have hready : BoundaryReady N C a (state (initialCode N sample register)) := by
    rw [hfirst]
    exact actual_initial_calendar_boundary N C sample register
  rw [compiledCalendarProgram,heq,sourceProgram_append] at hd
  obtain ⟨s,hs,hds⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hstart := actual_original_boundary_batch_support N C H gamma common r a _ hready hs
  have hfinal := actual_calendar_tail_support N C H gamma common r dates a hfuture hp.2 hp.1 s hstart hds
  intro x
  have hreadyFinal := hfinal.1.1.1 x
  cases hloc : copyLocation (state d) x with
  | node v => exact False.elim (not_lt_of_ge (hfinal.2 v) (hfinal.1.2 x v hloc))
  | edge e => exact False.elim (not_lt_of_ge (hfinal.2 (N.graph.source e)) (hfinal.1.1.2 x e hloc))
  | rootPopulation v =>
      rw [hloc] at hreadyFinal
      exact congrArg Location.rootPopulation hreadyFinal.1




end UnifiedLean.Source.SourceInitializedCalendar

end FullContextModule66

section FullContextModule67



/-!
# ACTUAL current-source first holding clocks and Poisson kernel

Contributor: dot, 2026-10-02. Every original-population CURRENT legal pair has
an actual independent exponential clock (two ordered orientations at half-rate).
The source PMF can return to its original finite state only through holding:
every genuine source merger strictly decreases live cardinality. Its Poisson
no-real-merger probability is derived and matches the independent clock product
tail. This is the arbitrary-copy/source-state FIRST-event binding; winner/time
path/reset equivalence and final unranked/timed observation remain later gates.
-/
namespace UnifiedLean.Source.SourceActualHoldingClocks
open Nanuq.Source GProgram.SourceForest ProbabilityTheory MeasureTheory Set
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def liveCard {N : RootedBinary V E X} {sample : Copy → X} (s : Code N sample) : Nat :=
  s.val.live.card

lemma merger_destination_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    liveCard (stepDestination N s (some p)) + 1 = liveCard s :=
  merge_live_card (state s)
    (GProgram.SourceForestKingmanPopulationProjection.population_pair_is_source_legal
      (state s) (originalPlace N p.1) (originalPlace_not_node N p.1) p.2.property)

lemma step_support_card_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceStep N r s).support) : liveCard d ≤ liveCard s := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  cases p with
  | none => exact le_refl _
  | some p => have h := merger_destination_card N s p; omega

lemma iteration_support_card_le (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r k s).support) : liveCard d ≤ liveCard s := by
  induction k generalizing s with
  | zero =>
      have h : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      rw [h]
  | succ k ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact (ih m hdm).trans (step_support_card_le N r s hm)

lemma iteration_larger_card_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s d : Code N sample) (h : liveCard s < liveCard d) :
    sourceIteration N r k s d = 0 := by
  by_contra hd
  have hle := iteration_support_card_le N r k s ((PMF.mem_support_iff _ _).mpr hd)
  omega

/-- No real source merger can be hidden in a return to the same encoded state.
Its kth-step return mass is precisely k genuine holding outcomes. -/
theorem actual_iteration_no_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) :
    sourceIteration N r k s s = (choicePMF N r s none)^k := by
  induction k with
  | zero => simp only [sourceIteration,PMF.pure_apply_self,pow_zero]
  | succ k ih =>
      rw [sourceIteration,sourceStep,PMF.bind_map,PMF.bind_apply,tsum_fintype,Fintype.sum_option]
      have hzero : (∑ p : Choice N s, choicePMF N r s (some p) *
          sourceIteration N r k (stepDestination N s (some p)) s) = 0 := by
        apply Finset.sum_eq_zero
        intro p _
        have hc := merger_destination_card N s p
        rw [iteration_larger_card_zero N r k (stepDestination N s (some p)) s (by omega)]
        simp
      simp only [Function.comp_apply] at *
      rw [hzero,add_zero]
      change choicePMF N r s none * sourceIteration N r k s s = _
      rw [ih,pow_succ']

lemma poisson_hold_series (a q : ℝ) :
    (∑' k : Nat, (Real.exp (-a) * a^k / k.factorial) * q^k) = Real.exp (a*(q-1)) := by
  have hh : HasSum (fun k : Nat => (Real.exp (-a) * a^k / k.factorial) * q^k)
      (Real.exp (-a) * Real.exp (a*q)) := by
    simpa only [mul_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,← Real.exp_eq_exp_ℝ]
      using (NormedSpace.expSeries_div_hasSum_exp (a*q)).mul_left (Real.exp (-a))
  rw [hh.tsum_eq,← Real.exp_add]
  congr 1
  ring

/-- Exact no-real-merger probability of the constructed ACTUAL source epoch
PMF, with CURRENT total legal pair rate, not a fitted exponential premise. -/
theorem actual_source_kernel_no_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s s).toReal = Real.exp (-(totalRate N r s * (t : ℝ))) := by
  rw [sourceTimeKernel,bind_probability_real]
  simp_rw [countPMF_real,actual_iteration_no_merger,ENNReal.toReal_pow,choicePMF_real]
  rw [poisson_hold_series]
  congr 1
  change (globalRateBound (Copy := Copy) r * (t : ℝ)) *
    ((1-totalRate N r s/globalRateBound (Copy := Copy) r)-1) = -(totalRate N r s * (t : ℝ))
  have hne := (globalRateBound_positive (Copy := Copy) r).ne'
  field_simp [hne]
  ring

noncomputable def currentPairClockMeasure (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Measure (Choice N s → ℝ) :=
  Measure.pi (fun p => expMeasure (choiceRate N r s p))

/-- All clocks are indexed by genuine CURRENT original-population pair choices;
when there are no pairs the empty product gives survival probability one. -/
def currentNoFirstMerger (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) : Set (Choice N s → ℝ) :=
  Set.univ.pi (fun _ => Set.Ioi (t : ℝ))

theorem actual_current_clock_no_merger (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (currentPairClockMeasure N r s (currentNoFirstMerger N s t)).toReal =
      Real.exp (-(totalRate N r s * (t : ℝ))) := by
  have hp : ∀ p : Choice N s, 0 < choiceRate N r s p :=
    fun p => div_pos (pairRate_pos r p.1) (by norm_num)
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (hp p)
  rw [currentPairClockMeasure,currentNoFirstMerger,Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ p : Choice N s, (expMeasure (choiceRate N r s p)).real (Set.Ioi (t : ℝ))) = _
  have htail : (∏ p : Choice N s, (expMeasure (choiceRate N r s p)).real (Set.Ioi (t : ℝ))) =
      ∏ p : Choice N s, Real.exp (-(choiceRate N r s p * (t : ℝ))) := by
    apply Finset.prod_congr rfl
    intro p _
    exact positive_exp_clock_tail (hp p) t.property
  rw [htail,← Real.exp_sum,Finset.sum_neg_distrib,← Finset.sum_mul]
  rfl

/-- Independent ORIGINAL current-root pair clocks are bound to the actual
Poisson-source kernel at its first event. No desired clock survival equality
is assumed as a source field. -/
theorem actual_first_clock_source_binding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (currentPairClockMeasure N r s (currentNoFirstMerger N s t)).toReal =
      (sourceTimeKernel N r t s s).toReal := by
  rw [actual_current_clock_no_merger,actual_source_kernel_no_merger]





end UnifiedLean.Source.SourceActualHoldingClocks

end FullContextModule67

section FullContextModule68


/-!
# Genuine source first-merger mark retained without changing source dynamics

Contributor: dot, 2026-10-02. Augments the ACTUAL epoch state by its first actual
original-population CURRENT pair choice. Forgetting the latent mark gives the
existing source step/iteration/Poisson kernel; its marginal is the actual
absorbing first-choice process. This is proof-state instrumentation, not an
added physical control or claim that the original passive menu measures it.
Winning exponential-clock label/time and reset equivalence remain next gates.
-/
namespace UnifiedLean.Source.SourceFirstMergerMark
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- None means no real merger and the actual source is still s. After one
real merger, its actual initial choice and the evolving source state are stored. -/
abbrev FirstState (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :=
  Option (Choice N s × Code N sample)

noncomputable def forgetFirst (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : FirstState N s → Code N sample
  | none => s
  | some q => q.2

noncomputable def firstMark (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : FirstState N s → Option (Choice N s)
  | none => none
  | some q => some q.1

noncomputable def firstDestination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Option (Choice N s) → FirstState N s
  | none => none
  | some p => some (p,stepDestination N s (some p))

noncomputable def firstSourceStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : FirstState N s → PMF (FirstState N s)
  | none => (choicePMF N r s).map (firstDestination N s)
  | some q => (sourceStep N r q.2).map (fun d => some (q.1,d))

noncomputable def stoppedMarkStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Option (Choice N s) → PMF (Option (Choice N s))
  | none => choicePMF N r s
  | some p => PMF.pure (some p)

/-- The augmented primitive is EXACTLY the original physical source step
when its latent first-choice proof record is forgotten. -/
theorem first_source_step_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (z : FirstState N s) :
    (firstSourceStep N r s z).map (forgetFirst N s) = sourceStep N r (forgetFirst N s z) := by
  cases z with
  | none =>
      rw [firstSourceStep,PMF.map_comp]
      change (choicePMF N r s).map ((forgetFirst N s) ∘ firstDestination N s) = _
      have h : (forgetFirst N s) ∘ firstDestination N s = stepDestination N s := by
        funext p
        cases p <;> rfl
      rw [h]
      rfl
  | some q =>
      rw [firstSourceStep,PMF.map_comp]
      change (sourceStep N r q.2).map id = _
      rw [PMF.map_id]
      rfl

/-- Its actual first-mark marginal uses actual CURRENT original source choices;
there is no desired winner distribution supplied as a source field. -/
theorem first_source_step_mark (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (z : FirstState N s) :
    (firstSourceStep N r s z).map (firstMark N s) = stoppedMarkStep N r s (firstMark N s z) := by
  cases z with
  | none =>
      rw [firstSourceStep,PMF.map_comp]
      change (choicePMF N r s).map ((firstMark N s) ∘ firstDestination N s) = _
      have h : (firstMark N s) ∘ firstDestination N s = id := by
        funext p
        cases p <;> rfl
      rw [h,PMF.map_id]
      rfl
  | some q =>
      rw [firstSourceStep,PMF.map_comp]
      change (sourceStep N r q.2).map (Function.const _ (some q.1)) = _
      rw [PMF.map_const]
      rfl

noncomputable def firstSourceIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Nat → FirstState N s → PMF (FirstState N s)
  | 0,z => PMF.pure z
  | k+1,z => (firstSourceStep N r s z).bind (firstSourceIteration N r s k)

noncomputable def stoppedMarkIteration (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Nat → Option (Choice N s) → PMF (Option (Choice N s))
  | 0,z => PMF.pure z
  | k+1,z => (stoppedMarkStep N r s z).bind (stoppedMarkIteration N r s k)

/-- All actual source iterations are preserved, including real post-first-merger
source evolution and its current-root pair resets. -/
theorem first_iteration_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (z : FirstState N s) :
    (firstSourceIteration N r s k z).map (forgetFirst N s) =
      sourceIteration N r k (forgetFirst N s z) := by
  induction k generalizing z with
  | zero => simp only [firstSourceIteration,sourceIteration,PMF.pure_map]
  | succ k ih =>
      rw [firstSourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (firstSourceStep N r s z).bind (sourceIteration N r k ∘ forgetFirst N s) = _
      rw [← PMF.bind_map,first_source_step_forget]
      rfl

theorem first_iteration_mark (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (z : FirstState N s) :
    (firstSourceIteration N r s k z).map (firstMark N s) =
      stoppedMarkIteration N r s k (firstMark N s z) := by
  induction k generalizing z with
  | zero => simp only [firstSourceIteration,stoppedMarkIteration,PMF.pure_map]
  | succ k ih =>
      rw [firstSourceIteration,PMF.map_bind]
      simp_rw [ih]
      change (firstSourceStep N r s z).bind (stoppedMarkIteration N r s k ∘ firstMark N s) = _
      rw [← PMF.bind_map,first_source_step_mark]
      rfl

noncomputable def firstSourceTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (z : FirstState N s) : PMF (FirstState N s) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind (fun k => firstSourceIteration N r s k z)

noncomputable def firstMarkTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0)
    (z : Option (Choice N s)) : PMF (Option (Choice N s)) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind (fun k => stoppedMarkIteration N r s k z)

/-- Whole original epoch PMF is preserved by this latent first-event record. -/
theorem first_time_kernel_forget (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (z : FirstState N s) :
    (firstSourceTimeKernel N r s t z).map (forgetFirst N s) =
      sourceTimeKernel N r t (forgetFirst N s z) := by
  rw [firstSourceTimeKernel,sourceTimeKernel,PMF.map_bind]
  simp_rw [first_iteration_forget]

/-- First-event marginal derives from the ACTUAL continued source process. -/
theorem first_time_kernel_mark (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (z : FirstState N s) :
    (firstSourceTimeKernel N r s t z).map (firstMark N s) = firstMarkTimeKernel N r s t (firstMark N s z) := by
  rw [firstSourceTimeKernel,firstMarkTimeKernel,PMF.map_bind]
  simp_rw [first_iteration_mark]





end UnifiedLean.Source.SourceFirstMergerMark

end FullContextModule68

section FullContextModule69


/-!
# Derived ACTUAL source first-pair/by-time distribution

Contributor: dot, 2026-10-02. Computes the first actual original-population
CURRENT pair mark of the genuine source augmentation. Its by-time mass is
(rate/totalRate)*(1-exp(-totalRate*time)), derived from actual choice weights,
absorbing first-mark recursion and Poisson mixing. It is not supplied as a
clock/source-law field. Equality with the winning independent exponential
clock joint law, and reset/path/terminal observations, remain next gates.
-/
namespace UnifiedLean.Source.SourceFirstMarkDistribution
open Nanuq.Source ProbabilityTheory
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMergerMark
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma current_pair_total_positive (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) : 0 < totalRate N r s := by
  have hp : 0 < choiceRate N r s p := div_pos (pairRate_pos r p.1) (by norm_num)
  have hle : choiceRate N r s p ≤ totalRate N r s :=
    Finset.single_le_sum (fun q _ => (div_pos (pairRate_pos r q.1) (by norm_num)).le) (Finset.mem_univ p)
  exact hp.trans_le hle

lemma stopped_mark_absorbed (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (p : Choice N s) :
    stoppedMarkIteration N r s k (some p) = PMF.pure (some p) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [stoppedMarkIteration,stoppedMarkStep,PMF.pure_bind,ih]

lemma first_mark_some_recurrence (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (p : Choice N s) :
    (stoppedMarkIteration N r s (k+1) none (some p)).toReal =
      choiceMass N r s none * (stoppedMarkIteration N r s k none (some p)).toReal +
        choiceMass N r s (some p) := by
  rw [stoppedMarkIteration,stoppedMarkStep,bind_probability_real,tsum_fintype,Fintype.sum_option]
  simp only [choicePMF_real]
  congr 1
  calc
    _ = ∑ q : Choice N s, if q = p then choiceMass N r s (some q) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      rw [stopped_mark_absorbed]
      by_cases hq : q = p
      · simp [PMF.pure_apply,hq]
      · simp [PMF.pure_apply,hq,Ne.symm hq]
    _ = _ := by simp

/-- Exact first actual pair mark at each finite attempt count. -/
theorem actual_first_mark_attempt_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (k : Nat) (p : Choice N s) :
    (stoppedMarkIteration N r s k none (some p)).toReal =
      choiceRate N r s p / totalRate N r s * (1-(choiceMass N r s none)^k) := by
  have htotal := (current_pair_total_positive N r s p).ne'
  have hbound := (globalRateBound_positive (Copy := Copy) r).ne'
  have hchoice : choiceMass N r s (some p) =
      choiceRate N r s p / totalRate N r s * (1-choiceMass N r s none) := by
    simp only [choiceMass]
    field_simp [htotal,hbound]
    ring
  induction k with
  | zero => simp [stoppedMarkIteration,PMF.pure_apply]
  | succ k ih =>
      rw [first_mark_some_recurrence,ih,hchoice,pow_succ']
      ring

lemma actual_hold_poisson_hasSum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    HasSum (fun k : Nat =>
      (Real.exp (-((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)) *
        (((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)^k) / k.factorial) *
          (choiceMass N r s none)^k)
      (Real.exp (-(totalRate N r s * (t : ℝ)))) := by
  let a : ℝ := ((globalClockRate (Copy := Copy) r * t : ℝ≥0) : ℝ)
  let h : ℝ := choiceMass N r s none
  have hh : HasSum (fun k : Nat => (Real.exp (-a)*a^k/k.factorial)*h^k)
      (Real.exp (-a)*Real.exp (a*h)) := by
    simpa only [mul_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,← Real.exp_eq_exp_ℝ]
      using (NormedSpace.expSeries_div_hasSum_exp (a*h)).mul_left (Real.exp (-a))
  have he : Real.exp (-a)*Real.exp (a*h) = Real.exp (-(totalRate N r s * (t : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    change -(globalRateBound (Copy := Copy) r*(t : ℝ)) +
      (globalRateBound (Copy := Copy) r*(t : ℝ))*(1-totalRate N r s/globalRateBound (Copy := Copy) r) = _
    have hne := (globalRateBound_positive (Copy := Copy) r).ne'
    field_simp [hne]
    ring
  rw [he] at hh
  exact hh

/-- Pair identity AND event-before-time probability are computed from the
ACTUAL continued source process first-mark marginal. Physical exponential
race winning-label/time identification is a further source binding. -/
theorem actual_first_pair_by_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (p : Choice N s) :
    (firstMarkTimeKernel N r s t none (some p)).toReal =
      choiceRate N r s p / totalRate N r s * (1-Real.exp (-(totalRate N r s*(t : ℝ)))) := by
  rw [firstMarkTimeKernel,bind_probability_real]
  simp_rw [countPMF_real,actual_first_mark_attempt_mass]
  let a : ℝ≥0 := globalClockRate (Copy := Copy) r * t
  have hc := hasSum_one_poissonMeasure a
  have hh := actual_hold_poisson_hasSum N r s t
  have hs := (hc.sub hh).mul_left (choiceRate N r s p/totalRate N r s)
  have htarget : HasSum (fun k : Nat =>
      (Real.exp (-(a : ℝ))*(a : ℝ)^k/k.factorial) *
      (choiceRate N r s p/totalRate N r s*(1-(choiceMass N r s none)^k)))
      (choiceRate N r s p/totalRate N r s*(1-Real.exp (-(totalRate N r s*(t : ℝ))))) := by
    simpa only [a,mul_sub,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using hs
  exact htarget.tsum_eq

/-- Explicit first-pair law belongs to the actual source augmentation that
forgets exactly to the previously constructed whole original epoch kernel. -/
theorem actual_augmented_first_pair_by_time (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (p : Choice N s) :
    (((firstSourceTimeKernel N r s t none).map (firstMark N s)) (some p)).toReal =
      choiceRate N r s p / totalRate N r s * (1-Real.exp (-(totalRate N r s*(t : ℝ)))) := by
  rw [first_time_kernel_mark]
  exact actual_first_pair_by_time N r s t p





end UnifiedLean.Source.SourceFirstMarkDistribution

end FullContextModule69

section FullContextModule70




/-!
# Actual exponential race: split an original CURRENT pair clock

Contributor: dot, 2026-10-02. Finite product-measure coordinate decomposition
for the current source pair clocks, feeding the explicit winning-label/time
calculation. This standard measure identity is not a desired race law field.
Ordered half-rate choices remain internal encoding; physical unordered/unranked
readout and post-event reset/path binding must be retained as separate gates.
-/
namespace UnifiedLean.Source.SourceExponentialRace
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Other (p : I) := {q : I // q ≠ p}

/-- Literal clock coordinate split, preserving every original choice ID. -/
noncomputable def splitClock (p : I) : (I → ℝ) ≃ᵐ (ℝ × (Other p → ℝ)) where
  toFun c := (c p,fun q => c q.val)
  invFun z q := if h : q = p then z.1 else z.2 ⟨q,h⟩
  left_inv c := by
    funext q
    by_cases h : q = p
    · subst q; simp
    · simp [h]
  right_inv z := by
    apply Prod.ext
    · simp
    · funext q; simp [q.property]
  measurable_toFun := by
    change Measurable (fun c : I → ℝ => (c p,fun q : Other p => c q.val))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Other p → ℝ) => fun q : I =>
      if h : q = p then z.1 else z.2 ⟨q,h⟩)
    apply measurable_pi_lambda
    intro q
    by_cases h : q = p
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop

lemma splitClock_preimage_pi (p : I) (sets : I → Set ℝ) :
    (splitClock p).symm ⁻¹' (Set.univ.pi sets) =
      sets p ×ˢ Set.univ.pi (fun q : Other p => sets q.val) := by
  ext z
  simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Set.mem_univ,true_implies]
  change (∀ q : I, (if h : q = p then z.1 else z.2 ⟨q,h⟩) ∈ sets q) ↔
    (z.1 ∈ sets p ∧ ∀ q : Other p, z.2 q ∈ sets q.val)
  constructor
  · intro h
    refine ⟨by simpa using h p,?_⟩
    intro q
    simpa only [dif_neg q.property] using h q.val
  · rintro ⟨hp,hother⟩ q
    by_cases hq : q = p
    · subst q; simpa using hp
    · simpa only [dif_neg hq] using hother ⟨q,hq⟩

/-- Standard finite product split derived on measurable rectangles; no
conditional race/winner probability has been supplied. -/
theorem splitClock_measurePreserving (mu : I → Measure ℝ) [∀ i, SigmaFinite (mu i)] (p : I) :
    MeasurePreserving (splitClock p) (Measure.pi mu)
      ((mu p).prod (Measure.pi (fun q : Other p => mu q.val))) := by
  apply MeasurePreserving.symm (splitClock p).symm
  refine ⟨(splitClock p).symm.measurable, (Measure.pi_eq (fun sets hsets => ?_)).symm⟩
  rw [(splitClock p).symm.map_apply,splitClock_preimage_pi,Measure.prod_prod,Measure.pi_pi]
  letI : Unique {q : I // q = p} :=
    {default := ⟨p,rfl⟩,uniq := by intro q; exact Subtype.ext q.property}
  have hh := Fintype.prod_subtype_mul_prod_subtype (fun q : I => q = p) (fun q => mu q (sets q))
  have hd : (default : {q : I // q = p}).val = p := (default : {q : I // q = p}).property
  simpa only [Fintype.prod_unique,hd] using hh

/-- Winning CURRENT original pair p no later than t, with all other genuine
pair clocks strictly later. This is a latent source event, not a new readout. -/
def winnerBefore (p : I) (t : ℝ) : Set (I → ℝ) :=
  {c | c p ≤ t ∧ ∀ q : I, q ≠ p → c p < c q}

def splitWinnerBefore (p : I) (t : ℝ) : Set (ℝ × (Other p → ℝ)) :=
  {z | z.1 ≤ t ∧ ∀ q : Other p, z.1 < z.2 q}

lemma winnerBefore_preimage (p : I) (t : ℝ) :
    (splitClock p) ⁻¹' splitWinnerBefore p t = winnerBefore p t := by
  ext c
  simp only [Set.mem_preimage,splitWinnerBefore,winnerBefore,Set.mem_setOf_eq,splitClock,
    MeasurableEquiv.coe_mk]
  constructor
  · rintro ⟨ht,h⟩
    exact ⟨ht,fun q hq => h ⟨q,hq⟩⟩
  · rintro ⟨ht,h⟩
    exact ⟨ht,fun q => h q.val q.property⟩

lemma measurable_split_winner (p : I) (t : ℝ) : MeasurableSet (splitWinnerBefore p t) := by
  have h1 : MeasurableSet {z : ℝ × (Other p → ℝ) | z.1 ≤ t} :=
    measurableSet_le measurable_fst measurable_const
  have h2 : MeasurableSet (⋂ q : Other p, {z : ℝ × (Other p → ℝ) | z.1 < z.2 q}) :=
    MeasurableSet.iInter (fun q => measurableSet_lt measurable_fst
      ((measurable_pi_apply q).comp measurable_snd))
  simpa only [splitWinnerBefore,Set.setOf_and,Set.setOf_forall] using h1.inter h2

/-- Actual race event probability reduces by Fubini to the winning coordinate's
integral of independent competitor tails. -/
theorem actual_race_measure_reduction (mu : I → Measure ℝ) [∀ i, SigmaFinite (mu i)]
    (p : I) (t : ℝ) :
    (Measure.pi mu) (winnerBefore p t) =
      ∫⁻ x in Set.Iic t, (Measure.pi (fun q : Other p => mu q.val))
        (Set.univ.pi (fun _ : Other p => Set.Ioi x)) ∂(mu p) := by
  rw [← winnerBefore_preimage,
    (splitClock_measurePreserving mu p).measure_preimage_equiv (splitWinnerBefore p t)]
  rw [Measure.prod_apply (measurable_split_winner p t)]
  have hsets : ∀ x : ℝ, (Prod.mk x) ⁻¹' splitWinnerBefore p t =
      if x ≤ t then Set.univ.pi (fun _ : Other p => Set.Ioi x) else ∅ := by
    intro x
    by_cases hx : x ≤ t <;> ext c <;> simp [splitWinnerBefore,hx,Set.mem_pi]
  simp_rw [hsets]
  rw [← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro x
  by_cases hx : x ≤ t <;> simp [hx,Set.indicator]



end UnifiedLean.Source.SourceExponentialRace

end FullContextModule70

section FullContextModule71


/-!
# ORIGINAL CURRENT-pair exponential winner/by-time density

Contributor: dot, 2026-10-02. Derives the actual independent exponential race
winning coordinate/time CDF by product-measure/Fubini/PDF calculation, then
instantiates actual source rates and matches the derived first-mark source law.
No race equality is an input field. Ordered half-rate clocks are internal
encoding; complete unordered/unranked reset/path/timed-law assembly remains.
-/
namespace UnifiedLean.Source.SourceExponentialRaceDensity
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open UnifiedLean.Source.SourceExponentialRace
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma sum_other_plus_pair (rate : I → ℝ) (p : I) :
    rate p + (∑ q : Other p, rate q.val) = ∑ i : I, rate i := by
  letI : Unique {q : I // q = p} :=
    {default := ⟨p,rfl⟩,uniq := by intro q; exact Subtype.ext q.property}
  have hd : (default : {q : I // q = p}).val = p := (default : {q : I // q = p}).property
  simpa only [Fintype.sum_unique,hd] using
    (Fintype.sum_subtype_add_sum_subtype (fun q : I => q = p) rate)

lemma race_total_positive (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) :
    0 < ∑ i : I, rate i :=
  (hr p).trans_le (Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ p))

/-- Exact independent competitor tail, conditional on the actual winning
coordinate time x. Empty competitors correctly have probability one. -/
lemma competitor_tail (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I)
    {x : ℝ} (hx : 0 ≤ x) :
    (Measure.pi (fun q : Other p => expMeasure (rate q.val)))
      (Set.univ.pi (fun _ : Other p => Set.Ioi x)) =
        ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) := by
  letI : ∀ q : Other p, IsProbabilityMeasure (expMeasure (rate q.val)) :=
    fun q => isProbabilityMeasure_expMeasure (hr q.val)
  have hh : ((Measure.pi (fun q : Other p => expMeasure (rate q.val)))
      (Set.univ.pi (fun _ : Other p => Set.Ioi x))).toReal =
        Real.exp (-((∑ q : Other p, rate q.val)*x)) := by
    rw [Measure.pi_pi,ENNReal.toReal_prod]
    change (∏ q : Other p, (expMeasure (rate q.val)).real (Set.Ioi x)) = _
    have htail : (∏ q : Other p, (expMeasure (rate q.val)).real (Set.Ioi x)) =
        ∏ q : Other p, Real.exp (-(rate q.val*x)) := by
      apply Finset.prod_congr rfl
      intro q _
      exact UnifiedLean.Source.NativePairClockLaw.positive_exp_clock_tail (hr q.val) hx
    rw [htail,← Real.exp_sum,Finset.sum_neg_distrib,← Finset.sum_mul]
  rw [← hh,ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Multiplying the ACTUAL winning clock's PDF by its independent competitor
tails is the rate fraction times the ACTUAL total-rate exponential PDF. -/
lemma actual_race_pdf_factor (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) (x : ℝ) :
    exponentialPDF (rate p) x *
      (Measure.pi (fun q : Other p => expMeasure (rate q.val)))
        (Set.univ.pi (fun _ : Other p => Set.Ioi x)) =
      ENNReal.ofReal (rate p/(∑ i : I, rate i)) * exponentialPDF (∑ i : I, rate i) x := by
  have htotal := race_total_positive rate hr p
  by_cases hx : 0 ≤ x
  · rw [competitor_tail rate hr p hx,exponentialPDF_of_nonneg hx,exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (mul_nonneg (hr p).le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (div_nonneg (hr p).le htotal.le)]
    congr 1
    have hs := sum_other_plus_pair rate p
    have hexp : Real.exp (-(rate p*x))*Real.exp (-((∑ q : Other p, rate q.val)*x)) =
        Real.exp (-((∑ i : I, rate i)*x)) := by
      rw [← Real.exp_add]
      congr 1
      rw [← hs]
      ring
    calc
      rate p*Real.exp (-(rate p*x))*Real.exp (-((∑ q : Other p, rate q.val)*x)) =
        rate p*(Real.exp (-(rate p*x))*Real.exp (-((∑ q : Other p, rate q.val)*x))) := by ring
      _ = rate p*Real.exp (-((∑ i : I, rate i)*x)) := by rw [hexp]
      _ = rate p/(∑ i : I, rate i)*((∑ i : I, rate i)*Real.exp (-((∑ i : I, rate i)*x))) := by
        field_simp [htotal.ne']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx),zero_mul,mul_zero]

/-- Full actual winning-coordinate/by-time probability, not merely survival
or an assumed proportional winner distribution. -/
theorem actual_exponential_race_winner_by_time (rate : I → ℝ) (hr : ∀ i, 0 < rate i)
    (p : I) (t : ℝ≥0) :
    ((Measure.pi (fun i => expMeasure (rate i))) (winnerBefore p (t : ℝ))).toReal =
      rate p/(∑ i : I, rate i)*(1-Real.exp (-((∑ i : I, rate i)*(t : ℝ)))) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have htotal := race_total_positive rate hr p
  rw [actual_race_measure_reduction]
  have hh : (∫⁻ x in Set.Iic (t : ℝ),
      (Measure.pi (fun q : Other p => expMeasure (rate q.val)))
        (Set.univ.pi (fun _ : Other p => Set.Ioi x)) ∂expMeasure (rate p)) =
      ENNReal.ofReal (rate p/(∑ i : I, rate i)) *
        ∫⁻ x in Set.Iic (t : ℝ), exponentialPDF (∑ i : I, rate i) x := by
    change (∫⁻ x in Set.Iic (t : ℝ), _ ∂volume.withDensity (exponentialPDF (rate p))) = _
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
      (by unfold exponentialPDF; fun_prop) _ measurableSet_Iic
      (Filter.Eventually.of_forall (fun x => by unfold exponentialPDF; exact ENNReal.ofReal_lt_top))]
    simp only [Pi.mul_apply]
    simp_rw [actual_race_pdf_factor rate hr p]
    rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop)]
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.property
  rw [hh,lintegral_exponentialPDF_eq_antiDeriv htotal,if_pos ht]
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (div_nonneg (hr p).le htotal.le)]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [t.property])))]

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceFirstMergerMark
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual ORIGINAL current-pair exponential winner/time law matches the
actual source first-mark/by-time law. Post-event reset/path consistency and
physical unordered/unranked observation still require their next source links. -/
theorem original_current_race_source_mark_binding (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) (p : Choice N s) :
    (currentPairClockMeasure N r s (winnerBefore p (t : ℝ))).toReal =
      (firstMarkTimeKernel N r s t none (some p)).toReal := by
  have hp : ∀ q : Choice N s, 0 < choiceRate N r s q :=
    fun q => div_pos (pairRate_pos r q.1) (by norm_num)
  rw [currentPairClockMeasure,actual_exponential_race_winner_by_time _ hp,
    actual_first_pair_by_time]
  rfl




end UnifiedLean.Source.SourceExponentialRaceDensity

end FullContextModule71

section FullContextModule72



/-!
# Actual exponential residual clocks

Contributor: dot, 2026-10-02. This is the measure-level memorylessness used
inside the forthcoming winner-conditioned reset calculation. The law is
proved for the literal exponential measure, not supplied as a source field.
The connected next endpoint must retain the winner/time and all surviving
clock coordinates; deterministic survival alone is not a complete path law.
-/
namespace UnifiedLean.Source.SourceExponentialResiduals
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators NNReal ENNReal

lemma exponential_real_Iic {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (expMeasure r).real (Iic x) = if 0 ≤ x then 1-Real.exp (-(r*x)) else 0 := by
  letI := isProbabilityMeasure_expMeasure hr
  rw [← cdf_eq_real, cdf_expMeasure_eq hr]

lemma exponential_real_Ioc {r u x : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (hx : 0 ≤ x) :
    (expMeasure r).real (Ioc u (u+x)) =
      Real.exp (-(r*u)) * (1-Real.exp (-(r*x))) := by
  letI := isProbabilityMeasure_expMeasure hr
  rw [← Iic_sdiff_Iic, measureReal_sdiff (Iic_subset_Iic.mpr (by linarith)) measurableSet_Iic,
    exponential_real_Iic hr, exponential_real_Iic hr, if_pos (by linarith : 0 ≤ u+x), if_pos hu]
  have hh : Real.exp (-(r*(u+x))) = Real.exp (-(r*u))*Real.exp (-(r*x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hh]
  ring

/-- Shift the actual surviving exponential clock by elapsed time. This exact
unnormalized measure identity retains the survival mass explicitly. -/
theorem actual_exponential_residual_measure {r : ℝ} (hr : 0 < r) (u : ℝ≥0) :
    ((expMeasure r).restrict (Ioi (u : ℝ))).map (fun y : ℝ => y-(u : ℝ)) =
      ENNReal.ofReal (Real.exp (-(r*(u : ℝ)))) • expMeasure r := by
  letI := isProbabilityMeasure_expMeasure hr
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage (by fun_prop : Measurable (fun y : ℝ => y-(u : ℝ))))]
  have hp : (fun y : ℝ => y-(u : ℝ)) ⁻¹' Iic x ∩ Ioi (u : ℝ) = Ioc (u : ℝ) ((u : ℝ)+x) := by
    ext y
    simp only [mem_inter_iff,mem_preimage,mem_Iic,mem_Ioi,mem_Ioc]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  rw [hp]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  change (expMeasure r).real (Ioc (u : ℝ) ((u : ℝ)+x)) = _
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change _ = Real.exp (-(r*(u : ℝ))) * (expMeasure r).real (Iic x)
  rw [exponential_real_Iic hr]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact exponential_real_Ioc hr (show (0 : ℝ) ≤ (u : ℝ) from u.property) hx
  · rw [if_neg hx,Ioc_eq_empty_of_le (by linarith),measureReal_empty,mul_zero]

variable {I : Type*} [Fintype I]

/-- All genuine surviving coordinates retain their independent original
exponential law after elapsed time is subtracted. No posterior law is an
input; the unnormalized survival factor is explicitly derived. -/
theorem actual_exponential_product_residual_measure (rate : I → ℝ)
    (hr : ∀ i, 0 < rate i) (u : ℝ≥0) :
    ((Measure.pi (fun i => expMeasure (rate i))).restrict
      (Set.univ.pi (fun _ : I => Ioi (u : ℝ)))).map
      (fun c : I → ℝ => fun i => c i-(u : ℝ)) =
      ENNReal.ofReal (Real.exp (-((∑ i, rate i)*(u : ℝ)))) •
        Measure.pi (fun i => expMeasure (rate i)) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  rw [Measure.restrict_pi_pi,Measure.pi_map_pi (f := fun _ : I => fun y : ℝ => y-(u : ℝ)) (fun i => by fun_prop)]
  simp_rw [actual_exponential_residual_measure (hr _)]
  letI : ∀ i : I, IsFiniteMeasure (ENNReal.ofReal (Real.exp (-(rate i*(u : ℝ)))) • expMeasure (rate i)) :=
    fun i => Measure.smul_finite _ ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro sets hsets
  rw [Measure.smul_apply,smul_eq_mul,Measure.pi_pi]
  simp_rw [Measure.smul_apply,smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),← Real.exp_sum]
  congr 1
  rw [Finset.sum_neg_distrib,Finset.sum_mul]

/-- Equivalent arbitrary measurable residual-event form, used at the actual
random first winning time by Fubini in the connected race/reset theorem. -/
theorem actual_survivor_residual_event (rate : I → ℝ)
    (hr : ∀ i, 0 < rate i) (u : ℝ≥0) (B : Set (I → ℝ)) (hB : MeasurableSet B) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((fun c : I → ℝ => fun i => c i-(u : ℝ)) ⁻¹' B ∩
        Set.univ.pi (fun _ : I => Ioi (u : ℝ))) =
      ENNReal.ofReal (Real.exp (-((∑ i, rate i)*(u : ℝ)))) *
        (Measure.pi (fun i => expMeasure (rate i))) B := by
  have hh := congrArg (fun mu : Measure (I → ℝ) => mu B)
    (actual_exponential_product_residual_measure rate hr u)
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.restrict_apply (hB.preimage (by fun_prop)),Measure.smul_apply,smul_eq_mul] at hh
  exact hh




end UnifiedLean.Source.SourceExponentialResiduals

end FullContextModule72

section FullContextModule73


/-!
# Winning-clock time and independent residuals of every surviving coordinate

Contributor: dot, 2026-10-02. The actual product clock measure is restricted
to an actual winning coordinate and mapped to its time plus all competitors'
residual clocks. Factorization is derived, not a supplied reset-law field.
Original source destination/reset catalogue and successive path assembly are
subsequent bindings; latent clock records are not added physical observations.
-/
namespace UnifiedLean.Source.SourceWinningClockReset
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceExponentialRaceDensity
open UnifiedLean.Source.SourceExponentialResiduals
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Literal winning time and every original competitor's remaining clock. -/
noncomputable def resetClock (p : I) : (I → ℝ) ≃ᵐ (ℝ × (Other p → ℝ)) where
  toFun c := (c p,fun q => c q.val-c p)
  invFun z q := if h : q = p then z.1 else z.1+z.2 ⟨q,h⟩
  left_inv c := by
    funext q
    by_cases h : q = p
    · subst q; simp
    · simp [h]
  right_inv z := by
    apply Prod.ext
    · simp
    · funext q; simp [q.property]
  measurable_toFun := by
    change Measurable (fun c : I → ℝ => (c p,fun q : Other p => c q.val-c p))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Other p → ℝ) => fun q : I =>
      if h : q = p then z.1 else z.1+z.2 ⟨q,h⟩)
    apply measurable_pi_lambda
    intro q
    by_cases h : q = p
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop

def winningRegion (p : I) : Set (I → ℝ) :=
  {c | 0 ≤ c p ∧ ∀ q : Other p, c p < c q.val}

lemma measurable_winningRegion (p : I) : MeasurableSet (winningRegion p) := by
  have h1 : MeasurableSet {c : I → ℝ | 0 ≤ c p} :=
    measurableSet_le measurable_const (measurable_pi_apply p)
  have h2 : MeasurableSet (⋂ q : Other p, {c : I → ℝ | c p < c q.val}) :=
    MeasurableSet.iInter (fun q => measurableSet_lt (measurable_pi_apply p) (measurable_pi_apply q.val))
  simpa only [winningRegion,Set.setOf_and,Set.setOf_forall] using h1.inter h2

def splitResetEvent (p : I) (A : Set ℝ) (B : Set (Other p → ℝ)) :
    Set (ℝ × (Other p → ℝ)) :=
  {z | z.1 ∈ A ∧ 0 ≤ z.1 ∧
    (fun q : Other p => z.2 q-z.1) ∈ B ∧ ∀ q : Other p, z.1 < z.2 q}

lemma measurable_split_reset (p : I) (A : Set ℝ) (B : Set (Other p → ℝ))
    (hA : MeasurableSet A) (hB : MeasurableSet B) : MeasurableSet (splitResetEvent p A B) := by
  have h1 : MeasurableSet {z : ℝ × (Other p → ℝ) | z.1 ∈ A} := hA.preimage measurable_fst
  have h2 : MeasurableSet {z : ℝ × (Other p → ℝ) | 0 ≤ z.1} :=
    measurableSet_le measurable_const measurable_fst
  have h3 : MeasurableSet {z : ℝ × (Other p → ℝ) | (fun q : Other p => z.2 q-z.1) ∈ B} := hB.preimage (by fun_prop :
    Measurable (fun z : ℝ × (Other p → ℝ) => fun q => z.2 q-z.1))
  have h4 : MeasurableSet (⋂ q : Other p, {z : ℝ × (Other p → ℝ) | z.1 < z.2 q}) :=
    MeasurableSet.iInter (fun q => measurableSet_lt measurable_fst
      ((measurable_pi_apply q).comp measurable_snd))
  simpa only [splitResetEvent,Set.setOf_and,Set.setOf_forall] using
    h1.inter (h2.inter (h3.inter h4))

lemma actual_reset_event_fubini (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I)
    (A : Set ℝ) (B : Set (Other p → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((resetClock p) ⁻¹' (A ×ˢ B) ∩ winningRegion p) =
      ∫⁻ x in A ∩ Ici 0,
        ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) *
          (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B ∂expMeasure (rate p) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have hp : (resetClock p) ⁻¹' (A ×ˢ B) ∩ winningRegion p =
      (splitClock p) ⁻¹' splitResetEvent p A B := by
    ext c
    simp only [mem_inter_iff,mem_preimage,mem_prod,resetClock,splitClock,
      MeasurableEquiv.coe_mk,winningRegion,splitResetEvent,mem_setOf_eq]
    tauto
  rw [hp,(splitClock_measurePreserving (fun i => expMeasure (rate i)) p).measure_preimage_equiv,
    Measure.prod_apply (measurable_split_reset p A B hA hB)]
  have hs : ∀ x : ℝ, (Prod.mk x) ⁻¹' splitResetEvent p A B =
      if x ∈ A ∩ Ici 0 then
        (fun c : Other p → ℝ => fun q => c q-x) ⁻¹' B ∩
          Set.univ.pi (fun _ : Other p => Ioi x) else ∅ := by
    intro x
    by_cases hx : x ∈ A ∩ Ici 0
    · rw [if_pos hx]
      ext c
      simp only [mem_preimage,splitResetEvent,mem_setOf_eq,mem_inter_iff,mem_pi,
        mem_univ,true_implies,mem_Ioi]
      exact ⟨fun h => ⟨h.2.2.1,h.2.2.2⟩,fun h => ⟨hx.1,hx.2,h.1,h.2⟩⟩
    · rw [if_neg hx]
      ext c
      simp only [mem_preimage,splitResetEvent,mem_setOf_eq,mem_empty_iff_false]
      exact ⟨fun h => hx ⟨h.1,h.2.1⟩,False.elim⟩
  simp_rw [hs]
  rw [← lintegral_indicator (hA.inter measurableSet_Ici)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A ∩ Ici 0
  · simp only [if_pos hx,Set.indicator_of_mem hx]
    exact actual_survivor_residual_event (fun q : Other p => rate q.val)
      (fun q => hr q.val) ⟨x,hx.2⟩ B hB
  · simp only [if_neg hx,measure_empty,Set.indicator_of_notMem hx]

lemma exponential_nonnegative_support {r : ℝ} (hr : 0 < r) :
    (expMeasure r).restrict (Ici 0) = expMeasure r := by
  letI := isProbabilityMeasure_expMeasure hr
  have hz : (expMeasure r) (Iic 0) = 0 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((expMeasure r).real (Iic 0)) = 0
    rw [exponential_real_Iic hr]
    simp
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro x hx
  simp only [mem_setOf_eq,mem_Ici,not_le] at hx
  exact hx.le

lemma residual_pdf_factor (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) (x : ℝ) :
    exponentialPDF (rate p) x *
      ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) =
      ENNReal.ofReal (rate p/(∑ i, rate i)) * exponentialPDF (∑ i, rate i) x := by
  by_cases hx : 0 ≤ x
  · have hh := actual_race_pdf_factor rate hr p x
    rw [competitor_tail rate hr p hx] at hh
    exact hh
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),exponentialPDF_of_neg (lt_of_not_ge hx),
      zero_mul,mul_zero]

/-- Joint probability of the actual winning time and ANY measurable event
of all residual competitor clocks factors exactly. This is stronger than
the winner CDF or scalar no-event memorylessness. -/
theorem actual_winner_residual_rectangle (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I)
    (A : Set ℝ) (B : Set (Other p → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((resetClock p) ⁻¹' (A ×ˢ B) ∩ winningRegion p) =
      ENNReal.ofReal (rate p/(∑ i, rate i)) * (expMeasure (∑ i, rate i)) A *
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B := by
  have htotal := race_total_positive rate hr p
  rw [actual_reset_event_fubini rate hr p A B hA hB]
  change (∫⁻ x in A ∩ Ici 0, _ ∂volume.withDensity (exponentialPDF (rate p))) = _
  rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable volume
    (by unfold exponentialPDF; fun_prop) _ (hA.inter measurableSet_Ici)
    (Filter.Eventually.of_forall (fun x => by unfold exponentialPDF; exact ENNReal.ofReal_lt_top))]
  simp only [Pi.mul_apply]
  have hf : ∀ x : ℝ, exponentialPDF (rate p) x *
      (ENNReal.ofReal (Real.exp (-((∑ q : Other p, rate q.val)*x))) *
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B) =
      (ENNReal.ofReal (rate p/(∑ i, rate i)) *
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) B) *
          exponentialPDF (∑ i, rate i) x := by
    intro x
    rw [← mul_assoc,residual_pdf_factor rate hr p]
    ac_rfl
  simp_rw [hf]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop)]
  have hmass : (∫⁻ x in A ∩ Ici 0, exponentialPDF (∑ i, rate i) x) =
      (expMeasure (∑ i, rate i)) A := by
    change _ = (volume.withDensity (exponentialPDF (∑ i, rate i))) A
    rw [withDensity_apply _ hA]
    have hh := congrArg (fun mu : Measure ℝ => mu A) (exponential_nonnegative_support htotal)
    rw [Measure.restrict_apply hA] at hh
    change (volume.withDensity (exponentialPDF (∑ i, rate i))) (A ∩ Ici 0) =
      (volume.withDensity (exponentialPDF (∑ i, rate i))) A at hh
    rw [withDensity_apply _ (hA.inter measurableSet_Ici),withDensity_apply _ hA] at hh
    exact hh
  rw [hmass]
  ac_rfl

/-- Full joint reset measure: after an actual winning coordinate p, every
remaining clock is independently exponential at its SAME original rate and
independent of the winning time. The winning mass is the original rate
fraction; neither factorization nor a conditional reset law is assumed. -/
theorem actual_winner_reset_measure (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) :
    ((Measure.pi (fun i => expMeasure (rate i))).restrict (winningRegion p)).map (resetClock p) =
      (ENNReal.ofReal (rate p/(∑ i, rate i)) • expMeasure (∑ i, rate i)).prod
        (Measure.pi (fun q : Other p => expMeasure (rate q.val))) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  letI := isProbabilityMeasure_expMeasure (race_total_positive rate hr p)
  letI := Measure.smul_finite (expMeasure (∑ i, rate i))
    (show ENNReal.ofReal (rate p/(∑ i, rate i)) ≠ ∞ from ENNReal.ofReal_ne_top)
  apply (Measure.prod_eq _).symm
  intro A B hA hB
  rw [(resetClock p).map_apply,Measure.restrict_apply ((hA.prod hB).preimage (resetClock p).measurable),
    actual_winner_residual_rectangle rate hr p A B hA hB,Measure.smul_apply,smul_eq_mul]

open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- SOURCE INSTANCE of the full winning-time/residual law. All original
CURRENT competitor IDs and their original population half-rates are retained.
An actual winner yields independent original-rate residuals, independent of
its time. This discharges the clock-memoryless reset implication; choosing
the merged destination's persistent/new pair catalogue and composing all
successive paths remain the connected original-source assembly. -/
theorem original_current_winner_reset (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    ((currentPairClockMeasure N r s).restrict (winningRegion p)).map (resetClock p) =
      (ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).prod
        (Measure.pi (fun q : Other p => expMeasure (choiceRate N r s q.val))) := by
  apply actual_winner_reset_measure
  intro q
  exact div_pos (pairRate_pos r q.1) (by norm_num)





end UnifiedLean.Source.SourceWinningClockReset

end FullContextModule73

section FullContextModule74


/-!
# Actual merged CURRENT-pair catalogue inside the surviving clock coordinates

Contributor: dot, 2026-10-02. Original source merges erase only their second
live representative and retain every remaining live population. Consequently
EVERY pair in the actual coded destination is an injective, same-rate original
competitor of the winning clock. This supplies the concrete catalogue needed
to transport the proved residual product law, rather than an assumed reset.
-/
namespace UnifiedLean.Source.SourceMergerClockCatalogue
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceExponentialRace
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma merged_live (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    (state (stepDestination N s (some p))).live = (state s).live.erase p.2.val.2 := rfl

lemma merged_live_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (x : Copy)
    (hx : x ∈ (state (stepDestination N s (some p))).live) :
    (state (stepDestination N s (some p))).location x = (state s).location x := by
  unfold state stepDestination admittedCode
  rw [decode_encode_live_population]
  rfl
  exact hx

/-- Actual finite coding does not invent or move a live population after a
merger. Its original-population root catalogue erases exactly the removed ID. -/
theorem merged_population_catalogue (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (place : Location V E) :
    populationRoots (state (stepDestination N s (some p))) place =
      (populationRoots (state s) place).erase p.2.val.2 := by
  ext x
  simp only [populationRoots,Finset.mem_filter,Finset.mem_erase]
  have hl := merged_live N s p
  by_cases hx : x ∈ (state (stepDestination N s (some p))).live
  · rw [merged_live_population N s p x hx]
    rw [hl,Finset.mem_erase] at hx ⊢
    tauto
  · have hn : ¬(x ≠ p.2.val.2 ∧ x ∈ (state s).live) := by
      simpa only [hl,Finset.mem_erase] using hx
    tauto

lemma destination_pair_old (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) :
    q.2.val ∈ (populationRoots (state s) (originalPlace N q.1)).offDiag := by
  have h := q.2.property
  simp only [merged_population_catalogue] at h
  rcases Finset.mem_offDiag.mp h with ⟨h1,h2,hne⟩
  exact Finset.mem_offDiag.mpr ⟨(Finset.mem_erase.mp h1).2,(Finset.mem_erase.mp h2).2,hne⟩

noncomputable def destinationChoiceOld (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) : Choice N s :=
  ⟨q.1,⟨q.2.val,destination_pair_old N s p q⟩⟩

lemma destinationChoiceOld_injective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    Function.Injective (destinationChoiceOld N s p) := by
  intro q q' h
  have hi : q.1 = q'.1 := congrArg (fun z : Choice N s => z.1) h
  have hp : q.2.val = q'.2.val := congrArg (fun z : Choice N s => z.2.val) h
  cases q with
  | mk i q =>
      cases q' with
      | mk i' q' =>
          cases hi
          exact congrArg (Sigma.mk i) (Subtype.ext hp)

lemma destinationChoiceOld_ne_winner (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) : destinationChoiceOld N s p q ≠ p := by
  have h := q.2.property
  simp only [merged_population_catalogue] at h
  have hn := (Finset.mem_erase.mp (Finset.mem_offDiag.mp h).2.1).1
  intro heq
  exact hn (congrArg (fun z : Choice N s => z.2.val.2) heq)

/-- Every actual post-merger coordinate is a distinct genuine surviving
old coordinate. Both original graph/population and current representative IDs
are preserved by the embedding; all removed-ID clocks are discarded. -/
noncomputable def destinationClockEmbedding (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    Choice N (stepDestination N s (some p)) ↪ Other p where
  toFun q := ⟨destinationChoiceOld N s p q,destinationChoiceOld_ne_winner N s p q⟩
  inj' := by
    intro q q' h
    exact destinationChoiceOld_injective N s p (congrArg Subtype.val h)

theorem destination_clock_original_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p))) :
    choiceRate N r s (destinationClockEmbedding N s p q).val =
      choiceRate N r (stepDestination N s (some p)) q := rfl




end UnifiedLean.Source.SourceMergerClockCatalogue

end FullContextModule74

section FullContextModule75



/-!
# ORIGINAL actual post-merger current-clock reset law

Contributor: dot, 2026-10-02. Reuses library independence of product coordinates
to transport the already proved winning-time/residual law along the actual
same-rate post-merger catalogue embedding. All obsolete clocks are dropped;
the destination has its literal independent exponential current-pair law.
No destination/reset distribution is assumed. Successive timed source paths,
calendar composition and terminal genealogical completion remain next gates.
-/
namespace UnifiedLean.Source.SourceDestinationClockReset
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceWinningClockReset
open UnifiedLean.Source.SourceMergerClockCatalogue
open scoped Classical BigOperators NNReal ENNReal

lemma actual_product_coordinate_projection {I J : Type*} [Fintype I] [Fintype J]
    (mu : I → Measure ℝ) [∀ i, IsProbabilityMeasure (mu i)] (e : J ↪ I) :
    (Measure.pi mu).map (fun c : I → ℝ => fun j => c (e j)) =
      Measure.pi (fun j => mu (e j)) := by
  have hind : iIndepFun (fun i : I => fun c : I → ℝ => c i) (Measure.pi mu) :=
    iIndepFun_pi (μ := mu) (X := fun _ : I => fun y : ℝ => y)
      (fun _ => measurable_id.aemeasurable)
  have hsub := hind.precomp (g := e) e.injective
  have hh := hsub.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  simp_rw [(measurePreserving_eval mu _).map_eq] at hh
  exact hh

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Every current destination clock is a genuine surviving coordinate with
the same original population rate. Its joint law is therefore the literal
actual clock product at that actual merged coded state. -/
theorem actual_destination_residual_product (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    (Measure.pi (fun q : Other p => expMeasure (choiceRate N r s q.val))).map
      (fun c : Other p → ℝ => fun q : Choice N (stepDestination N s (some p)) =>
        c (destinationClockEmbedding N s p q)) =
      currentPairClockMeasure N r (stepDestination N s (some p)) := by
  letI : ∀ q : Other p, IsProbabilityMeasure (expMeasure (choiceRate N r s q.val)) :=
    fun q => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r q.val.1) (by norm_num))
  rw [actual_product_coordinate_projection _ (destinationClockEmbedding N s p)]
  rfl

/-- Actual source reset map retains the first winning time and exactly the
destination's CURRENT legal pair clocks. Old clocks incident to the removed
representative are discarded, including the winning/reversed orientations. -/
noncomputable def destinationResetMap (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    (Choice N s → ℝ) → ℝ × (Choice N (stepDestination N s (some p)) → ℝ) :=
  fun c => (c p,fun q => c (destinationClockEmbedding N s p q).val-c p)

/-- Coherent source endpoint: given an actual winning CURRENT original pair,
the actual merged destination's FULL clock catalogue is independently reset
at its SAME original rates and independent of the first winning time. This
is a full joint measure law, derived from literal clocks and actual mergers.
It still does not identify the entire multi-event timed/calendar path law. -/
theorem original_source_destination_clock_reset (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    ((currentPairClockMeasure N r s).restrict (winningRegion p)).map (destinationResetMap N s p) =
      (ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).prod
        (currentPairClockMeasure N r (stepDestination N s (some p))) := by
  letI : IsProbabilityMeasure (expMeasure (totalRate N r s)) := isProbabilityMeasure_expMeasure
    (UnifiedLean.Source.SourceFirstMarkDistribution.current_pair_total_positive N r s p)
  letI := Measure.smul_finite (expMeasure (totalRate N r s))
    (show ENNReal.ofReal (choiceRate N r s p/totalRate N r s) ≠ ∞ from ENNReal.ofReal_ne_top)
  letI : ∀ q : Other p, IsProbabilityMeasure (expMeasure (choiceRate N r s q.val)) :=
    fun q => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r q.val.1) (by norm_num))
  let project : (Other p → ℝ) → (Choice N (stepDestination N s (some p)) → ℝ) :=
    fun c q => c (destinationClockEmbedding N s p q)
  have hh := congrArg (fun mu : Measure (ℝ × (Other p → ℝ)) => mu.map (Prod.map id project))
    (original_current_winner_reset N r s p)
  rw [Measure.map_map (by fun_prop) (resetClock p).measurable,
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop),Measure.map_id,
    actual_destination_residual_product N r s p] at hh
  exact hh




end UnifiedLean.Source.SourceDestinationClockReset

end FullContextModule75

section FullContextModule76






/-!
# Actual source epoch renewal identity for the timed-clock path binding

Contributor: dot, 2026-10-02. The generator row is DERIVED from the actual
source PMF. The exponential's first-jump integral equation is then derived by
the fundamental theorem of calculus, matching the literal winning-clock law
and actual merged-state reset already proved. A timed path/kernel equality
must still be assembled; an integral/source-law identity is not an input.
-/
namespace UnifiedLean.Source.SourceEpochRenewal
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Matrix NormedSpace
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceGeneratorExponential
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual generator row action, retaining every CURRENT original pair and
its actual merged destination. No fitted/desired generator row is assumed. -/
theorem actual_generator_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample)
    (F : Matrix (Code N sample) (Code N sample) ℝ) :
    (sourceGeneratorMatrix N (sample := sample) r * F) s d =
      (∑ p : Choice N s, choiceRate N r s p * F (stepDestination N s (some p)) d) -
        totalRate N r s * F s d := by
  unfold sourceGeneratorMatrix
  rw [Matrix.smul_mul,Matrix.sub_mul,Matrix.one_mul]
  change globalRateBound (Copy := Copy) r *
    ((∑ z : Code N sample, (sourceStep N r s z).toReal * F z d) - F s d) = _
  rw [sourceStep_expectation N r s (fun z => F z d),Fintype.sum_option]
  simp only [choiceMass,stepDestination]
  have hne := (globalRateBound_positive (Copy := Copy) r).ne'
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp [hne]
  ring

lemma actual_exponential_entry_derivative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => (exp ((t-v) • sourceGeneratorMatrix N (sample := sample) r)) s d)
      (-(sourceGeneratorMatrix N (sample := sample) r *
        exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r)) s d) u := by
  let eval : Matrix (Code N sample) (Code N sample) ℝ →L[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ s d).toContinuousLinearMap
  have hm := (hasDerivAt_exp_smul_const' (sourceGeneratorMatrix N (sample := sample) r) (t-u)).scomp u
    ((hasDerivAt_const u t).sub (hasDerivAt_id u))
  have hh := eval.hasFDerivAt.comp_hasDerivAt u hm
  simpa only [eval,Function.comp_def,sub_self,zero_sub,neg_one_smul,ContinuousLinearMap.map_neg,
    LinearMap.coe_toContinuousLinearMap',Matrix.entryLinearMap_apply] using hh

lemma actual_renewal_derivative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-(totalRate N r s*v)) *
      (exp ((t-v) • sourceGeneratorMatrix N (sample := sample) r)) s d)
      (-(Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          (exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r))
            (stepDestination N s (some p)) d)) u := by
  have hE := actual_exponential_entry_derivative N r s d t u
  change HasDerivAt (fun v : ℝ => (exp ((t-v) • sourceGeneratorMatrix N (sample := sample) r)) s d)
    (-((sourceGeneratorMatrix N (sample := sample) r * exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r)) s d)) u at hE
  rw [actual_generator_row] at hE
  have he := ((hasDerivAt_id u).const_mul (-totalRate N r s)).exp
  simp only [mul_one,neg_mul,id_eq] at he
  have hh := he.mul hE
  convert hh using 1 <;> first | rfl | ring

/-- First-jump renewal is a CONSEQUENCE of the actual generator and matrix
exponential. Its density uses actual original pair rates and actual merged
destinations, exactly as the literal clock/reset law does. -/
theorem actual_source_exponential_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ) :
    (exp (t • sourceGeneratorMatrix N (sample := sample) r)) s d =
      Real.exp (-(totalRate N r s*t)) * (if s = d then 1 else 0) +
      ∫ u in 0..t, Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          (exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r))
            (stepDestination N s (some p)) d := by
  have hc : Continuous (fun u : ℝ => Real.exp (-(totalRate N r s*u)) *
      ∑ p : Choice N s, choiceRate N r s p *
        (exp ((t-u) • sourceGeneratorMatrix N (sample := sample) r))
          (stepDestination N s (some p)) d) := by
    apply Continuous.mul (by fun_prop)
    apply continuous_finsetSum
    intro p _
    exact continuous_const.mul (continuous_iff_continuousAt.mpr
      (fun u => (actual_exponential_entry_derivative N r (stepDestination N s (some p)) d t u).continuousAt))
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => actual_renewal_derivative N r s d t u) (hc.neg.intervalIntegrable 0 t)
  rw [intervalIntegral.integral_neg] at hh
  simp only [sub_self,zero_smul,exp_zero,Matrix.one_apply,mul_zero,neg_zero,
    Real.exp_zero,one_mul,sub_zero] at hh
  linarith

/-- The actual constructed PMF satisfies the same first-jump recursion with
its actual future source kernels, not just a conditional matrix identity.
On the integration interval the remaining duration is EXACTLY t-u. -/
theorem actual_source_kernel_first_jump (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ≥0) :
    (sourceTimeKernel N r t s d).toReal =
      Real.exp (-(totalRate N r s*(t : ℝ))) * (if s = d then 1 else 0) +
      ∫ u in 0..(t : ℝ), Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          (sourceTimeKernel N r (Real.toNNReal ((t : ℝ)-u))
            (stepDestination N s (some p)) d).toReal := by
  rw [source_time_kernel_eq_exponential,actual_source_exponential_renewal]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  have hut : u ≤ (t : ℝ) := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hu
    exact hu.2
  simp_rw [source_time_kernel_eq_exponential,Real.coe_toNNReal _ (sub_nonneg.mpr hut)]





end UnifiedLean.Source.SourceEpochRenewal

end FullContextModule76

section FullContextModule77


/-!
# Finite real-merger expansion of the actual ORIGINAL source epoch law

Contributor: dot, 2026-10-02. Expands the proved actual first-jump recursion
using literal original pair densities and actual destinations. Strict live
cardinality descent proves this finite recursive integral exactly equals the
actual source PMF once the budget reaches the supplied copy carrier size.
This is the connected analytic half of the literal clock-path binding;
measurable timed path pushforward and terminal observation are still pending.
-/
namespace UnifiedLean.Source.SourceFiniteJumpExpansion
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceEpochRenewal
open UnifiedLean.Source.SourceEpochSemigroup
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- A concrete finite first-jump density recursion. It uses the original
source destinations and densities, not an asserted transition law field. -/
noncomputable def finiteJumpMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Nat → ℝ≥0 → Code N sample → Code N sample → ℝ
  | 0,t,s,d => Real.exp (-(totalRate N r s*(t : ℝ))) * (if s = d then 1 else 0)
  | n+1,t,s,d => Real.exp (-(totalRate N r s*(t : ℝ))) * (if s = d then 1 else 0) +
      ∫ u in 0..(t : ℝ), Real.exp (-(totalRate N r s*u)) *
        ∑ p : Choice N s, choiceRate N r s p *
          finiteJumpMass N r n (Real.toNNReal ((t : ℝ)-u)) (stepDestination N s (some p)) d

lemma choice_empty_of_zero_live (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : liveCard s = 0) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := (Finset.mem_offDiag.mp p.2.property).1
  have hl := populationRoots_subset_live (state s) (originalPlace N p.1) hp
  have hc : (state s).live.card = 0 := hs
  rw [Finset.card_eq_zero] at hc
  rw [hc] at hl
  simpa using hl

/-- All real mergers lower the actual source's live-copy cardinality. Thus
the concrete finite clock-density recursion closes the ACTUAL entire epoch
transition law, without an unknown source-size budget or uniqueness premise. -/
theorem finite_jump_mass_eq_source_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (t : ℝ≥0) (s d : Code N sample)
    (hn : liveCard s ≤ n) : finiteJumpMass N r n t s d = (sourceTimeKernel N r t s d).toReal := by
  induction n generalizing t s with
  | zero =>
      have hs : liveCard s = 0 := by omega
      letI := choice_empty_of_zero_live N s hs
      rw [actual_source_kernel_first_jump]
      simp only [finiteJumpMass,Finset.univ_eq_empty,Finset.sum_empty,mul_zero,
        intervalIntegral.integral_zero,add_zero]
  | succ n ih =>
      rw [finiteJumpMass,actual_source_kernel_first_jump]
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      rw [ih _ (stepDestination N s (some p)) (by
        have hc := merger_destination_card N s p
        omega)]

/-- Uniform finite expansion for this SAME original supplied copy carrier.
This budget follows from source live IDs and does not bound an unknown G3
graph presentation or permit uncoupled rowwise fitting. -/
theorem original_copy_cap_jump_expansion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample) :
    finiteJumpMass N r (Fintype.card Copy) t s d = (sourceTimeKernel N r t s d).toReal :=
  finite_jump_mass_eq_source_kernel N r _ t s d (Finset.card_le_univ s.val.live)

/-- Nonnegativity and normalization of this concrete finite density expansion
are consequences of its proved actual-source equality, not input axioms. -/
theorem original_jump_expansion_stochastic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (∀ d : Code N sample, 0 ≤ finiteJumpMass N r (Fintype.card Copy) t s d) ∧
      (∑ d : Code N sample, finiteJumpMass N r (Fintype.card Copy) t s d) = 1 := by
  simp_rw [original_copy_cap_jump_expansion]
  exact ⟨fun _ => ENNReal.toReal_nonneg,pmf_sum_real _⟩




end UnifiedLean.Source.SourceFiniteJumpExpansion

end FullContextModule77

section FullContextModule78


/-!
# Measurable actual winning-coordinate selection for the source clock path

Contributor: dot, 2026-10-02. Strict winning regions are disjoint and their
ACTUAL exponential-product masses sum to one. The measurable selector's
failure event therefore has zero mass whenever the current catalogue is
nonempty. No arbitrary tie-breaker is given positive physical probability.
This is the path-map admission component, not yet its full pushforward law.
-/
namespace UnifiedLean.Source.SourceRaceWinnerSelection
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceExponentialRaceDensity
open UnifiedLean.Source.SourceWinningClockReset
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma winning_coordinate_unique (c : I → ℝ) {p q : I}
    (hp : c ∈ winningRegion p) (hq : c ∈ winningRegion q) : p = q := by
  by_contra hne
  exact (hp.2 ⟨q,Ne.symm hne⟩).asymm (hq.2 ⟨p,hne⟩)

lemma winning_regions_disjoint : _root_.Pairwise (fun p q : I => Disjoint (winningRegion p) (winningRegion q)) := by
  intro p q hne
  apply Set.disjoint_left.mpr
  intro c hp hq
  exact hne (winning_coordinate_unique c hp hq)

noncomputable def selectedWinner (c : I → ℝ) : Option I :=
  if h : ∃ p : I, c ∈ winningRegion p then some (Classical.choose h) else none

lemma selectedWinner_eq_some_iff (c : I → ℝ) (p : I) :
    selectedWinner c = some p ↔ c ∈ winningRegion p := by
  by_cases h : ∃ q : I, c ∈ winningRegion q
  · rw [selectedWinner,dif_pos h,Option.some.injEq]
    constructor
    · intro heq
      rw [← heq]
      exact Classical.choose_spec h
    · intro hp
      exact winning_coordinate_unique c (Classical.choose_spec h) hp
  · rw [selectedWinner,dif_neg h]
    constructor
    · intro hf; cases hf
    · intro hp; exact False.elim (h ⟨p,hp⟩)

lemma selectedWinner_none_preimage :
    (selectedWinner : (I → ℝ) → Option I) ⁻¹' {none} = (⋃ p : I, winningRegion p)ᶜ := by
  ext c
  simp only [mem_preimage,mem_singleton_iff,mem_compl_iff,mem_iUnion]
  by_cases h : ∃ q : I, c ∈ winningRegion q <;> simp [selectedWinner,h]

lemma selectedWinner_measurable [MeasurableSpace (Option I)] :
    Measurable (selectedWinner : (I → ℝ) → Option I) := by
  apply measurable_to_countable'
  intro z
  cases z with
  | none =>
      rw [selectedWinner_none_preimage]
      exact (MeasurableSet.iUnion measurable_winningRegion).compl
  | some p =>
      have hh : (selectedWinner : (I → ℝ) → Option I) ⁻¹' {some p} = winningRegion p := by
        ext c
        exact selectedWinner_eq_some_iff c p
      rw [hh]
      exact measurable_winningRegion p

lemma actual_winning_region_mass (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p : I) :
    (Measure.pi (fun i => expMeasure (rate i))) (winningRegion p) =
      ENNReal.ofReal (rate p/(∑ i, rate i)) := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  letI := isProbabilityMeasure_expMeasure (race_total_positive rate hr p)
  have hh := congrArg (fun mu : Measure (ℝ × (Other p → ℝ)) => mu univ)
    (actual_winner_reset_measure rate hr p)
  rw [(resetClock p).map_apply,preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter] at hh
  rw [← Set.univ_prod_univ,Measure.prod_prod,Measure.smul_apply,smul_eq_mul,
    measure_univ,measure_univ,mul_one,mul_one] at hh
  exact hh

/-- Every nonempty actual strictly-positive clock catalogue has a unique
strict winning coordinate almost surely. Ties/negative/pathological records
are excluded by a DERIVED zero-mass result, not an admission premise. -/
theorem actual_no_winner_null (rate : I → ℝ) (hr : ∀ i, 0 < rate i) (p0 : I) :
    (Measure.pi (fun i => expMeasure (rate i)))
      ((selectedWinner : (I → ℝ) → Option I) ⁻¹' {none}) = 0 := by
  letI : ∀ i : I, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  have htotal := race_total_positive rate hr p0
  have hm := MeasurableSet.iUnion (measurable_winningRegion (I := I))
  have hmass : (Measure.pi (fun i => expMeasure (rate i))) (⋃ p : I, winningRegion p) = 1 := by
    rw [measure_iUnion winning_regions_disjoint measurable_winningRegion,tsum_fintype]
    simp_rw [actual_winning_region_mass rate hr]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => div_nonneg (hr p).le htotal.le),
      ← Finset.sum_div,div_self htotal.ne',ENNReal.ofReal_one]
  rw [selectedWinner_none_preimage,measure_compl hm (measure_ne_top _ _),hmass,measure_univ,tsub_self]



end UnifiedLean.Source.SourceRaceWinnerSelection

end FullContextModule78

section FullContextModule79


/-!
# Actual ORIGINAL source embedded real-merger jump law

Contributor: dot, 2026-10-02. Constructs original current pair-rate fractions,
with absorption only when the actual legal catalogue is empty. The resulting
PMF is PROVED to be the literal independent exponential clock winner law.
This is the embedded event law used for unranked ancestral completion. Dummy
uniformization holds are not counted as mergers; no desired jump law is a
contract field. Full timed source strengthening remains a separate goal.
-/
namespace UnifiedLean.Source.SourceEmbeddedJumpLaw
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceRaceWinnerSelection
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance choiceOptionMeasurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : MeasurableSpace (Option (Choice N s)) := ⊤

noncomputable def jumpMass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : Option (Choice N s) → ℝ
  | none => if totalRate N r s = 0 then 1 else 0
  | some p => choiceRate N r s p/totalRate N r s

lemma jumpMass_nonnegative (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (q : Option (Choice N s)) :
    0 ≤ jumpMass N r s q := by
  cases q with
  | none => unfold jumpMass; split_ifs <;> norm_num
  | some p =>
      exact div_nonneg (div_pos (pairRate_pos r p.1) (by norm_num)).le
        (totalRate_nonnegative N r s)

lemma jumpMass_normalized (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (∑ q : Option (Choice N s), jumpMass N r s q) = 1 := by
  rw [Fintype.sum_option]
  simp only [jumpMass]
  by_cases hz : totalRate N r s = 0
  · simp [hz]
  · rw [if_neg hz,← Finset.sum_div]
    change 0+totalRate N r s/totalRate N r s = 1
    simp [hz]

/-- This PMF uses only actual original pair rates and their actual current
catalogue; the zero-rate row absorbs because no current pair exists. -/
noncomputable def sourceJumpChoice (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Option (Choice N s)) :=
  PMF.ofFintype (fun q => ENNReal.ofReal (jumpMass N r s q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => jumpMass_nonnegative N r s q),jumpMass_normalized]
    simp)

lemma sourceJumpChoice_apply (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (q : Option (Choice N s)) :
    sourceJumpChoice N r s q = ENNReal.ofReal (jumpMass N r s q) := PMF.ofFintype_apply _ _

lemma choice_empty_of_zero_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hz : totalRate N r s = 0) :
    IsEmpty (Choice N s) := ⟨fun p => (current_pair_total_positive N r s p).ne' hz⟩

lemma choice_nonempty_of_nonzero_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hz : totalRate N r s ≠ 0) :
    Nonempty (Choice N s) := by
  by_contra he
  letI : IsEmpty (Choice N s) := ⟨not_nonempty_iff_imp_false.mp he⟩
  exact hz (by simp [totalRate])

set_option maxHeartbeats 600000 in
/-- The source embedded-jump choice is EXACTLY the actual independent current
exponential-clock winner, including the genuine empty-catalogue absorption.
Tie/pathological branches have zero mass in every nonempty positive catalogue. -/
theorem original_clock_winner_eq_jump_choice (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (currentPairClockMeasure N r s).map selectedWinner = (sourceJumpChoice N r s).toMeasure := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  apply Measure.ext_of_singleton
  intro q
  rw [Measure.map_apply selectedWinner_measurable (measurableSet_singleton q),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton q),sourceJumpChoice_apply]
  cases q with
  | some p =>
      have hp : (selectedWinner : (Choice N s → ℝ) → Option (Choice N s)) ⁻¹' {some p} =
          UnifiedLean.Source.SourceWinningClockReset.winningRegion p := by
        ext c
        exact selectedWinner_eq_some_iff c p
      rw [hp]
      simpa only [currentPairClockMeasure,jumpMass,totalRate] using
        (actual_winning_region_mass (I := Choice N s) (choiceRate N r s)
          (fun q => div_pos (pairRate_pos r q.1) (by norm_num)) p)
  | none =>
      by_cases hz : totalRate N r s = 0
      · letI := choice_empty_of_zero_rate N r s hz
        have hc : (selectedWinner : (Choice N s → ℝ) → Option (Choice N s)) = fun _ => none := by
          funext c
          simp [selectedWinner]
        rw [hc]
        simp [jumpMass,hz,currentPairClockMeasure]
      · obtain ⟨p0⟩ := choice_nonempty_of_nonzero_rate N r s hz
        change (Measure.pi (fun q : Choice N s => expMeasure (choiceRate N r s q)))
          (selectedWinner ⁻¹' {none}) = _
        rw [actual_no_winner_null (choiceRate N r s)
          (fun q => div_pos (pairRate_pos r q.1) (by norm_num)) p0]
        simp [jumpMass,hz]

noncomputable def sourceJumpStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Code N sample) :=
  (sourceJumpChoice N r s).map (stepDestination N s)



end UnifiedLean.Source.SourceEmbeddedJumpLaw

end FullContextModule79

section FullContextModule80




/-!
# Current-owner original-site coins and stopped pair mixture

Contributor: dot, 2026-10-02. Every original hybrid has ONE source parameter;
each still-separate tip owner receives its own Bernoulli coin at that original
site. All potential coins are drawn independently of original holding clocks.
Unused seed bits are latent variables, never declared measured itinerary labels.
The surviving original-route readout marginalizes those unused bits by a finite
sum. This constructs the private/independent two-root law up to its first merger;
full multi-root reset dynamics and the serial-region observation adapter remain
separate obligations.
-/
namespace UnifiedLean.Source.NativeIndependentPairMixture
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- One parameter assignment on the unchanged original hybrid registry. -/
structure HybridProbabilities (N : RootedBinary V E X) where
  gamma : Hybrid N → ℝ
  positive : ∀ h, 0 < gamma h
  below_one : ∀ h, gamma h < 1

abbrev NativeCoinSeed (N : RootedBinary V E X) := (X × Hybrid N) → Bool

noncomputable def originalCoinMass (N : RootedBinary V E X)
    (p : HybridProbabilities N) (a : NativeCoinSeed N) : ℝ :=
  ∏ s : X × Hybrid N, if a s then p.gamma s.2 else 1-p.gamma s.2

lemma originalCoinMass_positive (N : RootedBinary V E X)
    (p : HybridProbabilities N) (a : NativeCoinSeed N) : 0 < originalCoinMass N p a := by
  apply Finset.prod_pos
  intro s _
  split_ifs
  · exact p.positive s.2
  · exact sub_pos.mpr (p.below_one s.2)

lemma originalCoinMass_normalized (N : RootedBinary V E X) (p : HybridProbabilities N) :
    (∑ a : NativeCoinSeed N, originalCoinMass N p a) = 1 := by
  unfold originalCoinMass
  rw [← Fintype.prod_sum (fun (s : X × Hybrid N) (b : Bool) =>
    if b then p.gamma s.2 else 1-p.gamma s.2)]
  have h : ∀ s : X × Hybrid N,
      (∑ b : Bool, if b then p.gamma s.2 else 1-p.gamma s.2) = 1 := by
    intro s
    simp
  simp only [h,Finset.prod_const_one]

noncomputable def originalCoinPMF (N : RootedBinary V E X)
    (p : HybridProbabilities N) : PMF (NativeCoinSeed N) :=
  PMF.ofFintype (fun a => ENNReal.ofReal (originalCoinMass N p a)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (originalCoinMass_positive N p a).le),
      originalCoinMass_normalized]
    simp)

noncomputable def seededRoutes (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : NativeCoinSeed N) : RouteFamily N :=
  compiledRouteFamily N C H (fun x h => a (x,h))

/-- Actual independent coin × original edge-clock source measure. -/
noncomputable def nativePairMeasure (N : RootedBinary V E X)
    (p : HybridProbabilities N) (r : PositivePairRates E) :
    Measure (NativeCoinSeed N × (Option E → ℝ)) :=
  (originalCoinPMF N p).toMeasure.prod (originalClockMeasure r)

/-- The predicate can depend on traversed ORIGINAL route IDs, not unobserved
coin labels. P=True is total survival; a route-record fiber is a measured
successful record. The observer discards all post-merger root logging. -/
def survivingReadoutEvent (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ)
    (P : NativeCoinSeed N → Prop) : Set (NativeCoinSeed N × (Option E → ℝ)) :=
  ⋃ a : NativeCoinSeed N, {a} ×ˢ
    (if P a then noFirstMerger N C (seededRoutes N C H a) x y t else ∅)

lemma noFirstMerger_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (R : RouteFamily N) (x y : X) (t : ℝ) :
    MeasurableSet (noFirstMerger N C R x y t) := by
  exact MeasurableSet.pi (Set.toFinite Set.univ).countable (fun e _ => measurableSet_Ioi)

lemma survivingReadoutEvent_measurable (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ)
    (P : NativeCoinSeed N → Prop) :
    MeasurableSet (survivingReadoutEvent N C H x y t P) := by
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.prod (measurableSet_singleton a)
  split_ifs
  · exact noFirstMerger_measurable N C _ x y t
  · exact MeasurableSet.empty

lemma survivingReadoutEvent_section (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (x y : X) (t : ℝ)
    (P : NativeCoinSeed N → Prop) (a : NativeCoinSeed N) :
    Prod.mk a ⁻¹' survivingReadoutEvent N C H x y t P =
      if P a then noFirstMerger N C (seededRoutes N C H a) x y t else ∅ := by
  ext clock
  simp only [survivingReadoutEvent,Set.mem_preimage,Set.mem_iUnion,Set.mem_prod,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨b,hab,hb⟩
    subst b
    exact hb
  · intro h
    exact ⟨a,rfl,h⟩

/-- Product-measure disintegration over the finite actual source seed. -/
theorem native_surviving_readout_mass (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (x y : X) (t : ℝ) (P : NativeCoinSeed N → Prop) :
    nativePairMeasure N p r (survivingReadoutEvent N C H x y t P) =
      ∑ a : NativeCoinSeed N, (originalCoinPMF N p a) *
        (if P a then originalClockMeasure r
          (noFirstMerger N C (seededRoutes N C H a) x y t) else 0) := by
  letI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  letI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [nativePairMeasure, Measure.prod_apply
    (survivingReadoutEvent_measurable N C H x y t P), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [survivingReadoutEvent_section,PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  split_ifs <;> simp [mul_comm]

/-- The unconditional pair probability is a source-derived finite mixture,
with no posterior replacement of the current-owner original hybrid coins.
Distinct owners enforce private/current-root semantics for this readout. -/
theorem below_root_native_pair_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (r : PositivePairRates E) (x y : X)
    (_different_current_owners : x ≠ y) {t : ℝ} (ht : t ≤ C.age N.root) :
    (nativePairMeasure N p r (survivingReadoutEvent N C H x y t (fun _ => True))).toReal =
      ∑ a : NativeCoinSeed N, originalCoinMass N p a *
        routeSurvival N C r.edge (seededRoutes N C H a) x y t := by
  letI : ∀ e : Option E, IsProbabilityMeasure (expMeasure (pairRate r e)) :=
    fun e => isProbabilityMeasure_expMeasure (pairRate_pos r e)
  letI : IsProbabilityMeasure (originalClockMeasure r) := by
    unfold originalClockMeasure
    infer_instance
  rw [native_surviving_readout_mass]
  simp only [if_true]
  rw [ENNReal.toReal_sum (by
    intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.toReal_mul,below_root_original_clock_law N C r _ x y ht]
  simp only [originalCoinPMF,PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (originalCoinMass_positive N p a).le]






end UnifiedLean.Source.NativeIndependentPairMixture

end FullContextModule80

section FullContextModule81



/-!
# Natural original-site initialization and unconditional calendar kernel

Contributor: dot, 2026-10-02. Reuses the existing strict ORIGINAL hybrid
probability assignment. A real independent original-site Bernoulli product
constructs latent shared registers once; CURRENT independent pulses use the
same original parameters freshly at their actual node. The unconditional
initialized calendar PMF and selected transport are constructed, rather than
assuming a desired marginal/source law. Unused registers remain latent; this
adds no observation/control menu. Ancestral completion and full holding-clock
path/unranked/timed observation equivalence remain further source obligations.
-/
namespace UnifiedLean.Source.SourceNaturalInitialization
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.UniformizedSourceStep
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Same strict original parameter assignment, with true = original parent1
as in the native source coin construction; no orientation silently changes. -/
noncomputable def originalGamma {N : RootedBinary V E X} (p : HybridProbabilities N)
    (h : Hybrid N) : unitInterval := ⟨p.gamma h,⟨(p.positive h).le,(p.below_one h).le⟩⟩

noncomputable def originalRegisterMeasure (N : RootedBinary V E X) (p : HybridProbabilities N) :
    Measure (Hybrid N → Bool) := Measure.pi (fun h => bitMeasure (originalGamma p h))

instance originalRegister_probability (N : RootedBinary V E X) (p : HybridProbabilities N) :
    IsProbabilityMeasure (originalRegisterMeasure N p) := by
  unfold originalRegisterMeasure
  infer_instance

/-- One register per actual original hybrid, reused by COMMON; nonhybrid
register slots are the inert false convention and are never independent coins. -/
noncomputable def originalRegister (N : RootedBinary V E X) (coin : Hybrid N → Bool) : V → Bool :=
  fun v => if hh : N.graph.IsHybrid v then coin ⟨v,hh⟩ else false

noncomputable def originalRegisterPMF (N : RootedBinary V E X) (p : HybridProbabilities N) : PMF (V → Bool) :=
  (originalRegisterMeasure N p).toPMF.map (originalRegister N)

/-- Natural full-copy calendar kernel conditional operations are assembled
with their SAME original-site parameter assignment and a once-drawn register. -/
noncomputable def naturalCalendarLaw (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E) : PMF (Code N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) common)
      (initialCode N sample register))

noncomputable def naturalSelectedCalendarLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (keep : Finset Copy) : PMF (SelectedIndex N sample keep) :=
  (originalRegisterPMF N p).bind (fun register =>
    selectedProgram N r keep (compiledCalendarProgram N C H (originalGamma p) common)
      (projection N keep (initialCode N sample register)))

/-- Unconditional whole selected-state law preserves ORIGINAL shared coupling
and natural CURRENT-root independent routing for all finite sample assignments. -/
theorem actual_natural_calendar_projection (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) (keep : Finset Copy) :
    (naturalCalendarLaw N C sample H p common r).map (projection N keep) =
      naturalSelectedCalendarLaw N C sample H p common r keep := by
  rw [naturalCalendarLaw,naturalSelectedCalendarLaw,PMF.map_bind]
  simp_rw [actual_source_program_projection]

/-- Natural register marginalization retains the derived complete initialized
physical-calendar support; all copies reach the same ORIGINAL ancestral root. -/
theorem natural_calendar_ancestral_support (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (naturalCalendarLaw N C sample H p common r).support) :
    ∀ x : Copy, copyLocation (state d) x = .rootPopulation N.root := by
  obtain ⟨register,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact initialized_original_calendar_ancestral_support N C sample register H (originalGamma p) common r hdr

/-- Arbitrary selected-state endpoint map is a derived probability transport,
not an assumed biological measurement/observed-law identification. -/
theorem natural_calendar_endpoint_probability {Obs : Type*}
    (N : RootedBinary V E X) (C : GProgram.G5.Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (keep : Finset Copy) (readout : SelectedIndex N sample keep → Obs) :
    (naturalCalendarLaw N C sample H p common r).map (readout ∘ projection N keep) =
      (naturalSelectedCalendarLaw N C sample H p common r keep).map readout := by
  rw [← PMF.map_comp,actual_natural_calendar_projection]





end UnifiedLean.Source.SourceNaturalInitialization

end FullContextModule81

section FullContextModule82



/-!
# Finite actual ORIGINAL ancestral merger completion

Contributor: dot, 2026-10-02. Reuses the accepted G2 generator/jump → calendar
→ ancestral-completion route at its UNRANKED endpoint scope. After the actual
calendar's proved root arrival, the actual exponential-winner jump PMF performs
source mergers until at most one live root remains. This is a genuine finite
PMF, with completion support DERIVED from original rates/root locations and
strict live-card descent. Eventual continuous-time limit and canonical
smaller-copy unranked transport remain separate connected obligations.
-/
namespace UnifiedLean.Source.SourceAncestralCompletion
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def AncestralRoot (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) : Prop :=
  ∀ x : Copy, copyLocation (state s) x = .rootPopulation N.root

lemma ancestral_live_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) {a : Copy} (ha : a ∈ (state s).live) :
    (state s).location a = .rootPopulation N.root := by
  have hrep : (state s).ancestor a = a := s.property.forest.representative a ha
  have hh := hs a
  change (state s).location ((state s).ancestor a) = .rootPopulation N.root at hh
  rw [hrep] at hh
  exact hh

lemma choice_empty_of_terminal_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hc : liveCard s ≤ 1) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  exact hp.different ((Finset.card_le_one.mp hc) _ hp.first_live _ hp.second_live)

lemma ancestral_choice_exists (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (hc : 1 < liveCard s) : Nonempty (Choice N s) := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hc
  refine ⟨⟨none,⟨(a,b),Finset.mem_offDiag.mpr ⟨?_,?_,hab⟩⟩⟩⟩
  · exact Finset.mem_filter.mpr ⟨ha,ancestral_live_location N s hs ha⟩
  · exact Finset.mem_filter.mpr ⟨hb,ancestral_live_location N s hs hb⟩

lemma ancestral_merger_preserved (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (p : Choice N s) :
    AncestralRoot N (stepDestination N s (some p)) := by
  intro x
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  unfold state stepDestination admittedCode
  rw [decode_encode_copyLocation,merge_population_preserved _ hm x]
  exact hs x

lemma source_jump_absorbs_terminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hc : liveCard s ≤ 1) :
    sourceJumpStep N r s = PMF.pure s := by
  letI := choice_empty_of_terminal_card N s hc
  have hz : totalRate N r s = 0 := by simp [totalRate]
  have hp : sourceJumpChoice N r s = PMF.pure none := by
    apply PMF.ext
    intro q
    cases q with
    | none => simp [sourceJumpChoice_apply,jumpMass,hz]
    | some p => exact isEmptyElim p
  rw [sourceJumpStep,hp,PMF.pure_map]
  rfl

lemma source_jump_support_cases (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceJumpStep N r s).support) :
    (d = s ∧ totalRate N r s = 0) ∨ ∃ p : Choice N s, d = stepDestination N s (some p) := by
  obtain ⟨q,hq,heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  cases q with
  | none =>
      left
      refine ⟨heq.symm,?_⟩
      by_contra hz
      have hn := (PMF.mem_support_iff _ _).mp hq
      rw [sourceJumpChoice_apply] at hn
      simp only [jumpMass,if_neg hz,ENNReal.ofReal_zero,ne_eq,not_true_eq_false] at hn
  | some p => exact Or.inr ⟨p,heq.symm⟩

noncomputable def ancestralCompletion (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Nat → Code N sample → PMF (Code N sample)
  | 0,s => PMF.pure s
  | n+1,s => (sourceJumpStep N r s).bind (ancestralCompletion N r n)

lemma ancestral_completion_fixed_terminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hc : liveCard s ≤ 1) :
    ancestralCompletion N r n s = PMF.pure s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ancestralCompletion,source_jump_absorbs_terminal N r s hc,PMF.pure_bind,ih]

/-- The original positive ancestral population completes after finitely many
actual merger jumps. No completion probability/support field is assumed. -/
theorem ancestral_completion_terminal_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hs : AncestralRoot N s)
    (hn : liveCard s ≤ n) {d : Code N sample}
    (hd : d ∈ (ancestralCompletion N r n s).support) : AncestralRoot N d ∧ liveCard d ≤ 1 := by
  induction n generalizing s with
  | zero =>
      have heq : d = s := by simpa only [ancestralCompletion,PMF.mem_support_pure_iff] using hd
      subst d
      exact ⟨hs,by omega⟩
  | succ n ih =>
      by_cases hc : liveCard s ≤ 1
      · rw [ancestral_completion_fixed_terminal N r (n+1) s hc] at hd
        have heq : d = s := by simpa only [PMF.mem_support_pure_iff] using hd
        subst d
        exact ⟨hs,hc⟩
      · obtain ⟨p0⟩ := ancestral_choice_exists N s hs (lt_of_not_ge hc)
        have hpos := current_pair_total_positive N r s p0
        obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
        rcases source_jump_support_cases N r s hm with ⟨_,hz⟩ | ⟨p,hp⟩
        · exact False.elim (hpos.ne' hz)
        · subst m
          exact ih _ (ancestral_merger_preserved N s hs p)
            (by have hcard := merger_destination_card N s p; omega) hdm

/-- A nonempty ORIGINAL copy carrier cannot end in an empty genealogy. -/
lemma admitted_live_card_positive [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : 0 < liveCard s := by
  obtain ⟨x⟩ := ‹Nonempty Copy›
  exact Finset.card_pos.mpr ⟨(state s).ancestor x,s.property.forest.ancestor_live x⟩

/-- Same original graph/parameters/register prior, now followed by genuine
ancestral merger completion. The finite PMF carries the complete old forests. -/
noncomputable def naturalCompletedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) : PMF (Code N sample) :=
  (naturalCalendarLaw N C sample H p common r).bind (ancestralCompletion N r (Fintype.card Copy))

/-- Actual graph-generated initialization and calendar, not an externally
supplied ancestral entry condition, yield exactly ONE final ancestral tree. -/
theorem natural_completed_one_tree_support [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) {d : Code N sample}
    (hd : d ∈ (naturalCompletedLaw N C sample H p common r).support) :
    AncestralRoot N d ∧ liveCard d = 1 := by
  obtain ⟨s,hs,hdc⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hroot := natural_calendar_ancestral_support N C sample H p common r hs
  obtain ⟨hr,hc⟩ := ancestral_completion_terminal_support N r (Fintype.card Copy) s hroot
    (Finset.card_le_univ s.val.live) hdc
  exact ⟨hr,by have hp := admitted_live_card_positive N d; omega⟩



end UnifiedLean.Source.SourceAncestralCompletion

end FullContextModule82

section FullContextModule83



/-!
# Actual labelled unranked genealogy observation

Contributor: dot (OpenAI), 2026-10-02.
Standard unordered-tree quotient mathematics is used, without a novelty claim.
The inherited original-copy Genealogy is quotiented only by recursively
generated child swaps. There is no associativity, leaf relabelling, or erasure
of binary ancestry topology. Actual selected-label pruning descends to this
quotient. A concrete finite unranked forest observer then instantiates the
already-derived natural calendar projection law.

This is an actual observer instance on the constructed finite source law.
Physical exponential winner/time/reset path identification, ancestral
completion, independently initialized smaller-copy law and timed observation
remain separate. No desired probability equality is a structure field.
-/
namespace UnifiedLean.Source.UnrankedGenealogyObservation
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceNaturalInitialization
open scoped Classical

variable {Copy : Type*} [DecidableEq Copy]

/-- Exact nonplane binary-tree equivalence: swaps at any graft, with only
equivalence closure and graft congruence. Labels and rooted topology remain. -/
inductive UnorderedEquiv : Genealogy Copy → Genealogy Copy → Prop
  | refl (a) : UnorderedEquiv a a
  | symm {a b} : UnorderedEquiv a b → UnorderedEquiv b a
  | trans {a b c} : UnorderedEquiv a b → UnorderedEquiv b c → UnorderedEquiv a c
  | graft {a b c d} : UnorderedEquiv a c → UnorderedEquiv b d →
      UnorderedEquiv (.graft a b) (.graft c d)
  | swap (a b) : UnorderedEquiv (.graft a b) (.graft b a)

def genealogySetoid : Setoid (Genealogy Copy) where
  r := UnorderedEquiv
  iseqv := ⟨UnorderedEquiv.refl, UnorderedEquiv.symm, UnorderedEquiv.trans⟩

abbrev UnrankedTree (Copy : Type*) := Quotient (genealogySetoid (Copy := Copy))

def toUnranked (a : Genealogy Copy) : UnrankedTree Copy := Quotient.mk _ a

theorem toUnranked_eq_iff (a b : Genealogy Copy) :
    toUnranked a = toUnranked b ↔ UnorderedEquiv a b :=
  Quotient.eq

theorem unordered_leaves {a b : Genealogy Copy} (h : UnorderedEquiv a b) :
    a.leaves = b.leaves := by
  induction h with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | graft _ _ ih1 ih2 => simp only [Genealogy.leaves, ih1, ih2]
  | swap a b => exact Finset.union_comm _ _

theorem unordered_wellLabelled {a b : Genealogy Copy} (h : UnorderedEquiv a b) :
    a.WellLabelled ↔ b.WellLabelled := by
  induction h with
  | refl a => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @graft a b c d h1 h2 ih1 ih2 =>
      simp only [Genealogy.WellLabelled, ih1, ih2, unordered_leaves h1, unordered_leaves h2]
  | swap a b =>
      constructor
      · rintro ⟨ha,hb,hd⟩; exact ⟨hb,ha,hd.symm⟩
      · rintro ⟨hb,ha,hd⟩; exact ⟨ha,hb,hd.symm⟩

def treeLeaves : UnrankedTree Copy → Finset Copy :=
  Quotient.lift Genealogy.leaves (fun _ _ h => unordered_leaves h)

def treeWellLabelled : UnrankedTree Copy → Prop :=
  Quotient.lift Genealogy.WellLabelled (fun _ _ h => propext (unordered_wellLabelled h))

/-- No extra erasure of original leaf labels is introduced by the quotient. -/
theorem toUnranked_equal_leaves {a b : Genealogy Copy}
    (h : toUnranked a = toUnranked b) : a.leaves = b.leaves :=
  unordered_leaves ((toUnranked_eq_iff a b).mp h)

def OptionEquiv : Option (Genealogy Copy) → Option (Genealogy Copy) → Prop
  | none, none => True
  | some a, some b => UnorderedEquiv a b
  | _, _ => False

lemma optionEquiv_refl (a : Option (Genealogy Copy)) : OptionEquiv a a := by
  cases a with
  | none => trivial
  | some a => exact UnorderedEquiv.refl a

lemma optionEquiv_symm {a b : Option (Genealogy Copy)} (h : OptionEquiv a b) :
    OptionEquiv b a := by
  cases a <;> cases b <;> simp only [OptionEquiv] at h ⊢
  all_goals first | trivial | exact UnorderedEquiv.symm h

lemma optionEquiv_trans {a b c : Option (Genealogy Copy)}
    (h1 : OptionEquiv a b) (h2 : OptionEquiv b c) : OptionEquiv a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptionEquiv] at h1 h2 ⊢
  all_goals first | trivial | contradiction | exact UnorderedEquiv.trans h1 h2

lemma joinPruned_respects {a b c d : Option (Genealogy Copy)}
    (h1 : OptionEquiv a c) (h2 : OptionEquiv b d) :
    OptionEquiv (Genealogy.joinPruned a b) (Genealogy.joinPruned c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [OptionEquiv, Genealogy.joinPruned] at h1 h2 ⊢
  all_goals first | trivial | contradiction | assumption | exact UnorderedEquiv.graft h1 h2

lemma joinPruned_swap (a b : Option (Genealogy Copy)) :
    OptionEquiv (Genealogy.joinPruned a b) (Genealogy.joinPruned b a) := by
  cases a <;> cases b <;> simp only [Genealogy.joinPruned, OptionEquiv]
  all_goals first | trivial | exact UnorderedEquiv.refl _ | exact UnorderedEquiv.swap _ _

/-- Selected-label restriction, including empty/unary suppression, is
well defined for exact rooted unranked binary genealogies. -/
theorem unordered_prune (keep : Finset Copy) {a b : Genealogy Copy}
    (h : UnorderedEquiv a b) : OptionEquiv (a.prune keep) (b.prune keep) := by
  induction h with
  | refl a => exact optionEquiv_refl _
  | symm _ ih => exact optionEquiv_symm ih
  | trans _ _ ih1 ih2 => exact optionEquiv_trans ih1 ih2
  | graft _ _ ih1 ih2 => exact joinPruned_respects ih1 ih2
  | swap a b => exact joinPruned_swap _ _

def optionUnranked (a : Option (Genealogy Copy)) : Option (UnrankedTree Copy) :=
  a.map toUnranked

lemma optionUnranked_eq {a b : Option (Genealogy Copy)} (h : OptionEquiv a b) :
    optionUnranked a = optionUnranked b := by
  cases a <;> cases b <;> simp only [OptionEquiv] at h
  all_goals first | rfl | exact congrArg some (Quotient.sound h)

def pruneTree (keep : Finset Copy) : UnrankedTree Copy → Option (UnrankedTree Copy) :=
  Quotient.lift (fun a => optionUnranked (a.prune keep))
    (fun _ _ h => optionUnranked_eq (unordered_prune keep h))

theorem prune_toUnranked (keep : Finset Copy) (a : Genealogy Copy) :
    pruneTree keep (toUnranked a) = optionUnranked (a.prune keep) := rfl

def optionTreeLeaves : Option (UnrankedTree Copy) → Finset Copy
  | none => ∅
  | some a => treeLeaves a

lemma optionUnranked_leaves (a : Option (Genealogy Copy)) :
    optionTreeLeaves (optionUnranked a) = Genealogy.optionLeaves a := by
  cases a <;> rfl

theorem pruneTree_leaves [Fintype Copy] (keep : Finset Copy) (a : UnrankedTree Copy) :
    optionTreeLeaves (pruneTree keep a) = treeLeaves a ∩ keep := by
  refine Quotient.inductionOn a ?_
  intro t
  change optionTreeLeaves (optionUnranked (t.prune keep)) = t.leaves ∩ keep
  rw [optionUnranked_leaves]
  exact Genealogy.prune_leaves keep t

variable {V E X : Type*} [Fintype Copy]

/-- A finite forest set of actual pruned unranked original-labelled trees.
Duplicate per-leaf records of one component are collapsed. Original population,
register, survivor IDs and global event history are not observations here. -/
noncomputable def unrankedForest (v : SelectedView V E Copy) : Finset (UnrankedTree Copy) :=
  Finset.univ.biUnion (fun x => match v.genealogy x with
    | none => ∅
    | some t => {toUnranked t})

noncomputable def sourceUnrankedForest (s : State V E Copy) (keep : Finset Copy) :
    Finset (UnrankedTree Copy) := unrankedForest (selectedView s keep)

lemma mem_unrankedForest (v : SelectedView V E Copy) (q : UnrankedTree Copy) :
    q ∈ unrankedForest v ↔
      ∃ x t, v.genealogy x = some t ∧ toUnranked t = q := by
  classical
  simp only [unrankedForest, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x,hx⟩
    cases ht : v.genealogy x with
    | none => simp [ht] at hx
    | some t =>
        have he : q = toUnranked t := by simpa [ht] using hx
        exact ⟨x,t,ht,he.symm⟩
  · rintro ⟨x,t,ht,rfl⟩
    exact ⟨x,by simp [ht]⟩

lemma mem_sourceUnrankedForest (s : State V E Copy) (keep : Finset Copy)
    (q : UnrankedTree Copy) : q ∈ sourceUnrankedForest s keep ↔
      ∃ x ∈ keep, ∃ t, (s.genealogy (s.ancestor x)).prune keep = some t ∧
        toUnranked t = q := by
  change q ∈ unrankedForest (selectedView s keep) ↔ _
  rw [mem_unrankedForest]
  constructor
  · rintro ⟨x,t,ht,hq⟩
    have hx : x ∈ keep := by
      by_contra hn
      simp [selectedView,selectedGenealogy,hn] at ht
    exact ⟨x,hx,t,by simpa [selectedView,selectedGenealogy,hx] using ht,hq⟩
  · rintro ⟨x,hx,t,ht,hq⟩
    exact ⟨x,t,by simpa [selectedView,selectedGenealogy,hx] using ht,hq⟩

lemma forest_member_live_witness (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {q : UnrankedTree Copy} (hq : q ∈ sourceUnrankedForest s keep) :
    ∃ l ∈ s.live, optionUnranked ((s.genealogy l).prune keep) = some q := by
  obtain ⟨x,hx,t,ht,hqt⟩ := (mem_sourceUnrankedForest s keep q).mp hq
  refine ⟨s.ancestor x,hs.ancestor_live x,?_⟩
  simp only [ht,optionUnranked,Option.map_some]
  exact congrArg some hqt

lemma treeLeaves_from_prune {t : Genealogy Copy} {keep : Finset Copy}
    {q : UnrankedTree Copy} (h : optionUnranked (t.prune keep) = some q) :
    treeLeaves q = t.leaves ∩ keep := by
  have hl := optionUnranked_leaves (t.prune keep)
  rw [h] at hl
  exact hl.trans (Genealogy.prune_leaves keep t)

/-- Every observed component is an actual well-labelled binary genealogy;
the observer does not create duplicate leaves or refitted components. -/
theorem source_unranked_forest_wellLabelled (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {q : UnrankedTree Copy} (hq : q ∈ sourceUnrankedForest s keep) :
    treeWellLabelled q := by
  obtain ⟨l,hl,hp⟩ := forest_member_live_witness s hs keep hq
  have hw := Genealogy.prune_wellLabelled keep (s.genealogy l) (hs.wellLabelled l hl)
  cases ht : (s.genealogy l).prune keep with
  | none => simp [ht,optionUnranked] at hp
  | some t =>
      have he : toUnranked t = q := by simpa [ht,optionUnranked] using hp
      rw [← he]
      change t.WellLabelled
      simpa only [ht,Genealogy.optionWellLabelled] using hw

/-- Exactly the selected original labels occur in the observed forest. -/
theorem source_unranked_forest_covers (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (x : Copy) :
    (∃ q ∈ sourceUnrankedForest s keep, x ∈ treeLeaves q) ↔ x ∈ keep := by
  constructor
  · rintro ⟨q,hq,hx⟩
    obtain ⟨l,hl,hp⟩ := forest_member_live_witness s hs keep hq
    rw [treeLeaves_from_prune hp] at hx
    exact (Finset.mem_inter.mp hx).2
  · intro hx
    have hxl : x ∈ (s.genealogy (s.ancestor x)).leaves :=
      (hs.leaf_fiber (s.ancestor x) (hs.ancestor_live x) x).mpr rfl
    have hpr := Genealogy.prune_leaves keep (s.genealogy (s.ancestor x))
    cases ht : (s.genealogy (s.ancestor x)).prune keep with
    | none =>
        rw [ht] at hpr
        have hi := Finset.mem_inter.mpr ⟨hxl,hx⟩
        rw [← hpr] at hi
        exact False.elim (Finset.notMem_empty x hi)
    | some t =>
        refine ⟨toUnranked t,(mem_sourceUnrankedForest s keep _).mpr ⟨x,hx,t,ht,rfl⟩,?_⟩
        rw [ht] at hpr
        change t.leaves = (s.genealogy (s.ancestor x)).leaves ∩ keep at hpr
        change x ∈ t.leaves
        rw [hpr]
        exact Finset.mem_inter.mpr ⟨hxl,hx⟩

/-- Distinct observed components partition the selected labels. The proof
uses the actual source leaf/ancestor fibres, not supplied partition metadata. -/
theorem source_unranked_forest_disjoint (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) {q r : UnrankedTree Copy}
    (hq : q ∈ sourceUnrankedForest s keep) (hr : r ∈ sourceUnrankedForest s keep)
    (hqr : q ≠ r) : Disjoint (treeLeaves q) (treeLeaves r) := by
  apply Finset.disjoint_left.mpr
  intro x hxq hxr
  obtain ⟨l,hl,hpl⟩ := forest_member_live_witness s hs keep hq
  obtain ⟨m,hm,hpm⟩ := forest_member_live_witness s hs keep hr
  rw [treeLeaves_from_prune hpl] at hxq
  rw [treeLeaves_from_prune hpm] at hxr
  have hxl := (hs.leaf_fiber l hl x).mp (Finset.mem_inter.mp hxq).1
  have hxm := (hs.leaf_fiber m hm x).mp (Finset.mem_inter.mp hxr).1
  have hlm : l = m := hxl.symm.trans hxm
  rw [← hlm] at hpm
  exact hqr (Option.some.inj (hpl.symm.trans hpm))

theorem sourceUnrankedForest_of_same_selectedView (s t : State V E Copy)
    (keep : Finset Copy) (h : selectedView s keep = selectedView t keep) :
    sourceUnrankedForest s keep = sourceUnrankedForest t keep := by
  unfold sourceUnrankedForest
  rw [h]

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- The supplied arbitrary-readout interface is now instantiated by an actual
unranked labelled forest observer on the constructed natural source law. -/
theorem natural_calendar_unranked_forest_law (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (keep : Finset Copy) :
    (naturalCalendarLaw N C sample H p common r).map
      (fun s => sourceUnrankedForest (state s) keep) =
    (naturalSelectedCalendarLaw N C sample H p common r keep).map
      (fun v => unrankedForest v.val) := by
  exact natural_calendar_endpoint_probability N C sample H p common r keep
    (fun v => unrankedForest v.val)











end UnifiedLean.Source.UnrankedGenealogyObservation

end FullContextModule83

section FullContextModule84



/-!
# Actual completed ORIGINAL rooted unranked tree law

Contributor: dot, 2026-10-02. Instantiates the inherited exact child-swap
quotient on the constructed natural calendar-plus-ancestral-merger law.
Its supported output is one well-labelled binary tree with EVERY original
copy label, not an arbitrary supplied endpoint observer/law. The remaining
G2 obligations are its eventual continuous-time limit and transport to the
independently initialized selected-copy source. Timed closure is not claimed.
-/
namespace UnifiedLean.Source.SourceCompletedUnrankedTree
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.UnrankedGenealogyObservation
open scoped Classical
variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]

lemma full_prune (t : Genealogy Copy) : t.prune Finset.univ = some t := by
  induction t with
  | leaf x => simp [Genealogy.prune]
  | graft a b iha ihb => simp only [Genealogy.prune,iha,ihb,Genealogy.joinPruned]

lemma one_live_ancestor {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (hc : s.live.card = 1) : ∃ a ∈ s.live, ∀ x : Copy, s.ancestor x = a := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  refine ⟨a,by rw [ha]; simp,?_⟩
  intro x
  have hx := hs.ancestor_live x
  simpa only [ha,Finset.mem_singleton] using hx

/-- Actual original-copy Valid fibres identify the completed tree's leaf set.
The observer discards only child order/hidden internal records, not leaf IDs. -/
theorem one_live_unranked_forest [Nonempty Copy] {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (hc : s.live.card = 1) :
    ∃ q : UnrankedTree Copy, sourceUnrankedForest s Finset.univ = {q} ∧
      treeWellLabelled q ∧ treeLeaves q = Finset.univ := by
  obtain ⟨a,ha,hanc⟩ := one_live_ancestor s hs hc
  refine ⟨toUnranked (s.genealogy a),?_,hs.wellLabelled a ha,?_⟩
  · ext q
    rw [mem_sourceUnrankedForest,Finset.mem_singleton]
    constructor
    · rintro ⟨x,_,t,ht,hq⟩
      rw [hanc x,full_prune] at ht
      have he : s.genealogy a = t := Option.some.inj ht
      exact hq.symm.trans (congrArg toUnranked he.symm)
    · intro hq
      obtain ⟨x⟩ := ‹Nonempty Copy›
      refine ⟨x,Finset.mem_univ x,s.genealogy a,?_,hq.symm⟩
      rw [hanc x,full_prune]
  · change (s.genealogy a).leaves = Finset.univ
    ext x
    rw [hs.leaf_fiber a ha x]
    simp [hanc x]

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

noncomputable def naturalCompletedUnrankedLaw (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E) :
    PMF (Finset (UnrankedTree Copy)) :=
  (naturalCompletedLaw N C sample H p common r).map
    (fun s => sourceUnrankedForest (state s) Finset.univ)

/-- Concrete end-to-end constructed original graph/calendar/prior/completion
output: every supported forest is exactly one complete original-labelled
rooted UNRANKED binary tree. No arbitrary measured-colour/endpoint field. -/
theorem natural_completed_unranked_tree_support [Nonempty Copy] (N : RootedBinary V E X)
    (C : GProgram.G5.Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    {F : Finset (UnrankedTree Copy)}
    (hF : F ∈ (naturalCompletedUnrankedLaw N C sample H p common r).support) :
    ∃ q : UnrankedTree Copy, F = {q} ∧ treeWellLabelled q ∧ treeLeaves q = Finset.univ := by
  obtain ⟨s,hs,hobs⟩ := (PMF.mem_support_map_iff _ _ _).mp hF
  have hcard := (natural_completed_one_tree_support N C sample H p common r hs).2
  obtain ⟨q,hq,hw,hl⟩ := one_live_unranked_forest (state s) s.property.forest hcard
  exact ⟨q,hobs.symm.trans hq,hw,hl⟩



end UnifiedLean.Source.SourceCompletedUnrankedTree

end FullContextModule84

section FullContextModule85



/-!
# Actual ORIGINAL ancestral source rank drift

Contributor: dot, 2026-10-02. For the eventual G2 unranked completion limit,
derive a positive source-dependent contraction from actual root pairs. No
uniform unknown-rival contraction or hidden graph budget is asserted. All
rates and current catalogues are the original source's actual parameters.
-/
namespace UnifiedLean.Source.SourceAncestralDrift
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourceAncestralCompletion
open scoped Classical BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def excessRank {N : RootedBinary V E X} {sample : Copy → X}
    (s : Code N sample) : ℝ := (liveCard s : ℝ)-1

lemma excessRank_nonnegative [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : 0 ≤ excessRank s := by
  have hp := admitted_live_card_positive N s
  unfold excessRank
  have hh : (1 : ℝ) ≤ (liveCard s : ℝ) := by exact_mod_cast hp
  linarith

/-- One actual root ancestor supplies a distinct legal clock with every other
current root. This proves a linear ORIGINAL ancestral-rate lower bound. -/
theorem actual_ancestral_total_rate_lower [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (r.ancestral/2) * excessRank s ≤ totalRate N r s := by
  obtain ⟨x⟩ := ‹Nonempty Copy›
  let a := (state s).ancestor x
  have ha : a ∈ (state s).live := s.property.forest.ancestor_live x
  let Others := {b : Copy // b ∈ (state s).live.erase a}
  let e : Others → Choice N s := fun b =>
    ⟨none,⟨(a,b.val),Finset.mem_offDiag.mpr
      ⟨Finset.mem_filter.mpr ⟨ha,ancestral_live_location N s hs ha⟩,
        Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp b.property).2,
          ancestral_live_location N s hs (Finset.mem_erase.mp b.property).2⟩,
        Ne.symm (Finset.mem_erase.mp b.property).1⟩⟩⟩
  have he : Function.Injective e := by
    intro b c h
    exact Subtype.ext (congrArg (fun p : Choice N s => p.2.val.2) h)
  have hsub : (∑ q ∈ Finset.univ.image e, choiceRate N r s q) ≤ totalRate N r s := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro q _ _
    exact (div_pos (pairRate_pos r q.1) (by norm_num)).le
  rw [Finset.sum_image (fun _ _ _ _ h => he h)] at hsub
  have hw : ∀ b : Others, choiceRate N r s (e b) = r.ancestral/2 := fun _ => rfl
  simp only [hw,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsub
  have hcard := Finset.card_erase_add_one ha
  have hc : ((state s).live.erase a).card = liveCard s-1 := by
    change _ + 1 = liveCard s at hcard
    omega
  have hcR : (((state s).live.erase a).card : ℝ) = excessRank s := by
    unfold excessRank
    have hh : ((((state s).live.erase a).card : ℝ)+1) = (liveCard s : ℝ) := by exact_mod_cast hcard
    linarith
  have hOthers : Fintype.card Others = ((state s).live.erase a).card := by
    dsimp [Others]
    exact Fintype.card_coe _
  rw [hOthers] at hsub
  rw [hcR,mul_comm] at hsub
  exact hsub

lemma merged_excessRank (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : excessRank (stepDestination N s (some p)) = excessRank s-1 := by
  have h := merger_destination_card N s p
  have hh : ((liveCard (stepDestination N s (some p)) : ℝ)+1) = (liveCard s : ℝ) := by exact_mod_cast h
  unfold excessRank
  linarith

/-- Exact rank drift of the ACTUAL normalized source PMF, not a fitted Markov
table or an assumed contraction. Dummy holds correctly contribute zero drift. -/
theorem actual_source_excessRank_expectation (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * excessRank d) =
      excessRank s-totalRate N r s/globalRateBound (Copy := Copy) r := by
  rw [sourceStep_expectation,Fintype.sum_option]
  simp only [choiceMass,merged_excessRank]
  change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*excessRank s +
    (∑ p : Choice N s, (choiceRate N r s p/globalRateBound (Copy := Copy) r)*(excessRank s-1)) = _
  rw [← Finset.sum_mul,← Finset.sum_div]
  change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*excessRank s +
    (totalRate N r s/globalRateBound (Copy := Copy) r)*(excessRank s-1) = _
  ring

/-- Fixed-source positive ancestral rate yields the necessary strict rank
contraction. Its constant depends on this original graph/rate/copy carrier;
it is not uniform over all unknown G4 rivals. -/
theorem actual_ancestral_excessRank_contraction [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (∑ d : Code N sample, (sourceStep N r s d).toReal * excessRank d) ≤
      (1-(r.ancestral/2)/globalRateBound (Copy := Copy) r)*excessRank s := by
  rw [actual_source_excessRank_expectation]
  have hbound := div_le_div_of_nonneg_right (actual_ancestral_total_rate_lower N r s hs)
    (globalRateBound_positive (Copy := Copy) r).le
  have hb : ((r.ancestral/2)/globalRateBound (Copy := Copy) r)*excessRank s ≤
      totalRate N r s/globalRateBound (Copy := Copy) r := by
    have heq : ((r.ancestral/2)/globalRateBound (Copy := Copy) r)*excessRank s =
        ((r.ancestral/2)*excessRank s)/globalRateBound (Copy := Copy) r := by ring
    rw [heq]
    exact hbound
  nlinarith




end UnifiedLean.Source.SourceAncestralDrift

end FullContextModule85

section FullContextModule86



/-!
# Quantitative absorption of the actual original ancestral source

Contributor: dot, 2026-10-02. Derives finite-step and physical-time transient
bounds from the actual root catalogue, original positive ancestral rate and
constructed source PMFs. This is the connected eventual-completion gate, with
no uniform unknown-rival rate or effective hidden graph budget assumed.
-/
namespace UnifiedLean.Source.SourceAncestralAbsorption
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceAncestralDrift
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma finite_bind_expectation {A B : Type*} [Fintype A] [Fintype B]
    (p : PMF A) (f : A → PMF B) (F : B → ℝ) :
    (∑ b : B, ((p.bind f) b).toReal * F b) =
      ∑ a : A, (p a).toReal * (∑ b : B, (f a b).toReal * F b) := by
  simp_rw [bind_probability_real,tsum_fintype,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

noncomputable def contractionRatio (r : PositivePairRates E) : ℝ :=
  1-(r.ancestral/2)/globalRateBound (Copy := Copy) r

lemma contractionRatio_bounds (r : PositivePairRates E) :
    0 ≤ contractionRatio (Copy := Copy) r ∧ contractionRatio (Copy := Copy) r < 1 := by
  have hr : r.ancestral ≤ ∑ i : Option E, pairRate r i := by
    exact Finset.single_le_sum (fun i _ => (pairRate_pos r i).le) (Finset.mem_univ none)
  have hsum : 0 ≤ ∑ i : Option E, pairRate r i :=
    Finset.sum_nonneg (fun i _ => (pairRate_pos r i).le)
  have hν : r.ancestral/2 ≤ globalRateBound (Copy := Copy) r := by
    unfold globalRateBound
    nlinarith [sq_nonneg (Fintype.card Copy : ℝ),r.ancestral_pos]
  have hdiv := (div_le_one (globalRateBound_positive (Copy := Copy) r)).mpr hν
  have hpos := div_pos (show 0 < r.ancestral/2 by linarith [r.ancestral_pos])
    (globalRateBound_positive (Copy := Copy) r)
  unfold contractionRatio
  constructor <;> linarith

lemma ancestral_step_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    {d : Code N sample} (hd : d ∈ (sourceStep N r s).support) : AncestralRoot N d := by
  obtain ⟨q,_,hq⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hq]
  cases q with
  | none => exact hs
  | some p => exact ancestral_merger_preserved N s hs p

/-- Actual source iterations preserve original ancestral locations. -/
lemma ancestral_iteration_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) (hs : AncestralRoot N s)
    {d : Code N sample} (hd : d ∈ (sourceIteration N r k s).support) : AncestralRoot N d := by
  induction k generalizing s with
  | zero =>
      have h : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      simpa [h] using hs
  | succ k ih =>
      obtain ⟨m,hm,hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih m (ancestral_step_support N r s hs hm) hdm

/-- Source-derived geometric drift, for every original root state and number
of genuine uniformization trials. Holds are included with their actual mass. -/
theorem actual_ancestral_iteration_rank_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (k : Nat) (s : Code N sample)
    (hs : AncestralRoot N s) :
    (∑ d : Code N sample, (sourceIteration N r k s d).toReal * excessRank d) ≤
      contractionRatio (Copy := Copy) r ^ k * excessRank s := by
  have hq := (contractionRatio_bounds (Copy := Copy) r).1
  induction k generalizing s with
  | zero => simp [sourceIteration,PMF.pure_apply,apply_ite]
  | succ k ih =>
      rw [sourceIteration,finite_bind_expectation]
      calc
        _ ≤ ∑ m : Code N sample, (sourceStep N r s m).toReal *
            (contractionRatio (Copy := Copy) r ^ k * excessRank m) := by
          apply Finset.sum_le_sum
          intro m _
          by_cases hm : m ∈ (sourceStep N r s).support
          · exact mul_le_mul_of_nonneg_left (ih m (ancestral_step_support N r s hs hm))
              ENNReal.toReal_nonneg
          · have hz : sourceStep N r s m = 0 := by simpa only [PMF.mem_support_iff,not_not] using hm
            simp [hz]
        _ = contractionRatio (Copy := Copy) r ^ k *
            (∑ m : Code N sample, (sourceStep N r s m).toReal * excessRank m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
        _ ≤ contractionRatio (Copy := Copy) r ^ k *
            (contractionRatio (Copy := Copy) r * excessRank s) :=
          mul_le_mul_of_nonneg_left (actual_ancestral_excessRank_contraction N r s hs)
            (pow_nonneg hq k)
        _ = _ := by rw [pow_succ]; ring

/-- Any still-uncoalesced original source state has probability bounded by
actual expected excess rank, hence by the source-derived geometric factor. -/
theorem actual_ancestral_iteration_transient_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (k : Nat) (s d : Code N sample)
    (hs : AncestralRoot N s) (hd : 1 < liveCard d) :
    (sourceIteration N r k s d).toReal ≤ contractionRatio (Copy := Copy) r ^ k * excessRank s := by
  have hr : (1 : ℝ) ≤ excessRank d := by
    unfold excessRank
    have hh : (2 : ℝ) ≤ (liveCard d : ℝ) := by exact_mod_cast hd
    linarith
  calc
    _ ≤ (sourceIteration N r k s d).toReal * excessRank d := by
      nlinarith [show 0 ≤ (sourceIteration N r k s d).toReal from ENNReal.toReal_nonneg]
    _ ≤ ∑ z : Code N sample, (sourceIteration N r k s z).toReal * excessRank z :=
      Finset.single_le_sum (fun z _ => mul_nonneg ENNReal.toReal_nonneg (excessRank_nonnegative N z))
        (Finset.mem_univ d)
    _ ≤ _ := actual_ancestral_iteration_rank_bound N r k s hs

/-- The actual Poisson/source epoch has exponentially vanishing transient
mass. The rate is the ORIGINAL positive ancestral rate, not an asserted
absorption law or a rate uniform over unknown graphs. -/
theorem actual_ancestral_time_transient_bound [Nonempty Copy] (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s d : Code N sample)
    (hs : AncestralRoot N s) (hd : 1 < liveCard d) :
    (sourceTimeKernel N r t s d).toReal ≤ excessRank s * Real.exp (-(r.ancestral/2*(t : ℝ))) := by
  let a : ℝ := globalRateBound (Copy := Copy) r * (t : ℝ)
  let q := contractionRatio (Copy := Copy) r
  have hsum : HasSum (fun k : Nat =>
      (Real.exp (-a) * a^k / k.factorial) * (q^k * excessRank s))
      (Real.exp (-a) * Real.exp (a*q) * excessRank s) := by
    simpa only [mul_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm,← Real.exp_eq_exp_ℝ]
      using ((NormedSpace.expSeries_div_hasSum_exp (a*q)).mul_left (Real.exp (-a))).mul_right (excessRank s)
  have hnon : ∀ k : Nat, 0 ≤ (countPMF (globalClockRate (Copy := Copy) r*t) k).toReal *
      (sourceIteration N r k s d).toReal := fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hle : ∀ k : Nat, (countPMF (globalClockRate (Copy := Copy) r*t) k).toReal *
      (sourceIteration N r k s d).toReal ≤
      (Real.exp (-a)*a^k/k.factorial)*(q^k*excessRank s) := by
    intro k
    have hh := mul_le_mul_of_nonneg_left (actual_ancestral_iteration_transient_bound N r k s d hs hd)
      (show 0 ≤ (countPMF (globalClockRate (Copy := Copy) r*t) k).toReal from ENNReal.toReal_nonneg)
    rw [countPMF_real] at hh
    change (Real.exp (-a)*a^k/k.factorial)*(sourceIteration N r k s d).toReal ≤
      (Real.exp (-a)*a^k/k.factorial)*(q^k*excessRank s) at hh
    rw [countPMF_real]
    exact hh
  rw [sourceTimeKernel,bind_probability_real]
  calc
    _ ≤ ∑' k : Nat, (Real.exp (-a)*a^k/k.factorial)*(q^k*excessRank s) :=
      (hsum.summable.of_nonneg_of_le hnon hle).tsum_le_tsum hle hsum.summable
    _ = Real.exp (-a) * Real.exp (a*q) * excessRank s := hsum.tsum_eq
    _ = _ := by
      rw [← Real.exp_add,mul_comm _ (excessRank s)]
      congr 2
      dsimp [a,q,contractionRatio]
      have hν := (globalRateBound_positive (Copy := Copy) r).ne'
      field_simp [hν]
      ring




end UnifiedLean.Source.SourceAncestralAbsorption

end FullContextModule86

section FullContextModule87


/-!
# Actual ancestral completion is harmonic for the ORIGINAL source kernel

Contributor: dot, 2026-10-02. The finite winner-jump completion is proved
stable and harmonic for the actual uniformized/Poisson source, not supplied
as a desired terminal law. Together with source-derived transient decay this
identifies the eventual unranked ancestral law.
-/
namespace UnifiedLean.Source.SourceCompletionHarmonic
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceFirstMarkDistribution
open UnifiedLean.Source.SourceStepGeneratorBinding
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceAncestralAbsorption
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma bind_congr_on_support {A B : Type*} (p : PMF A) (f g : A → PMF B)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  apply PMF.ext
  intro b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · have hz : p a = 0 := by simpa only [PMF.mem_support_iff,not_not] using ha
    simp [hz]

/-- Completion is stable after the proved original live-card budget. -/
theorem ancestral_completion_stabilizes (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hs : AncestralRoot N s)
    (hn : liveCard s ≤ n) : ancestralCompletion N r (n+1) s = ancestralCompletion N r n s := by
  induction n generalizing s with
  | zero =>
      have hc : liveCard s ≤ 1 := by omega
      rw [ancestral_completion_fixed_terminal N r 1 s hc,ancestral_completion_fixed_terminal N r 0 s hc]
  | succ n ih =>
      by_cases hc : liveCard s ≤ 1
      · rw [ancestral_completion_fixed_terminal N r (n+1+1) s hc,
          ancestral_completion_fixed_terminal N r (n+1) s hc]
      · change (sourceJumpStep N r s).bind (ancestralCompletion N r (n+1)) =
          (sourceJumpStep N r s).bind (ancestralCompletion N r n)
        apply bind_congr_on_support
        intro d hd
        rcases source_jump_support_cases N r s hd with ⟨_,hz⟩ | ⟨p,hp⟩
        · obtain ⟨p0⟩ := ancestral_choice_exists N s hs (lt_of_not_ge hc)
          exact False.elim ((current_pair_total_positive N r s p0).ne' hz)
        · subst d
          exact ih _ (ancestral_merger_preserved N s hs p)
            (by have hh := merger_destination_card N s p; omega)

noncomputable def completionKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : PMF (Code N sample) :=
  ancestralCompletion N r (Fintype.card Copy) s

lemma completion_jump_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceJumpStep N r s).bind (completionKernel N r) = completionKernel N r s := by
  exact ancestral_completion_stabilizes N r (Fintype.card Copy) s hs (Finset.card_le_univ s.val.live)

lemma completion_terminal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : liveCard s ≤ 1) :
    completionKernel N r s = PMF.pure s := ancestral_completion_fixed_terminal N r _ s hs

/-- Completion is harmonic for actual normalized source steps, including
all genuine hold mass. The identity is derived from original rate fractions. -/
theorem completion_source_step_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceStep N r s).bind (completionKernel N r) = completionKernel N r s := by
  have hj := completion_jump_harmonic N r s hs
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,tsum_fintype,sourceStep_expectation,Fintype.sum_option]
  simp only [choiceMass]
  by_cases hz : totalRate N r s = 0
  · letI := choice_empty_of_zero_rate N r s hz
    simp [hz,stepDestination]
  · have he := congrArg (fun p : PMF (Code N sample) => (p z).toReal) hj
    rw [sourceJumpStep,PMF.bind_map,bind_probability_real,tsum_fintype,Fintype.sum_option] at he
    simp_rw [sourceJumpChoice_apply,ENNReal.toReal_ofReal (jumpMass_nonnegative N r s _)] at he
    simp only [jumpMass,if_neg hz,zero_mul,zero_add,Function.comp_apply] at he
    have hsums : (∑ p : Choice N s, choiceRate N r s p *
        (completionKernel N r (stepDestination N s (some p)) z).toReal) =
        totalRate N r s * (completionKernel N r s z).toReal := by
      simp_rw [div_mul_eq_mul_div] at he
      rw [← Finset.sum_div] at he
      exact ((div_eq_iff hz).mp he).trans (mul_comm _ _)
    change (1-totalRate N r s/globalRateBound (Copy := Copy) r)*
        (completionKernel N r s z).toReal +
        (∑ p : Choice N s, (choiceRate N r s p/globalRateBound (Copy := Copy) r)*
          (completionKernel N r (stepDestination N s (some p)) z).toReal) = _
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div,hsums]
    ring

/-- The completed actual jump law is invariant under every actual source
iteration, using ancestral support rather than a globally asserted row law. -/
theorem completion_source_iteration_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (k : Nat) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceIteration N r k s).bind (completionKernel N r) = completionKernel N r s := by
  induction k generalizing s with
  | zero => simp [sourceIteration]
  | succ k ih =>
      rw [sourceIteration,PMF.bind_bind]
      calc
        _ = (sourceStep N r s).bind (completionKernel N r) := by
          apply bind_congr_on_support
          intro d hd
          exact ih d (ancestral_step_support N r s hs hd)
        _ = _ := completion_source_step_harmonic N r s hs

/-- Exact source-time kernel followed by actual completion equals the same
completed original-source law, for every nonnegative ancestral duration. -/
theorem completion_source_time_harmonic (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceTimeKernel N r t s).bind (completionKernel N r) = completionKernel N r s := by
  rw [sourceTimeKernel,PMF.bind_bind]
  simp_rw [completion_source_iteration_harmonic N r _ s hs]
  exact PMF.bind_const _ _





end UnifiedLean.Source.SourceCompletionHarmonic

end FullContextModule87

section FullContextModule88


/-!
UNCHECKED additive derivative, CLOUD-G6-SOL-ULTRA-20261007, 2026-10-07.
Specializes the original actual jump/completion kernels on AncestralRoot.
Classical uniform pair choice is prior; this file connects its rate cancellation
and rational row formula to the SAME source Code/merger/completion definitions.
No equality of unbinned waiting ages or executable enumeration is claimed.
-/
namespace UnifiedLean.G6.AncestralRateFree
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceEmbeddedJumpLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.SourceCompletionHarmonic
open scoped Classical BigOperators

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma ancestral_choice_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (p : Choice N s) : p.1 = none := by
  have hp : p.2.val.1 ∈ populationRoots (state s) (originalPlace N p.1) :=
    (Finset.mem_offDiag.mp p.2.property).1
  have hm := Finset.mem_filter.mp hp
  have hloc : Location.rootPopulation N.root = originalPlace N p.1 :=
    (ancestral_live_location N s hs hm.1).symm.trans hm.2
  cases hi : p.1 with
  | none => rfl
  | some e =>
    have hbad : Location.rootPopulation N.root = Location.edge e := by
      simpa only [hi, originalPlace] using hloc
    cases hbad

lemma ancestral_choice_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    (p : Choice N s) : choiceRate N r s p = pairRate r none / 2 := by
  unfold choiceRate
  rw [ancestral_choice_population N s hs p]

lemma ancestral_total_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    totalRate N r s = (Fintype.card (Choice N s) : ℝ) * (pairRate r none / 2) := by
  unfold totalRate
  simp_rw [ancestral_choice_rate N r s hs]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A formula on the SAME ordered Choice carrier, with terminal holding. -/
noncomputable def ancestralChoiceMass (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Option (Choice N s) → ℝ
  | none => if Fintype.card (Choice N s) = 0 then 1 else 0
  | some _ => 1 / (Fintype.card (Choice N s) : ℝ)

lemma ancestral_jump_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    (q : Option (Choice N s)) : jumpMass N r s q = ancestralChoiceMass N s q := by
  have hroot : pairRate r none ≠ 0 := ne_of_gt (pairRate_pos r none)
  have hr : pairRate r none / 2 ≠ 0 := ne_of_gt (div_pos (pairRate_pos r none) (by norm_num))
  have hz : totalRate N r s = 0 ↔ Fintype.card (Choice N s) = 0 := by
    rw [ancestral_total_rate N r s hs, mul_eq_zero]
    simp only [hr, or_false, Nat.cast_eq_zero]
  cases q with
  | none => simp only [jumpMass, hz, ancestralChoiceMass]
  | some p =>
    letI : Nonempty (Choice N s) := ⟨p⟩
    have hc : (Fintype.card (Choice N s) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Choice N s) ≠ 0)
    rw [jumpMass, ancestral_choice_rate N r s hs p, ancestral_total_rate N r s hs]
    dsimp only [ancestralChoiceMass]
    field_simp [hc, hr, hroot]

noncomputable def rationalAncestralChoiceMass (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) : Option (Choice N s) → ℚ
  | none => if Fintype.card (Choice N s) = 0 then 1 else 0
  | some _ => 1 / (Fintype.card (Choice N s) : ℚ)

lemma rational_ancestral_choice_mass_actual (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) (q : Option (Choice N s)) :
    (rationalAncestralChoiceMass N s q : ℝ) = jumpMass N r s q := by
  rw [ancestral_jump_mass N r s hs q]
  cases q with
  | none =>
    by_cases hc : Fintype.card (Choice N s) = 0
    · simp only [rationalAncestralChoiceMass, ancestralChoiceMass, if_pos hc, Rat.cast_one]
    · simp only [rationalAncestralChoiceMass, ancestralChoiceMass, if_neg hc, Rat.cast_zero]
  | some p => simp [rationalAncestralChoiceMass, ancestralChoiceMass]

lemma ancestral_jump_choice_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) : sourceJumpChoice N r s = sourceJumpChoice N rhat s := by
  apply PMF.ext
  intro q
  rw [sourceJumpChoice_apply, sourceJumpChoice_apply,
    ancestral_jump_mass N r s hs q, ancestral_jump_mass N rhat s hs q]

lemma ancestral_jump_step_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) : sourceJumpStep N r s = sourceJumpStep N rhat s := by
  rw [sourceJumpStep, sourceJumpStep, ancestral_jump_choice_rate_invariant N r rhat s hs]

theorem ancestral_completion_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (k : ℕ)
    (s : Code N sample) (hs : AncestralRoot N s) :
    ancestralCompletion N r k s = ancestralCompletion N rhat k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [ancestralCompletion, ancestralCompletion,
      ancestral_jump_step_rate_invariant N r rhat s hs]
    apply bind_congr_on_support
    intro d hd
    rcases source_jump_support_cases N rhat s hd with ⟨he, _⟩ | ⟨p, he⟩
    · subst d
      exact ih s hs
    · subst d
      exact ih _ (ancestral_merger_preserved N s hs p)

theorem completion_kernel_rate_invariant (N : RootedBinary V E X)
    {sample : Copy → X} (r rhat : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) : completionKernel N r s = completionKernel N rhat s :=
  ancestral_completion_rate_invariant N r rhat (Fintype.card Copy) s hs










end UnifiedLean.G6.AncestralRateFree

end FullContextModule88

section FullContextModule89






/-! Actual arbitrary-copy single-population epoch as a rational polynomial in the
one physical survival coordinate. Source counting, real-merger recursion and
ordered-pair normalization are retained. Contributor: dot,2026-10-09.
Every original edge occurrence and the ancestral root are included.
This one-population gate does not establish the full G7 graph compiler. -/
namespace GProgram.G7.SinglePopulationPolynomialKernel
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceEpochRenewal UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.G6.AncestralRateFree
open UnifiedLean.Source.FiniteSourceSnapshot
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Every original copy currently belongs to one specified physical original
population. Its carried genealogy and original latent register are unchanged. -/
def CoLocated (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) : Prop :=
  ∀ x : Copy, copyLocation (state s) x = originalPlace N i

lemma population_live_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    {a : Copy} (ha : a ∈ (state s).live) :
    (state s).location a = originalPlace N i := by
  have hr : (state s).ancestor a = a := s.property.forest.representative a ha
  have hh := hs a
  change (state s).location ((state s).ancestor a) = _ at hh
  rw [hr] at hh
  exact hh

lemma population_roots (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    populationRoots (state s) (originalPlace N i) = (state s).live := by
  apply Finset.filter_eq_self.mpr
  intro a ha
  exact population_live_location N s i hs ha

lemma originalPlace_injective (N : RootedBinary V E X) :
    Function.Injective (originalPlace N) := by
  intro a b h
  cases a <;> cases b <;> simp_all [originalPlace]

lemma population_choice (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (p : Choice N s) : p.1 = i := by
  have ha := (Finset.mem_offDiag.mp p.2.property).1
  have hh := Finset.mem_filter.mp ha
  apply originalPlace_injective N
  exact hh.2.symm.trans (population_live_location N s i hs hh.1)

lemma population_choice_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E)
    (hs : CoLocated N s i) (p : Choice N s) :
    choiceRate N r s p = pairRate r i / 2 := by
  unfold choiceRate
  rw [population_choice N s i hs p]

noncomputable def populationChoices (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    Choice N s ≃ {p : Copy × Copy // p ∈ (state s).live.offDiag} where
  toFun p := ⟨p.2.val,by
    rcases Finset.mem_offDiag.mp p.2.property with ⟨ha,hb,hab⟩
    exact Finset.mem_offDiag.mpr ⟨populationRoots_subset_live _ _ ha,
      populationRoots_subset_live _ _ hb,hab⟩⟩
  invFun p := ⟨i,⟨p.val,by simpa [population_roots N s i hs] using p.property⟩⟩
  left_inv p := by
    rcases p with ⟨j,p⟩
    have hj : j = i := population_choice N s i hs ⟨j,p⟩
    subst j
    rfl
  right_inv p := rfl

lemma population_choice_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    Fintype.card (Choice N s) = liveCard s * (liveCard s - 1) := by
  rw [Fintype.card_congr (populationChoices N s i hs),Fintype.card_coe,Finset.offDiag_card]
  simp only [liveCard,Nat.mul_sub_one]
  rfl

lemma actual_population_holding_rate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    totalRate N r s = pairRate r i * ((liveCard s).choose 2 : ℝ) := by
  unfold totalRate
  simp_rw [population_choice_rate N r s i hs]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [population_choice_card N s i hs]
  have hn : liveCard s * (liveCard s-1) = 2 * (liveCard s).choose 2 := by
    rw [Nat.choose_two_right]
    exact (Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self (liveCard s))).symm
  have hr : ((liveCard s * (liveCard s-1) : ℕ) : ℝ) =
      2 * ((liveCard s).choose 2 : ℝ) := by exact_mod_cast hn
  rw [hr]
  ring

lemma population_merger_preserved (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) (p : Choice N s) :
    CoLocated N (stepDestination N s (some p)) i := by
  intro x
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  unfold state stepDestination admittedCode
  rw [UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_copyLocation,
    merge_population_preserved _ hm x]
  exact hs x

lemma actual_terminal_epoch (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s d : Code N sample) (t : ℝ≥0)
    (hk : liveCard s ≤ 1) :
    (sourceTimeKernel N r t s d).toReal = if s = d then 1 else 0 := by
  letI := choice_empty_of_terminal_card N s hk
  rw [actual_source_kernel_first_jump]
  simp [totalRate]

/-- Exact ordered-pair convolution. The half rate is retained. This formula
is valid even at zero duration; it uses no limiting or numerical comparison. -/
lemma damped_monomial_integral (n m rho a t : ℝ) (hnm : n ≠ m) :
    (∫ u in (0:ℝ)..t, Real.exp (-n*rho*u) * (rho/2) * a *
      Real.exp (-m*rho*(t-u))) =
      a / (2*(n-m)) * (Real.exp (-m*rho*t)-Real.exp (-n*rho*t)) := by
  have hd : n-m ≠ 0 := sub_ne_zero.mpr hnm
  let F := fun u : ℝ => a/(2*(n-m)) *
    (Real.exp (-m*rho*t)-Real.exp (-m*rho*t+(m-n)*rho*u))
  have hD (u : ℝ) : HasDerivAt F
      (Real.exp (-n*rho*u) * (rho/2) * a * Real.exp (-m*rho*(t-u))) u := by
    have he := ((((hasDerivAt_id u).const_mul ((m-n)*rho)).const_add (-m*rho*t)).exp)
    have hh := ((hasDerivAt_const u (Real.exp (-m*rho*t))).sub he).const_mul
      (a/(2*(n-m)))
    apply hh.congr_deriv
    have hx : Real.exp (-n*rho*u) * Real.exp (-m*rho*(t-u)) =
        Real.exp (-m*rho*t+(m-n)*rho*u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [id_eq,mul_one]
    rw [← hx]
    field_simp [hd]
    <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hD u) (show IntervalIntegrable
      (fun u : ℝ => Real.exp (-n*rho*u)*(rho/2)*a*Real.exp (-m*rho*(t-u)))
      MeasureTheory.volume 0 t from (by fun_prop : Continuous _).intervalIntegrable _ _)
  rw [hi]
  dsimp [F]
  have hx : -m*rho*t+(m-n)*rho*t = -n*rho*t := by ring
  rw [hx]
  simp

/-- Rational exponential-polynomial syntax, converted to a genuine polynomial
by replacing exp(-m*rho*t) with X^m. Ordered-pair half rates are included in
liftTerm rather than silently switching to unordered paths. -/
abbrev Expr := List (ℕ × ℚ)

def liftTerm (n : ℕ) (z : ℕ × ℚ) : Expr :=
  let b := z.2 / (2 * ((n : ℚ) - (z.1 : ℚ)))
  [(z.1,b),(n,-b)]

def liftExpr (n : ℕ) (p : Expr) : Expr := p.flatMap (liftTerm n)

noncomputable def kernelExpr (N : RootedBinary V E X) {sample : Copy → X} :
    ℕ → Code N sample → Code N sample → Expr
  | 0,s,d => [(0,if s=d then 1 else 0)]
  | budget+1,s,d =>
      if liveCard s ≤ 1 then [(0,if s=d then 1 else 0)]
      else [((liveCard s).choose 2,if s=d then 1 else 0)] ++
        (Finset.univ.toList : List (Choice N s)).flatMap (fun p =>
          liftExpr ((liveCard s).choose 2)
            (kernelExpr N budget (stepDestination N s (some p)) d))

noncomputable def exprPolynomial (p : Expr) : Polynomial ℚ :=
  (p.map (fun z => Polynomial.C z.2 * Polynomial.X ^ z.1)).sum

noncomputable def exprValue (p : Expr) (rho t : ℝ) : ℝ :=
  (p.map (fun z => (z.2 : ℝ) * Real.exp (-(z.1 : ℝ)*rho*t))).sum

@[simp] lemma exprValue_nil (rho t : ℝ) : exprValue [] rho t = 0 := rfl

@[simp] lemma exprValue_cons (z : ℕ × ℚ) (p : Expr) (rho t : ℝ) :
    exprValue (z::p) rho t = (z.2 : ℝ)*Real.exp (-(z.1 : ℝ)*rho*t) + exprValue p rho t := rfl

@[simp] lemma exprValue_append (p q : Expr) (rho t : ℝ) :
    exprValue (p++q) rho t = exprValue p rho t + exprValue q rho t := by
  simp [exprValue,List.sum_append]

lemma exprValue_continuous (p : Expr) (rho : ℝ) : Continuous (fun t => exprValue p rho t) := by
  induction p with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  | cons z p ih =>
      simp only [exprValue_cons]
      exact ((Real.continuous_exp.comp (by fun_prop)).const_mul _).add ih

lemma exprValue_liftTerm (n : ℕ) (z : ℕ × ℚ) (rho t : ℝ) :
    exprValue (liftTerm n z) rho t =
      (z.2 : ℝ)/(2*((n:ℝ)-(z.1:ℝ))) *
        (Real.exp (-(z.1:ℝ)*rho*t)-Real.exp (-(n:ℝ)*rho*t)) := by
  simp [liftTerm,exprValue,Rat.cast_div,Rat.cast_mul,Rat.cast_sub]
  ring

lemma integral_exprValue (n : ℕ) (p : Expr) (rho t : ℝ)
    (hb : ∀ z ∈ p, z.1 < n) :
    (∫ u in (0:ℝ)..t, Real.exp (-(n:ℝ)*rho*u)*(rho/2)*exprValue p rho (t-u)) =
      exprValue (liftExpr n p) rho t := by
  induction p with
  | nil => simp [liftExpr]
  | cons z p ih =>
      have hz : z.1 < n := hb z (by simp)
      have hp : ∀ w ∈ p, w.1 < n := fun w hw => hb w (by simp [hw])
      have hn : (n:ℝ) ≠ (z.1:ℝ) := by exact_mod_cast (Nat.ne_of_gt hz)
      have hc : Continuous (fun u : ℝ => exprValue p rho (t-u)) :=
        (exprValue_continuous p rho).comp (continuous_const.sub continuous_id)
      have hf : IntervalIntegrable
          (fun u : ℝ => Real.exp (-(n:ℝ)*rho*u)*(rho/2)*(z.2:ℝ)*
            Real.exp (-(z.1:ℝ)*rho*(t-u))) volume 0 t :=
        (by fun_prop : Continuous _).intervalIntegrable _ _
      have hg : IntervalIntegrable
          (fun u : ℝ => Real.exp (-(n:ℝ)*rho*u)*(rho/2)*exprValue p rho (t-u)) volume 0 t :=
        (((by fun_prop : Continuous (fun u : ℝ => Real.exp (-(n:ℝ)*rho*u)*(rho/2)))).mul hc).intervalIntegrable _ _
      calc
        _ = (∫ u in (0:ℝ)..t, Real.exp (-(n:ℝ)*rho*u)*(rho/2)*(z.2:ℝ)*
              Real.exp (-(z.1:ℝ)*rho*(t-u))) +
            (∫ u in (0:ℝ)..t, Real.exp (-(n:ℝ)*rho*u)*(rho/2)*exprValue p rho (t-u)) := by
          rw [← intervalIntegral.integral_add hf hg]
          apply intervalIntegral.integral_congr
          intro u _
          dsimp only
          rw [exprValue_cons]
          ring
        _ = _ := by
          rw [damped_monomial_integral _ _ _ _ _ hn,ih hp]
          simp only [liftExpr,List.flatMap_cons,exprValue_append,exprValue_liftTerm]

lemma merger_exponent_lt (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (hk : 2 ≤ liveCard s) :
    (liveCard (stepDestination N s (some p))).choose 2 < (liveCard s).choose 2 := by
  have hc := merger_destination_card N s p
  have hj : 0 < liveCard (stepDestination N s (some p)) := by omega
  rw [← hc,Nat.choose_succ_succ,Nat.choose_one_right]
  change (liveCard (stepDestination N s (some p))).choose 2 <
    liveCard (stepDestination N s (some p)) + (liveCard (stepDestination N s (some p))).choose 2
  omega

lemma kernelExpr_bound (N : RootedBinary V E X) {sample : Copy → X}
    (budget : ℕ) (s d : Code N sample) :
    ∀ z ∈ kernelExpr N budget s d, z.1 ≤ (liveCard s).choose 2 := by
  induction budget generalizing s with
  | zero => simp [kernelExpr]
  | succ budget ih =>
      by_cases hk : liveCard s ≤ 1
      · simp [kernelExpr,hk]
      · intro z hz
        simp only [kernelExpr,if_neg hk,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
        rcases hz with hz | hz
        · subst z
          exact le_rfl
        · obtain ⟨p,hp,hz⟩ := List.mem_flatMap.mp hz
          obtain ⟨w,hw,hz⟩ := List.mem_flatMap.mp hz
          have hb := ih (stepDestination N s (some p)) w hw
          have he := merger_exponent_lt N s p (by omega)
          simp only [liftTerm,List.mem_cons,List.not_mem_nil,or_false] at hz
          rcases hz with hz | hz
          · subst z
            exact (hb.trans_lt he).le
          · subst z
            exact le_rfl

lemma exprValue_flatMap {A : Type*} (xs : List A) (f : A → Expr) (rho t : ℝ) :
    exprValue (xs.flatMap f) rho t = (xs.map (fun a => exprValue (f a) rho t)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,exprValue_append,List.map_cons,List.sum_cons,ih]

lemma exprValue_finite {A : Type*} [Fintype A] (f : A → Expr) (rho t : ℝ) :
    exprValue (Finset.univ.toList.flatMap f) rho t = ∑ a : A, exprValue (f a) rho t := by
  rw [exprValue_flatMap,Finset.sum_map_toList]

/-- The recursively constructed rational expression is the ACTUAL entire
single-population source transition row, uniformly in the positive physical rate bank.
No polynomial law or finite-time approximation is supplied as a premise. -/
theorem kernelExpr_actual (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (i : Option E) (budget : ℕ) (s d : Code N sample) (t : ℝ≥0)
    (hs : CoLocated N s i) (hb : liveCard s ≤ budget) :
    exprValue (kernelExpr N budget s d) (pairRate r i) (t:ℝ) =
      (sourceTimeKernel N r t s d).toReal := by
  induction budget generalizing s t with
  | zero =>
      rw [actual_terminal_epoch N r s d t (by omega)]
      by_cases he : s=d <;> simp [kernelExpr,exprValue,he]
  | succ budget ih =>
      by_cases hk : liveCard s ≤ 1
      · rw [kernelExpr,if_pos hk,actual_terminal_epoch N r s d t hk]
        by_cases he : s=d <;> simp [exprValue,he]
      · have hold : exprValue [((liveCard s).choose 2,if s=d then 1 else 0)]
            (pairRate r i) (t:ℝ) =
            Real.exp (-(totalRate N r s*(t:ℝ))) * (if s=d then 1 else 0) := by
          rw [actual_population_holding_rate N r s i hs]
          by_cases he : s=d
          · simp only [he,if_pos,exprValue_cons,exprValue_nil,Rat.cast_one,one_mul,add_zero,mul_one]
            congr 1
            ring
          · simp [exprValue,he]
        rw [kernelExpr,if_neg hk,exprValue_append,hold,exprValue_finite,
          actual_source_kernel_first_jump]
        congr 1
        symm
        let phi := fun (p : Choice N s) (u : ℝ) =>
          Real.exp (-((liveCard s).choose 2 : ℝ)*(pairRate r i)*u)*((pairRate r i)/2)*
            exprValue (kernelExpr N budget (stepDestination N s (some p)) d)
              (pairRate r i) ((t:ℝ)-u)
        have hphi (p : Choice N s) : IntervalIntegrable (phi p) volume 0 (t:ℝ) := by
          have hc : Continuous (fun u : ℝ =>
              exprValue (kernelExpr N budget (stepDestination N s (some p)) d)
                (pairRate r i) ((t:ℝ)-u)) :=
            (exprValue_continuous _ _).comp (continuous_const.sub continuous_id)
          exact ((by fun_prop : Continuous (fun u : ℝ =>
            Real.exp (-((liveCard s).choose 2 : ℝ)*(pairRate r i)*u)*((pairRate r i)/2))).mul hc).intervalIntegrable _ _
        calc
          _ = ∫ u in (0:ℝ)..(t:ℝ), ∑ p : Choice N s, phi p u := by
            apply intervalIntegral.integral_congr
            intro u hu
            dsimp only
            have hut : u ≤ (t:ℝ) := by
              have hh : u ∈ Set.Icc (0:ℝ) (t:ℝ) := by
                simpa only [Set.uIcc_of_le (show (0:ℝ) ≤ (t:ℝ) from t.property)] using hu
              exact hh.2
            have hexp : Real.exp (-(totalRate N r s*u)) =
                Real.exp (-((liveCard s).choose 2 : ℝ)*(pairRate r i)*u) := by
              rw [actual_population_holding_rate N r s i hs]
              congr 1
              ring
            rw [hexp,Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p _
            have hc := merger_destination_card N s p
            have he := ih (stepDestination N s (some p)) (Real.toNNReal ((t:ℝ)-u))
              (population_merger_preserved N s i hs p) (by omega)
            rw [Real.coe_toNNReal _ (sub_nonneg.mpr hut)] at he
            rw [← he,population_choice_rate N r s i hs p]
            dsimp [phi,pairRate]
            ring
          _ = ∑ p : Choice N s, ∫ u in (0:ℝ)..(t:ℝ), phi p u :=
            intervalIntegral.integral_finsetSum (fun p _ => hphi p)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro p _
            apply integral_exprValue
            intro z hz
            exact (kernelExpr_bound N budget (stepDestination N s (some p)) d z hz).trans_lt
              (merger_exponent_lt N s p (by omega))

@[simp] lemma exprPolynomial_nil : exprPolynomial [] = 0 := rfl

@[simp] lemma exprPolynomial_cons (z : ℕ × ℚ) (p : Expr) :
    exprPolynomial (z::p) = Polynomial.C z.2 * Polynomial.X ^ z.1 + exprPolynomial p := rfl

lemma exprPolynomial_eval (p : Expr) (rho t : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-rho*t)) (exprPolynomial p) =
      exprValue p rho t := by
  have he (n : ℕ) : Real.exp (-rho*t)^n = Real.exp (-(n:ℝ)*rho*t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  induction p with
  | nil => simp
  | cons z p ih =>
      simp only [exprPolynomial_cons,Polynomial.eval₂_add,Polynomial.eval₂_mul,
        Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X,exprValue_cons,he,ih]
      rfl

/-- A rational polynomial built from actual source choices and destinations.
Its coefficients contain no physical rates or source-probability fits. -/
noncomputable def populationPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) : Polynomial ℚ :=
  exprPolynomial (kernelExpr N (Fintype.card Copy) s d)

/-- Entire actual single-population transition law, at arbitrary finite positive rate
and nonnegative time, represented by one explicitly constructed rational
polynomial in the physical survival coordinate. -/
theorem actual_population_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-(pairRate r i)*(t:ℝ)))
      (populationPolynomial N s d) = (sourceTimeKernel N r t s d).toReal := by
  rw [populationPolynomial,exprPolynomial_eval]
  exact kernelExpr_actual N r i _ s d t hs (Finset.card_le_univ s.val.live)

lemma exprPolynomial_degree (p : Expr) (n : ℕ)
    (hb : ∀ z ∈ p, z.1 ≤ n) : (exprPolynomial p).natDegree ≤ n := by
  induction p with
  | nil => simp
  | cons z p ih =>
      rw [exprPolynomial_cons]
      apply Polynomial.natDegree_add_le_of_degree_le
      · rw [Polynomial.C_mul_X_pow_eq_monomial]
        exact (Polynomial.natDegree_monomial_le z.2).trans (hb z (by simp))
      · exact ih (fun w hw => hb w (by simp [hw]))

theorem populationPolynomial_degree (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    (populationPolynomial N s d).natDegree ≤ (liveCard s).choose 2 :=
  exprPolynomial_degree _ _ (kernelExpr_bound N _ s d)

/-- A co-located source epoch depends only on that population's physical
rate. Other original edge and ancestral rates may vary together arbitrarily;
the complete retained-state PMF is unchanged. -/
theorem own_population_rate_only (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r rhat : PositivePairRates E) (t : ℝ≥0) (hr : pairRate r i = pairRate rhat i) :
    sourceTimeKernel N r t s = sourceTimeKernel N rhat t s := by
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [← actual_population_polynomial N s d i hs r t,
    ← actual_population_polynomial N s d i hs rhat t,hr]

end GProgram.G7.SinglePopulationPolynomialKernel

end FullContextModule89

section FullContextModule90




/-! Executable exact rational coefficient lists for the actual original-source
single-population kernel. Contributor: dot, 2026-10-10. FinEnum replaces the
noncomputable Finset.toList ordering; source mergers and their snapshot
encoding remain literal. Permutation equivalence binds the executable list to
the already checked analytic recurrence for all positive rates and t >= 0.
-/
namespace GProgram.G7.EffectivePopulationCoefficients
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration
open scoped NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def sourceState {N : RootedBinary V E X} {sample : Copy → X}
    (s : Code N sample) : State V E Copy := decode N.root s.val

def place (N : RootedBinary V E X) : Option E → Location V E
  | none => .rootPopulation N.root
  | some e => .edge e

def encode (s : State V E Copy) (hs : Valid s) : Snapshot V E Copy where
  live := s.live
  ancestor := s.ancestor
  genealogy l := if h : l ∈ s.live then some ⟨s.genealogy l,hs.wellLabelled l h⟩ else none
  population l := if l ∈ s.live then some (s.location l) else none
  register := s.register

def encodeActual (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) : Code N sample :=
  ⟨encode s hs.forest,decode_encode_sourceValid N sample s hs⟩

instance choiceEnumeration (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : FinEnum (Choice N s) := by
  change FinEnum (Σ i : Option E,
    {p : Copy × Copy // p ∈ (populationRoots (sourceState s) (place N i)).offDiag})
  infer_instance

def merger (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : Code N sample :=
  encodeActual N sample (merge (sourceState s) p.2.val.1 p.2.val.2)
    (merge_source_valid N sample (state s) s.property
      (population_pair_is_source_legal (state s) (originalPlace N p.1)
        (originalPlace_not_node N p.1) p.2.property))

theorem merger_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    merger N s p = stepDestination N s (some p) := rfl

/-- Finite, rational arithmetic only. The copy cap supplies the fuel below. -/
def coefficients (N : RootedBinary V E X) {sample : Copy → X} :
    ℕ → Code N sample → Code N sample → Expr
  | 0,s,d => [(0,if s=d then 1 else 0)]
  | fuel+1,s,d =>
      if s.val.live.card ≤ 1 then [(0,if s=d then 1 else 0)]
      else [(s.val.live.card.choose 2,if s=d then 1 else 0)] ++
        (FinEnum.toList (Choice N s)).flatMap (fun p =>
          liftExpr (s.val.live.card.choose 2) (coefficients N fuel (merger N s p) d))

lemma enumeration_perm (A : Type*) [Fintype A] [FinEnum A] :
    (FinEnum.toList A).Perm (Finset.univ.toList : List A) := by
  apply (List.perm_ext_iff_of_nodup (FinEnum.nodup_toList (α := A))
    (Finset.nodup_toList _)).mpr
  intro a
  simp

/-- Reordering the complete legal-pair list only reorders monomial terms. -/
theorem coefficients_perm_kernelExpr (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : ℕ) (s d : Code N sample) :
    (coefficients N fuel s d).Perm (kernelExpr N fuel s d) := by
  classical
  induction fuel generalizing s with
  | zero => simp [coefficients,kernelExpr]
  | succ fuel ih =>
      by_cases h : s.val.live.card ≤ 1
      · simp [coefficients,kernelExpr,liveCard,h]
      · have hkernel : ¬ liveCard s ≤ 1 := h
        simp only [coefficients,kernelExpr,if_neg h,if_neg hkernel]
        simp only [liveCard]
        apply List.Perm.append
        · by_cases hsd : s = d <;> simp [hsd]
        · apply (enumeration_perm (Choice N s)).flatMap
          intro p _
          exact (ih (merger N s p)).flatMap_right (liftTerm (s.val.live.card.choose 2))

/-- The executable coefficient list denotes exactly the already verified
actual source polynomial, without selecting an existential polynomial. -/
theorem coefficients_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) :
    exprPolynomial (coefficients N (Fintype.card Copy) s d) = populationPolynomial N s d := by
  unfold exprPolynomial populationPolynomial
  exact ((coefficients_perm_kernelExpr N _ s d).map _).sum_eq

theorem actual_population_coefficients (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r i * (t:ℝ)))
      (exprPolynomial (coefficients N (Fintype.card Copy) s d)) =
      (sourceTimeKernel N r t s d).toReal := by
  rw [coefficients_polynomial]
  exact actual_population_polynomial N s d i hs r t

end GProgram.G7.EffectivePopulationCoefficients

end FullContextModule90

section FullContextModule91


/-!
# Literal merger support of the inherited executable coefficients

Contributor: Codex / lean_reuse_successor, 10 October 2026.
The search carrier uses the original Choice and merger, without enumerating all
Code states. The proof has arbitrary fuel and copy cardinality; no quotient,
resource bound, or Rust implementation theorem is asserted.
-/
namespace GProgram.G7.EffectiveCoefficientSupport

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open scoped NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Reflexive merger closure with precisely the executable coefficient fuel. -/
def destinations (N : RootedBinary V E X) {sample : Copy → X} :
    Nat → Code N sample → List (Code N sample)
  | 0, s => [s]
  | fuel + 1, s =>
      if s.val.live.card ≤ 1 then [s]
      else s :: (FinEnum.toList (Choice N s)).flatMap
        (fun p => destinations N fuel (merger N s p))

lemma liftExpr_zero_coefficients (n : Nat) (p : Expr)
    (hp : ∀ z ∈ p, z.2 = 0) :
    ∀ z ∈ liftExpr n p, z.2 = 0 := by
  intro z hz
  rcases List.mem_flatMap.mp hz with ⟨w, hw, hz⟩
  have hw0 := hp w hw
  have hz0 : z = (w.1, 0) ∨ z = (n, 0) := by
    simpa [liftTerm, hw0] using hz
  rcases hz0 with rfl | rfl <;> rfl

/-- Outside literal fuel-bounded merger support, every raw term vanishes. -/
theorem coefficients_zero_of_not_mem (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s d : Code N sample)
    (hd : d ∉ destinations N fuel s) :
    ∀ z ∈ coefficients N fuel s d, z.2 = 0 := by
  induction fuel generalizing s with
  | zero =>
      have hsd : s ≠ d := by
        intro h
        apply hd
        simp [destinations, h]
      intro z hz
      have hz0 : z = (0, 0) := by simpa [coefficients, hsd] using hz
      subst z
      rfl
  | succ fuel ih =>
      by_cases hk : s.val.live.card ≤ 1
      · have hsd : s ≠ d := by
          intro h
          apply hd
          rw [destinations, if_pos hk]
          exact List.mem_singleton.mpr h.symm
        intro z hz
        have hz0 : z = (0, 0) := by simpa [coefficients, hk, hsd] using hz
        subst z
        rfl
      · have hsd : s ≠ d := by
          intro h
          apply hd
          rw [destinations, if_neg hk]
          exact List.mem_cons.mpr (Or.inl h.symm)
        have hchildren (p : Choice N s) (hp : p ∈ FinEnum.toList (Choice N s)) :
            d ∉ destinations N fuel (merger N s p) := by
          intro hm
          apply hd
          simp only [destinations, if_neg hk, List.mem_cons, List.mem_flatMap]
          exact Or.inr ⟨p, hp, hm⟩
        intro z hz
        simp only [coefficients, if_neg hk, List.mem_append] at hz
        rcases hz with hz | hz
        · have hz0 : z = (s.val.live.card.choose 2, 0) := by
            simpa [hsd] using hz
          subst z
          rfl
        · rcases List.mem_flatMap.mp hz with ⟨p, hp, hz⟩
          exact liftExpr_zero_coefficients _ _
            (ih (merger N s p) (hchildren p hp)) z hz

lemma exprPolynomial_zero_of_zero_coefficients (p : Expr)
    (hp : ∀ z ∈ p, z.2 = 0) : exprPolynomial p = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      have hz : z.2 = 0 := hp z (by simp)
      have ht : ∀ w ∈ p, w.2 = 0 := fun w hw => hp w (by simp [hw])
      rw [exprPolynomial_cons, hz, Polynomial.C_0, zero_mul, zero_add]
      exact ih ht

theorem coefficients_polynomial_zero_of_not_mem (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : Nat) (s d : Code N sample)
    (hd : d ∉ destinations N fuel s) :
    exprPolynomial (coefficients N fuel s d) = 0 :=
  exprPolynomial_zero_of_zero_coefficients _
    (coefficients_zero_of_not_mem N fuel s d hd)

/-- In one actual co-located population, the support restriction is semantic. -/
theorem actual_population_zero_of_not_mem (N : RootedBinary V E X)
    {sample : Copy → X} (s d : Code N sample) (i : Option E)
    (hs : CoLocated N s i)
    (hd : d ∉ destinations N (Fintype.card Copy) s)
    (r : PositivePairRates E) (t : ℝ≥0) :
    (sourceTimeKernel N r t s d).toReal = 0 := by
  rw [← actual_population_coefficients N s d i hs r t]
  rw [coefficients_polynomial_zero_of_not_mem N _ s d hd]
  simp

end GProgram.G7.EffectiveCoefficientSupport

end FullContextModule91

section FullContextModule92


/-! SOURCE PROPOSAL. The complete imported context has NOT been elaborated.
This checks a supplied finite native population table against the EXISTING
literal merger recurrence. It is not a Rust/parser proof or a new kernel.
No #eval, native_decide, new axiom, external process or runtime writer occurs. -/

namespace Astra.NativePopulationTableCertificate

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveCoefficientSupport

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Native destinations are actual supplied admitted Codes, not validator flags.
Repeated destinations and raw duplicate/zero monomials are permitted. -/
abbrev Table (N : RootedBinary V E X) (sample : Copy → X) :=
  List (Code N sample × Expr)

def coefficient (p : Expr) (k : Nat) : ℚ :=
  (p.map fun z => if z.1 = k then z.2 else 0).sum

def checkExpr (p q : Expr) : Bool :=
  ((p.map Prod.fst ++ q.map Prod.fst).dedup).all fun k =>
    decide (coefficient p k = coefficient q k)

lemma polynomial_coefficient (p : Expr) (k : Nat) :
    (exprPolynomial p).coeff k = coefficient p k := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      rw [exprPolynomial_cons, Polynomial.coeff_add, ih]
      by_cases hz : z.1 = k
      · simp [coefficient, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial, hz, eq_comm]
      · simp [coefficient, Polynomial.C_mul_X_pow_eq_monomial,
          Polynomial.coeff_monomial, hz, Ne.symm hz]

lemma coefficient_zero_of_absent (p : Expr) (k : Nat)
    (hk : k ∉ p.map Prod.fst) : coefficient p k = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      have hz : z.1 ≠ k := by
        intro h
        apply hk
        simp [h]
      have hp : k ∉ p.map Prod.fst := by
        intro h
        apply hk
        simp [h]
      change (if z.1 = k then z.2 else 0) + coefficient p k = 0
      rw [if_neg hz, zero_add]
      exact ih hp

/-- Finite coefficient comparison is sound for every real evaluation. The
checker compares rational sums, not samples or floating-point values. -/
theorem checkExpr_sound (p q : Expr) (h : checkExpr p q = true) :
    exprPolynomial p = exprPolynomial q := by
  apply Polynomial.ext
  intro k
  rw [polynomial_coefficient, polynomial_coefficient]
  by_cases hk : k ∈ (p.map Prod.fst ++ q.map Prod.fst).dedup
  · have hall := List.all_eq_true.mp h
    exact of_decide_eq_true (hall k hk)
  · have hn : k ∉ p.map Prod.fst ∧ k ∉ q.map Prod.fst := by
      simpa only [List.mem_dedup, List.mem_append, not_or] using hk
    rw [coefficient_zero_of_absent p k hn.1,
      coefficient_zero_of_absent q k hn.2]

/-- Complete coefficient of one Code; duplicate native entries are summed. -/
def collect {N : RootedBinary V E X} {sample : Copy → X}
    (rows : Table N sample) (d : Code N sample) : Expr :=
  rows.flatMap fun row => if row.1 = d then row.2 else []

lemma collect_empty_of_absent {N : RootedBinary V E X} {sample : Copy → X}
    (rows : Table N sample) (d : Code N sample)
    (hd : d ∉ rows.map Prod.fst) : collect rows d = [] := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hr : row.1 ≠ d := by
        intro h
        apply hd
        simp [h]
      have ht : d ∉ rows.map Prod.fst := by
        intro h
        apply hd
        simp [h]
      change (if row.1 = d then row.2 else []) ++ collect rows d = []
      rw [if_neg hr, List.nil_append]
      exact ih ht

/-- This uses merger support plus supplied destinations, never all Code states.
A spurious nonzero native destination therefore cannot hide outside support. -/
def carrier (N : RootedBinary V E X) {sample : Copy → X} (fuel : Nat)
    (s : Code N sample) (rows : Table N sample) : List (Code N sample) :=
  (destinations N fuel s ++ rows.map Prod.fst).dedup

def check (N : RootedBinary V E X) {sample : Copy → X} (fuel : Nat)
    (s : Code N sample) (rows : Table N sample) : Bool :=
  (carrier N fuel s rows).all fun d =>
    checkExpr (collect rows d) (coefficients N fuel s d)

/-- The conclusion includes EVERY admitted destination, including zero on
all omitted destinations. It assumes no final row-polynomial equality. -/
theorem check_sound (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s : Code N sample) (rows : Table N sample)
    (h : check N fuel s rows = true) (d : Code N sample) :
    exprPolynomial (collect rows d) =
      exprPolynomial (coefficients N fuel s d) := by
  by_cases hd : d ∈ carrier N fuel s rows
  · have hall := List.all_eq_true.mp h
    exact checkExpr_sound _ _ (hall d hd)
  · have hn : d ∉ destinations N fuel s ∧ d ∉ rows.map Prod.fst := by
      simpa only [carrier, List.mem_dedup, List.mem_append, not_or] using hd
    calc
      exprPolynomial (collect rows d) = 0 := by
        rw [collect_empty_of_absent rows d hn.2]
        rfl
      _ = exprPolynomial (coefficients N fuel s d) :=
        (coefficients_polynomial_zero_of_not_mem N fuel s d hn.1).symm

/-- Actual co-located population semantics, using the original positive rates
and copy-cardinality fuel. No completed-calendar or source-census claim. -/
theorem checked_actual_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (rows : Table N sample)
    (h : check N (Fintype.card Copy) s rows = true)
    (d : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (r : PositivePairRates E) (t : ℝ≥0) :
    Polynomial.eval₂ (Rat.castHom ℝ) (Real.exp (-pairRate r i * (t : ℝ)))
      (exprPolynomial (collect rows d)) =
        (sourceTimeKernel N r t s d).toReal := by
  rw [check_sound N (Fintype.card Copy) s rows h d]
  exact actual_population_coefficients N s d i hs r t

end Astra.NativePopulationTableCertificate

end FullContextModule92
