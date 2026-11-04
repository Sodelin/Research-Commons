import Mathlib.Data.FinEnum
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

section ScopedPopulationModule0
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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


end ScopedPopulationModule0

section ScopedPopulationModule1
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
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


variable [DecidableEq E]
variable {N : RootedBinary V E X}


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


theorem merge_source_valid (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) {a b : Copy}
    (hm : LegalMerge s a b) : SourceValid N sample (merge s a b) := by
  refine ⟨merge_valid s hs.forest hm, ?_⟩
  intro x
  rw [merge_population_preserved s hm]
  exact hs.original_descendant x


end GProgram.SourceForest

end ScopedPopulationModule1

section ScopedPopulationModule2
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace GProgram.SourceForestKingmanPopulationProjection

open GProgram.SourceForest

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


end GProgram.SourceForestKingmanPopulationProjection

end ScopedPopulationModule2

section ScopedPopulationModule3
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule3

section ScopedPopulationModule4
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace UnifiedLean.Source.FiniteSourceSnapshot
open Nanuq.Source GProgram.SourceForest
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

end ScopedPopulationModule4

section ScopedPopulationModule5
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace UnifiedLean.Source.NativePairClockLaw
open Nanuq.Source
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


end UnifiedLean.Source.NativePairClockLaw

end ScopedPopulationModule5

section ScopedPopulationModule6
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule6

section ScopedPopulationModule7
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace UnifiedLean.Source.SourceStepGeneratorBinding
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
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


end UnifiedLean.Source.SourceStepGeneratorBinding

end ScopedPopulationModule7

section ScopedPopulationModule8
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace UnifiedLean.Source.SourceFiniteProjection
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceStepGeneratorBinding
open Matrix
open scoped BigOperators Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]


noncomputable def sourceTransition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Matrix (Code N sample) (Code N sample) ℝ :=
  fun s t => (sourceStep N r s t).toReal


end UnifiedLean.Source.SourceFiniteProjection

end ScopedPopulationModule8

section ScopedPopulationModule9
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace GProgram.G7.EffectiveSourceEnumeration
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteGenealogyEncoding UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceFiniteProjection

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]


instance optionEnumeration {A : Type*} [FinEnum A] : FinEnum (Option A) :=
  FinEnum.ofList (none :: (FinEnum.toList A).map some) (by
    intro a; cases a <;> simp)


/-- Equality is fieldwise; it does not search the large snapshot enumeration. -/
instance snapshotDecidableEq : DecidableEq (Snapshot V E Copy) := fun a b =>
  decidable_of_iff (a.live = b.live ∧ a.ancestor = b.ancestor ∧
    a.genealogy = b.genealogy ∧ a.population = b.population ∧ a.register = b.register)
    ⟨fun h => Snapshot.ext h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2,
     fun h => by cases h; exact ⟨rfl,rfl,rfl,rfl,rfl⟩⟩


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


end GProgram.G7.EffectiveSourceEnumeration

end ScopedPopulationModule9

section ScopedPopulationModule10
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
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


noncomputable def globalClockRate (r : PositivePairRates E) : ℝ≥0 :=
  ⟨globalRateBound (Copy := Copy) r,(globalRateBound_positive (Copy := Copy) r).le⟩

noncomputable def countPMF (rate : ℝ≥0) : PMF Nat := (poissonMeasure rate).toPMF

noncomputable def sourceTimeKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) : PMF (Code N sample) :=
  (countPMF (globalClockRate (Copy := Copy) r * t)).bind
    (fun k => sourceIteration N r k s)


end UnifiedLean.Source.SourcePoissonKernel

end ScopedPopulationModule10

section ScopedPopulationModule11
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace UnifiedLean.Source.SourceGeneratorExponential
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection
open Matrix NormedSpace
open scoped Classical Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]


noncomputable def sourceGeneratorMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : Matrix (Code N sample) (Code N sample) ℝ :=
  globalRateBound (Copy := Copy) r • (sourceTransition N (sample := sample) r - 1)


end UnifiedLean.Source.SourceGeneratorExponential

end ScopedPopulationModule11

section ScopedPopulationModule12
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule12

section ScopedPopulationModule13
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
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


end UnifiedLean.Source.SourceActualHoldingClocks

end ScopedPopulationModule13

section ScopedPopulationModule14
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule14

section ScopedPopulationModule15
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
namespace UnifiedLean.Source.SourceAncestralCompletion
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]


lemma choice_empty_of_terminal_card (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hc : liveCard s ≤ 1) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  exact hp.different ((Finset.card_le_one.mp hc) _ hp.first_live _ hp.second_live)


end UnifiedLean.Source.SourceAncestralCompletion

end ScopedPopulationModule15

section ScopedPopulationModule16
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule16

section ScopedPopulationModule17
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule17

section ScopedPopulationModule18
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false

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

end ScopedPopulationModule18

section ScopedPopulationCertificate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.deprecated false
open scoped NNReal

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

end ScopedPopulationCertificate
