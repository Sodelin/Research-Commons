import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.Fintype.Inv
import Mathlib.Logic.Equiv.Fin.Basic

section OriginalComponent0
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false















namespace Nanuq.Source

universe u v w

structure EdgeGraph (V : Type u) (E : Type v) where
  source : E → V
  target : E → V

namespace EdgeGraph

variable {V : Type u} {E : Type v} (G : EdgeGraph V E)


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


def ReachWithout (e : E) (a b : V) : Prop :=
  G.UReach (fun f => f ≠ e) a b


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







end OriginalComponent0

section OriginalComponent1
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

















namespace GProgram.G7

open Nanuq.Source
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

theorem sum_inDegree (G : EdgeGraph V E) :
    (∑ v, G.inDegree v) = Fintype.card E := by
  classical
  simp only [EdgeGraph.inDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_outDegree (G : EdgeGraph V E) :
    (∑ v, G.outDegree v) = Fintype.card E := by
  classical
  simp only [EdgeGraph.outDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

noncomputable def hybridCount (N : RootedBinary V E X) : Nat := by
  classical
  exact (Finset.univ.filter N.graph.IsHybrid).card

noncomputable def leafSet (N : RootedBinary V E X) : Finset V := by
  classical
  exact Finset.univ.image N.leaf

theorem leafSet_card (N : RootedBinary V E X) :
    (leafSet N).card = Fintype.card X := by
  classical
  simp [leafSet, Finset.card_image_of_injective, N.leaf.injective]

theorem degree_local_in (N : RootedBinary V E X) (v : V) :
    N.graph.inDegree v + (if v = N.root then 1 else 0) =
      1 + (if N.graph.IsHybrid v then 1 else 0) := by
  classical
  by_cases hr : v = N.root
  · subst v
    have hn : ¬ N.graph.IsHybrid N.root := by
      intro hh
      have h0 := N.root_degrees.1
      rw [hh.1] at h0
      cases h0
    simp [N.root_degrees.1, hn]
  · by_cases hl : ∃ x, N.leaf x = v
    · obtain ⟨x, rfl⟩ := hl
      have hn : ¬ N.graph.IsHybrid (N.leaf x) := by
        intro hh
        have h1 := (N.leaf_degrees x).1
        rw [hh.1] at h1
        cases h1
      simp [hr, (N.leaf_degrees x).1, hn]
    · rcases N.internal_degrees v hr (fun x hx => hl ⟨x, hx⟩) with ht | hh
      · have hn : ¬ N.graph.IsHybrid v := by
          intro hh
          rw [hh.1] at ht
          omega
        simp [hr, ht.1, hn]
      · simp [hr, hh, hh.1]

theorem degree_local_out (N : RootedBinary V E X) (v : V) :
    N.graph.outDegree v + 2 * (if v ∈ leafSet N then 1 else 0) +
      (if N.graph.IsHybrid v then 1 else 0) = 2 := by
  classical
  by_cases hr : v = N.root
  · subst v
    have hn : ¬ N.graph.IsHybrid N.root := by
      intro hh
      have h0 := hh.1
      rw [N.root_degrees.1] at h0
      omega
    have hl : N.root ∉ leafSet N := by
      simp only [leafSet, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      exact N.leaf_ne_root
    simp [N.root_degrees.2, hn, hl]
  · by_cases hl : ∃ x, N.leaf x = v
    · obtain ⟨x, rfl⟩ := hl
      have hn : ¬ N.graph.IsHybrid (N.leaf x) := by
        intro hh
        have h0 := hh.2
        rw [(N.leaf_degrees x).2] at h0
        omega
      have hm : N.leaf x ∈ leafSet N := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
      simp [(N.leaf_degrees x).2, hn, hm]
    · have hm : v ∉ leafSet N := by simpa [leafSet] using hl
      rcases N.internal_degrees v hr (fun x hx => hl ⟨x, hx⟩) with ht | hh
      · have hn : ¬ N.graph.IsHybrid v := by
          intro hh
          rw [hh.2] at ht
          omega
        simp [ht.2, hm, hn]
      · simp [hh, hh.2, hm]

theorem original_census (N : RootedBinary V E X) :
    Fintype.card V + 1 = 2 * Fintype.card X + 2 * hybridCount N ∧
    Fintype.card E + 2 = 2 * Fintype.card X + 3 * hybridCount N := by
  classical
  have hi := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => degree_local_in N v)
  have ho := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun v _ => degree_local_out N v)
  have hc : (∑ v : V, if N.graph.IsHybrid v then 1 else 0) = hybridCount N := by
    simp only [hybridCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hl : (∑ v : V, if v ∈ leafSet N then 1 else 0) = Fintype.card X := by
    rw [← leafSet_card N]
    simp
  simp only [Finset.sum_add_distrib, sum_inDegree, sum_outDegree,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hi ho
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hc, hl,
    ← Finset.mul_sum] at hi ho
  simp only [Nat.cast_id, mul_one] at hi ho
  omega





end GProgram.G7

end OriginalComponent1

section OriginalComponent2
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false



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





end OriginalComponent2

section OriginalComponent3
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


namespace Nanuq.Source
namespace EdgeGraph

variable {V E : Type*} (G : EdgeGraph V E)


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


theorem bridge_source_side_contains_taxon (e : E) :
    ∃ x, N.graph.ReachWithout e (N.graph.source e) (N.leaf x) := by
  obtain ⟨x, hx⟩ := N.exists_leaf_avoiding_of_ne_root (N.edge_target_ne_root e)
  exact ⟨x, (N.root_on_source_side e).trans (N.graph.avoid_target_reach_without e hx)⟩


theorem bridge_both_sides_contain_taxa {e : E} (he : N.graph.IsBridge e) :
    (∃ x, N.graph.ReachWithout e (N.graph.source e) (N.leaf x)) ∧
    (∃ x, N.graph.ReachWithout e (N.graph.target e) (N.leaf x)) :=
  ⟨N.bridge_source_side_contains_taxon e, N.bridge_target_side_contains_taxon he⟩

end RootedBinary
end Nanuq.Source





end OriginalComponent3

section OriginalComponent4
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
















namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]



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



theorem bridge_selected_tip_iff (N : RootedBinary V E X)
    {e : E} (he : N.graph.IsBridge e) (x : X) :
    N.graph.ReachWithout e (N.graph.target e) (N.leaf x) ↔
      N.graph.DReach (N.graph.target e) (N.leaf x) :=
  bridge_target_component_iff_descendant N he (N.leaf x)


theorem unique_child_edge (N : RootedBinary V E X) {h : V}
    (hh : N.graph.outDegree h = 1) :
    ∃! e : E, N.graph.source e = h := by
  classical
  obtain ⟨e, he, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp hh
  refine ⟨e, (Finset.mem_filter.mp he).2, ?_⟩
  intro f hf
  exact hu f (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hf⟩)



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

end OriginalComponent4

section OriginalComponent5
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false


















namespace GProgram.G5

open Nanuq.Source

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


structure Calendar (G : EdgeGraph V E) where
  age : V → ℝ
  edge_older : ∀ e, age (G.target e) < age (G.source e)

def Calendar.Active {G : EdgeGraph V E} (C : Calendar G) (t : ℝ) (e : E) : Prop :=
  C.age (G.target e) ≤ t ∧ t < C.age (G.source e)


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


theorem protective_edge_absent_on_outside_route (N : RootedBinary V E X)
    {h : V} {e : E} (hs : N.graph.source e = h)
    {x : X} (hout : ¬ N.graph.DReach h (N.leaf x)) {es : List E}
    (p : EdgePath N.graph N.root (N.leaf x) es) : e ∉ es := by
  intro he
  apply hout
  exact (Relation.ReflTransGen.single ⟨e, hs, rfl⟩).trans
    (p.target_reaches_end_of_mem he)

omit [Fintype V] [Fintype E] [DecidableEq V] in


theorem protective_interval_nonempty {G : EdgeGraph V E} (C : Calendar G) (e : E) :
    ∃ t : ℝ, C.Active t e :=
  ⟨C.age (G.target e), le_refl _, C.edge_older e⟩



theorem younger_side_open_interval_has_no_first :
    ¬ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → t ≤ u := by
  rintro ⟨t, ht, ht1, hmin⟩
  have h := hmin (t / 2) (by linarith) (by linarith)
  linarith









end GProgram.G5

end OriginalComponent5

section OriginalComponent6
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false















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

end OriginalComponent6

section OriginalComponent7
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false















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

end OriginalComponent7

section OriginalComponent8
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false



















namespace GProgram.G2

open Nanuq.Source

variable {V E X Copy L : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


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


structure LiveAncestry (Copy L : Type*) where
  ancestor : Copy → L
  surjective : Function.Surjective ancestor

def routedParent {N : RootedBinary V E X} (H : OriginalHybridParents N)
    (state : LiveAncestry Copy L) (coin : L → Bool) (copy : Copy) : E :=
  H.parent (coin (state.ancestor copy))



theorem coalesced_copies_cannot_split {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (state : LiveAncestry Copy L) (coin : L → Bool)
    {x y : Copy} (hxy : state.ancestor x = state.ancestor y) :
    routedParent H state coin x = routedParent H state coin y := by
  simp only [routedParent, hxy]



theorem routed_parent_eq_iff_live_coin_eq {N : RootedBinary V E X}
    (H : OriginalHybridParents N) (state : LiveAncestry Copy L) (coin : L → Bool)
    (x y : Copy) :
    routedParent H state coin x = routedParent H state coin y ↔
      coin (state.ancestor x) = coin (state.ancestor y) := by
  exact H.parent_injective.eq_iff

def mergedPair : LiveAncestry Bool Unit :=
  ⟨fun _ => (), by intro u; cases u; exact ⟨false, rfl⟩⟩



theorem opposite_copy_bits_are_not_a_live_pulse :
    ¬ ∃ coin : Unit → Bool, ∀ copy : Bool, coin (mergedPair.ancestor copy) = copy := by
  rintro ⟨coin, hcoin⟩
  have hf := hcoin false
  have ht := hcoin true
  have h : (false : Bool) = true := hf.symm.trans ht
  cases h

def bitWeight (p : ℚ) (bit : Bool) : ℚ := if bit then 1 - p else p



def perCopyPulse (p : ℚ) (a b : Bool) : ℚ := bitWeight p a * bitWeight p b


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

end OriginalComponent8

section OriginalComponent9
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false













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



theorem two_incoming_occurrences_not_bridge (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e f : E}
    (hne : f ≠ e) (hf : G.target f = G.target e) : ¬ G.IsBridge e := by
  intro he
  exact hne (bridge_incoming_unique G root ha hr he hf)



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

end OriginalComponent9

section OriginalComponent10
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
















namespace GProgram.G5.ComponentEntries

open Nanuq.Source

variable {V E : Type*}


theorem sameBlob_avoids_bridge (G : EdgeGraph V E) {e : E}
    (he : G.IsBridge e) {a b : V} (hab : G.SameBlob a b) : G.ReachWithout e a b := by
  apply G.ureach_mono (keep := fun f => ¬ G.IsBridge f) _ hab
  intro f hf hfe
  subst f
  exact hf he


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


theorem bridge_target_not_root_component (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) : ¬ G.SameBlob (G.target e) root := by
  intro hb
  exact G.bridge_sides_disjoint he
    (GProgram.G5.Minimal.root_source_side_of_rooted_acyclic G root ha hr e)
    (sameBlob_avoids_bridge G he hb)



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



theorem nonroot_component_has_incoming_bridge (G : EdgeGraph V E) (root : V)
    (hr : ∀ v, G.DReach root v) (v : V) (hv : ¬ G.SameBlob root v) :
    ∃ e, G.IsBridge e ∧ G.SameBlob (G.target e) v := by
  obtain ⟨es, hp⟩ := GProgram.G5.exists_edgePath_of_directed (hr v)
  rcases EdgePath.sameBlob_or_incoming_bridge hp with hs | ⟨e, _, he, hb⟩
  · exact False.elim (hv hs)
  · exact ⟨e, he, hb⟩


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

end OriginalComponent10

section OriginalComponent11
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
















namespace GProgram.G5.NonbridgeRoutes

open Nanuq.Source

variable {V E : Type*}


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



theorem original_nonbridge_route_unique_of_first (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} {e : E} {es fs : List E}
    (p : UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b (e :: es))
    (q : UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b (e :: fs)) : es = fs := by
  exact p.unique_of_same_first N.acyclic (cut_child_nonbridge_incoming_unique N hcut) q



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



theorem hybrid_nonbridge_route_family_card_le_two (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (ha : N.graph.IsHybrid a) (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ 2 := by
  simpa only [ha.1] using finite_nonbridge_route_family_card_le_indegree N hcut hab R hR



theorem ordinary_nonbridge_route_family_card_le_one (N : RootedBinary V E X)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {a b : V} (ha : ¬ N.graph.IsHybrid a) (hab : a ≠ b) (R : Finset (List E))
    (hR : ∀ es ∈ R, UpPath N.graph (fun f => ¬ N.graph.IsBridge f) a b es) :
    R.card ≤ 1 := by
  exact (finite_nonbridge_route_family_card_le_indegree N hcut hab R hR).trans
    (nonhybrid_indegree_le_one N ha)

end OriginalSource









end GProgram.G5.NonbridgeRoutes

end OriginalComponent11

section OriginalComponent12
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false













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

end OriginalComponent12

section OriginalComponent13
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false














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

end OriginalComponent13

section OriginalComponent14
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentCalendar
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


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

end OriginalComponent14

section OriginalComponent15
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


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



theorem current_port_support_card_le_indegree
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ N.graph.inDegree port := by
  rcases ht with ⟨hl,⟨hb,hu⟩ | ⟨entry,he,hb,hu⟩⟩
  · rw [activeRootRouteEdges_eq_root_component N C hb t]
    exact activeComponentEdges_card_le_indegree N C hcut hl hu
  · exact activeRootRouteEdges_card_le_indegree_of_entry N C hcut he hb hl hu


theorem current_port_support_card_le_two
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} {t : ℝ} (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ 2 :=
  (current_port_support_card_le_indegree N C hcut ht).trans
    (binary_indegree_le_two N port)


theorem current_ordinary_port_support_card_le_one
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    {port : V} (ho : ¬N.graph.IsHybrid port) {t : ℝ}
    (ht : InCurrentComponentInterval N C port t) :
    (activeRootRouteEdges N.graph C N.root port t).card ≤ 1 :=
  (current_port_support_card_le_indegree N C hcut ht).trans
    (nonhybrid_indegree_le_one N ho)



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

end OriginalComponent15

section OriginalComponent16
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












namespace GProgram.G5.ComponentSupport
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]



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

end OriginalComponent16

section OriginalComponent17
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












namespace GProgram.G5.ParentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
open GProgram.G5.ComponentSupport
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


def IsComponentEntryFor (N : RootedBinary V E X) (entry port : V) : Prop :=
  (entry = N.root ∧ N.graph.SameBlob N.root port) ∨
    ∃ e : E, N.graph.IsBridge e ∧ entry = N.graph.target e ∧
      N.graph.SameBlob (N.graph.target e) port

theorem component_entry_sameBlob (N : RootedBinary V E X) {entry port : V}
    (he : IsComponentEntryFor N entry port) : N.graph.SameBlob entry port := by
  rcases he with ⟨rfl,hb⟩ | ⟨e,_,rfl,hb⟩ <;> exact hb



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

end OriginalComponent17

section OriginalComponent18
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false





























namespace GProgram.SourceForest

open Nanuq.Source
open scoped BigOperators

inductive Genealogy (Copy : Type*)
  | leaf (copy : Copy)
  | graft (left right : Genealogy Copy)
  deriving DecidableEq

variable {Copy V E X : Type*}
variable [Fintype Copy] [DecidableEq Copy]


def Genealogy.leaves : Genealogy Copy → Finset Copy
  | .leaf x => {x}
  | .graft a b => a.leaves ∪ b.leaves


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



structure State (V E Copy : Type*) [DecidableEq Copy] where
  live : Finset Copy
  ancestor : Copy → Copy
  genealogy : Copy → Genealogy Copy
  location : Copy → Location V E
  register : V → Bool
  history : List (SourceEvent V E Copy)


structure Valid (s : State V E Copy) : Prop where
  ancestor_live : ∀ x, s.ancestor x ∈ s.live
  representative : ∀ l ∈ s.live, s.ancestor l = l
  leaf_fiber : ∀ l ∈ s.live, ∀ x, x ∈ (s.genealogy l).leaves ↔ s.ancestor x = l
  wellLabelled : ∀ l ∈ s.live, (s.genealogy l).WellLabelled

variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]



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



def merge (s : State V E Copy) (a b : Copy) : State V E Copy where
  live := s.live.erase b
  ancestor := fun x => if s.ancestor x = b then a else s.ancestor x
  genealogy := fun l => if l = a then .graft (s.genealogy a) (s.genealogy b)
    else s.genealogy l
  location := s.location
  register := s.register
  history := s.history ++ [.merger a b (s.location a)]



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


def transport (s : State V E Copy) (location : Copy → Location V E)
    (event : SourceEvent V E Copy) : State V E Copy :=
  { s with location := location, history := s.history ++ [event] }

theorem transport_valid (s : State V E Copy) (hs : Valid s)
    (location : Copy → Location V E) (event : SourceEvent V E Copy) :
    Valid (transport s location event) :=
  ⟨hs.ancestor_live, hs.representative, hs.leaf_fiber, hs.wellLabelled⟩

variable [DecidableEq E]
variable {N : RootedBinary V E X}


def exitEdge (N : RootedBinary V E X) (s : State V E Copy) (e : E) : State V E Copy :=
  transport s (fun l => if s.location l = .edge e then .node (N.graph.source e)
    else s.location l) (.edgeExit e)


def enterEdge (N : RootedBinary V E X) (s : State V E Copy) (e : E) : State V E Copy :=
  transport s (fun l => if s.location l = .node (N.graph.target e) then .edge e
    else s.location l) (.ordinaryEntry e)


def enterRoot (N : RootedBinary V E X) (s : State V E Copy) : State V E Copy :=
  transport s (fun l => if s.location l = .node N.root then .rootPopulation N.root
    else s.location l) (.rootEntry N.root)

theorem enterRoot_retains_original_root (N : RootedBinary V E X) (s : State V E Copy)
    (l : Copy) (hl : s.location l = .node N.root) :
    (enterRoot N s).location l = .rootPopulation N.root := by
  simp [enterRoot, transport, hl]


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


def Genealogy.joinPruned : Option (Genealogy Copy) → Option (Genealogy Copy) →
    Option (Genealogy Copy)
  | none, b => b
  | a, none => a
  | some a, some b => some (.graft a b)



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




theorem coinCylinderMass_eq_retained_product {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℚ) (retain : Finset A) (wanted : A → Bool) :
    coinCylinderMass p retain wanted = ∏ a ∈ retain, bitWeight p (wanted a) := by
  classical
  simp only [coinCylinderMass, ← cylinderFactor_product]
  rw [← Fintype.prod_sum]
  simp only [cylinderFactor_sum, Finset.prod_ite_mem_eq]



theorem pulse_selected_coin_marginal (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (keep : Finset Copy) (p : ℚ)
    (wanted : AtNode s H.hybrid → Bool) :
    let retain := (Finset.univ : Finset (AtNode s H.hybrid)).filter
      (fun l => (selectedBlock s keep l.val).Nonempty)
    coinCylinderMass p retain wanted = ∏ l ∈ retain, bitWeight p (wanted l) := by
  classical
  exact coinCylinderMass_eq_retained_product p _ wanted





























end GProgram.SourceForest

end OriginalComponent18

section OriginalComponent19
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












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

end OriginalComponent19

section OriginalComponent20
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

















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

end OriginalComponent20

section OriginalComponent21
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

















namespace GProgram.G5.OriginalCoinLaw
open GProgram.SourceForest
open GProgram.G5.QuartetKernel
open scoped BigOperators ENNReal NNReal
variable {Site α : Type*} [Fintype Site] [DecidableEq Site]

@[simp] theorem bitWeight_fair (b : Bool) : bitWeight (1 / 2) b = (1 / 2 : ℚ) := by
  cases b <;> norm_num [bitWeight]


noncomputable def jointBitMass (u v : Site) (a b : Bool) : ℚ := by
  classical
  exact ∑ coin : Site → Bool, independentWeight (1 / 2) coin *
    if coin u = a ∧ coin v = b then 1 else 0



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


def binaryPositions (position : Bool → α) : Fin 2 → α :=
  fun i => if i = 0 then position false else position true



theorem fair_source_meeting_weight [DecidableEq α] {u v : Site} (hne : u ≠ v)
    (p q : Bool → α) :
    (∑ coin : Site → Bool, independentWeight (1 / 2) coin *
      (if p (coin u) = q (coin v) then 1 else 0)) =
      (pairCount (binaryPositions p) (binaryPositions q) : ℚ) / 4 := by
  rw [fair_two_site_expectation hne (fun a b => if p a = q b then 1 else 0)]
  simp only [pairCount, binaryPositions]
  norm_num




end GProgram.G5.OriginalCoinLaw

end OriginalComponent21

section OriginalComponent22
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












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


noncomputable def independentPMF (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    PMF (Site → Bool) :=
  PMF.ofFintype (fun coin => ENNReal.ofReal (independentWeight p coin : ℝ))
    (independentWeight_ennreal_normalized hp hp1)

noncomputable def weightedEvent (p : ℚ) (event : (Site → Bool) → Prop) : ℚ := by
  classical
  exact ∑ coin : Site → Bool, independentWeight p coin * if event coin then 1 else 0



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

end OriginalComponent22

section OriginalComponent23
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false














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

end OriginalComponent23

section OriginalComponent24
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false














namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


def SureExactBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  ∀ R : RouteFamily N, ∃ e : E, selectedPopulationBlock N R B C t e = D


def NoSureNontrivialBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s t : ℝ) : Prop :=
  ∀ u : ℝ, s ≤ u → u < t → ∀ D : Finset X, D ⊆ B → 2 ≤ D.card →
    ¬SureExactBlock N C B D u


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

end OriginalComponent24

section OriginalComponent25
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false












namespace GProgram.G5.SafePast
open Nanuq.Source
open GProgram.G5
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]



def CoOccupy (N : RootedBinary V E X) (R : RouteFamily N)
    (C : Calendar N.graph) (t : ℝ) (x y : X) : Prop :=
  ∃ e : E, e ∈ R.edges x ∧ e ∈ R.edges y ∧ C.Active t e


def PairSureBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B D : Finset X) (t : ℝ) : Prop :=
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ D, x ≠ y → CoOccupy N R C t x y) ∧
  (∀ R : RouteFamily N, ∀ x ∈ D, ∀ y ∈ B, y ∉ D → ¬CoOccupy N R C t x y)



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


def NoPairSureNontrivialBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : Finset X) (s t : ℝ) : Prop :=
  ∀ u : ℝ, s ≤ u → u < t → ∀ D : Finset X, D ⊆ B → 2 ≤ D.card →
    ¬PairSureBlock N C B D u



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



theorem safeAt_of_no_earlier_pair_sure_block
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (B : Finset X) {s t : ℝ} (hstart : SafeAt N C B s)
    (hl : ∀ x ∈ B, C.age (N.leaf x) ≤ s) (hu : t ≤ C.age N.root)
    (hquiet : NoPairSureNontrivialBlock N C B s t) : SafeAt N C B t :=
  safeAt_of_no_earlier_sure_block N C hcut B hstart
    ((noSureNontrivialBlock_iff_pair_predicates N C B hl hu).mpr hquiet)




end GProgram.G5.SafePast

end OriginalComponent25

section OriginalComponent26
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false











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



theorem separated_at_safe_age_never_previously_met (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : Finset X) (R : RouteFamily N)
    {t : ℝ} (hu : t < C.age N.root) (hsafe : SafeAt N C B t)
    {x y : X} (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y)
    (hseparate : ¬CoOccupy N R C t x y) :
    ∀ u : ℝ, u ≤ t → ¬CoOccupy N R C u x y := by
  intro u hut hm
  exact hseparate (coOccupy_persists_to_safe_age N C B R hut hu hsafe hx hy hne hm)





end GProgram.G5.SafePast

end OriginalComponent26

section OriginalComponent27
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false























namespace GProgram.G5.ExponentialGerm

open scoped BigOperators
open Matrix

noncomputable def expSum {n : ℕ} (rate coeff : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ i : Fin n, coeff i * Real.exp (rate i * s)


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




theorem constant_coefficient_eq_of_right_germ {n : ℕ} (rate c d : Fin n → ℝ)
    (hrate : Function.Injective rate) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ s : ℝ, 0 ≤ s → s < ε → expSum rate c s = expSum rate d s)
    (zeroIndex : Fin n) (_hz : rate zeroIndex = 0) : c zeroIndex = d zeroIndex := by
  exact congrFun (coefficients_eq_of_right_germ rate c d hrate hε h) zeroIndex





end GProgram.G5.ExponentialGerm

end OriginalComponent27

section OriginalComponent28
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false













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

end OriginalComponent28

section OriginalComponent29
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false















namespace GProgram.G5.RouteHazard
open Nanuq.Source
open GProgram.G5
open GProgram.G5.SafePast
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]


noncomputable def exposure (G : EdgeGraph V E) (C : Calendar G) (t : ℝ) (e : E) : ℝ :=
  max 0 (min t (C.age (G.source e)) - C.age (G.target e))


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



theorem routeSurvival_add_on_endpoint_gap (N : RootedBinary V E X)
    (C : Calendar N.graph) (rate : E → ℝ) (R : RouteFamily N) (x y : X)
    {t ε u : ℝ} (hgap : EndpointGap N.graph C t ε) (hu : 0 ≤ u) (huε : u < ε) :
    routeSurvival N C rate R x y (t+u) = routeSurvival N C rate R x y t *
      Real.exp ((-currentPairRate N C rate R x y t) * u) := by
  rw [routeSurvival,accumulatedHazard_add_on_endpoint_gap N C rate R x y hgap hu huε,
    neg_add,Real.exp_add]
  simp only [routeSurvival,neg_mul]








end GProgram.G5.RouteHazard

end OriginalComponent29

section OriginalComponent30
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false





















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





end OriginalComponent30

section OriginalComponent31
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

























namespace GProgram.G1

open ProbabilityTheory


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


def registerWeight (p : ℝ) (register : Bool) : ℝ := if register then 1 - p else p

noncomputable def commonBigonConditional (rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  pairForestKernel (if register then rate1 else rate0) 1 separate

noncomputable def retainedRegisterJoint (p rate0 rate1 : ℝ)
    (register separate : Bool) : ℝ :=
  registerWeight p register * commonBigonConditional rate0 rate1 register separate


noncomputable def marginalForestKernel (p rate0 rate1 : ℝ) (separate : Bool) : ℝ :=
  retainedRegisterJoint p rate0 rate1 false separate +
    retainedRegisterJoint p rate0 rate1 true separate



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

end OriginalComponent31

section OriginalComponent32
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

















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



theorem rational_cap3_scalar_witness :
    s2 (1/2) (37/42) (5/6) = 13/14 ∧
    s3 (1/2) (37/42) (5/6) = (13/14)^3 := by
  norm_num [s2,s3]






end GProgram.G4.FourRoot

end OriginalComponent32

section OriginalComponent33
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false























namespace GProgram.G4.IndependentRouting

open scoped BigOperators

noncomputable def bitWeight (u : ℝ) (bit : Bool) : ℝ := if bit then 1-u else u

noncomputable def routingWeight {n : Nat} (u : ℝ) (coin : Fin n → Bool) : ℝ :=
  ∏ i, bitWeight u (coin i)

def count0 {n : Nat} (coin : Fin n → Bool) : Nat := ∑ i, if coin i then 0 else 1
def count1 {n : Nat} (coin : Fin n → Bool) : Nat := ∑ i, if coin i then 1 else 0



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


def FourRootArmLaw (arm : Nat → ℝ) (x : ℝ) : Prop :=
  arm 0 = 1 ∧ arm 1 = 1 ∧ arm 2 = x ∧ arm 3 = x^3 ∧ arm 4 = x^6




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

end OriginalComponent33

section OriginalComponent34
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
















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

end OriginalComponent34

section OriginalComponent35
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false



















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



theorem complete_joint_no_merger_mass (leading : PositiveEdge) (cells : Site → Cell) :
    (∑ c : Color Site, ∑ d : Color Site, observedPair leading cells c d) =
      leading.survival * ∏ i, cellSurvival (cells i) := by
  simp only [observedPair, ← Finset.mul_sum]
  congr 1
  simp_rw [← Fintype.prod_sum]
  rw [← Fintype.prod_sum (fun (i : Site) (a : Bool) =>
    ∑ b : Bool, localPairMass (cells i) a b)]
  simp only [localPairMass_sum]


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




theorem all_input_edge_clock_survival (edge : PositiveEdge) (n : Nat) :
    ((GProgram.G4.PairClocks.pairClockMeasure n)
      (GProgram.G4.PairClocks.noFirstMergeEvent n (-Real.log edge.survival))).toReal =
        edge.survival ^ (n.choose 2) := by
  rw [GProgram.G4.PairClocks.all_root_no_first_merge n
    (le_of_lt (neg_pos.mpr (Real.log_neg edge.positive edge.below_one))),
    neg_neg,Real.exp_log edge.positive]



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



theorem complete_original_parent_readout_injective
    (H : Site → GProgram.G2.OriginalHybridParents N) :
    Function.Injective (observedOriginalParents H) := by
  intro c d he
  funext i
  exact (H i).parent_injective (congrFun he i)



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



theorem path_resolved_C4_reconstruction (leading : PositiveEdge) (cells : Site → Cell) :
    measuredC4 leading cells = sourceC4 leading cells := by
  simp only [measuredC4,sourceC4,cycleDensity]
  simp_rw [reconstructed_kernel_eq_original]



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


theorem sourceC4_word_factorization (leading : PositiveEdge) (cells : Site → Cell) :
    sourceC4 leading cells = (ordinaryScalar leading cells)^4 * ∏ i, bareC4 (cells i).bigon := by
  unfold sourceC4 cycleDensity
  simp_rw [cycle_term_factor]
  simp only [← Finset.mul_sum]
  rw [sum_four_site_products]
  simp only [localCycle_sum,Finset.prod_mul_distrib,Finset.prod_pow,ordinaryScalar,mul_pow]
  ring



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



theorem joint_record_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) (c d : Color (Fin (n+1))) :
    observedPair leading (Fin.cons C rest) c d =
      localPairMass C (c 0) (d 0) * observedPair leading rest (Fin.tail c) (Fin.tail d) := by
  unfold observedPair
  simp only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Fin.tail]
  ring



theorem failure_cons_recursion {n : Nat} (leading : PositiveEdge)
    (C : Cell) (rest : Fin n → Cell) :
    outcomeMass leading (Fin.cons C rest) none = (1-leading.survival) +
      leading.survival * ((1-cellSurvival C) + cellSurvival C *
        (1-∏ i, cellSurvival (rest i))) := by
  simp only [outcomeMass,totalNoMerger,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  ring




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



theorem ordinary_no_bigon_scalar [IsEmpty Site] (leading : PositiveEdge) (cells : Site → Cell) :
    dataPairSurvival leading cells = leading.survival ∧
      dataC4 leading cells = leading.survival ^ 4 := by
  rw [dataPairSurvival_eq,normalized_PMF_data_C4_reconstruction]
  simp [totalNoMerger,sourceC4_word_factorization,ordinaryScalar]



















end GProgram.G4.PathResolved

end OriginalComponent35

section OriginalComponent36
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false














namespace UnifiedLean.Source.NativeParentRouting
open Nanuq.Source
open GProgram.G5
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

abbrev Nonroot (N : RootedBinary V E X) := {v : V // v ≠ N.root}



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



noncomputable def compiledRoute (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) : List E :=
  Classical.choose (selected_original_path_exists N C P v)

theorem compiledRoute_source_spec (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) :
    EdgePath N.graph N.root v (compiledRoute N C P v) ∧
      RespectsSelector N P (compiledRoute N C P v) :=
  Classical.choose_spec (selected_original_path_exists N C P v)



noncomputable def compiledRouteFamily (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : X → Hybrid N → Bool) : RouteFamily N where
  edges x := compiledRoute N C (coinSelector N H (coin x)) (N.leaf x)
  valid x := (compiledRoute_source_spec N C (coinSelector N H (coin x)) (N.leaf x)).1



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

end OriginalComponent36

section OriginalComponent37
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false















namespace UnifiedLean.Source.NativePairClockLaw
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]



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


theorem original_clock_survival_eq_routeSurvival (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) (t : ℝ) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      routeSurvival N C r.edge R x y t *
        Real.exp (-(r.ancestral * max 0 (t-C.age N.root))) := by
  rw [original_clock_no_merger_probability, native_hazard_decomposition,
    neg_add, Real.exp_add, routeSurvival]



theorem below_root_original_clock_law (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (R : RouteFamily N)
    (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    (originalClockMeasure r (noFirstMerger N C R x y t)).toReal =
      routeSurvival N C r.edge R x y t := by
  rw [original_clock_survival_eq_routeSurvival, max_eq_left (sub_nonpos.mpr ht)]
  simp



theorem compiled_original_pair_probability (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E) (H : OriginalParentRegistry N)
    (coin : X → Hybrid N → Bool) (x y : X) {t : ℝ} (ht : t ≤ C.age N.root) :
    (originalClockMeasure r (noFirstMerger N C (compiledRouteFamily N C H coin) x y t)).toReal =
      routeSurvival N C r.edge (compiledRouteFamily N C H coin) x y t :=
  below_root_original_clock_law N C r (compiledRouteFamily N C H coin) x y ht









end UnifiedLean.Source.NativePairClockLaw

end OriginalComponent37

section OriginalComponent38
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
















namespace UnifiedLean.Source.NativeIndependentPairMixture
open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]


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


noncomputable def nativePairMeasure (N : RootedBinary V E X)
    (p : HybridProbabilities N) (r : PositivePairRates E) :
    Measure (NativeCoinSeed N × (Option E → ℝ)) :=
  (originalCoinPMF N p).toMeasure.prod (originalClockMeasure r)




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

end OriginalComponent38

section OriginalComponent39
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false










namespace GProgram.G7.OriginalRelabelling
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture
open scoped BigOperators
variable {V E W F X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]

def graph (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) : EdgeGraph W F where
  source f := v (G.source (e.symm f))
  target f := v (G.target (e.symm f))

@[simp] theorem graph_source (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : E) :
    (graph G v e).source (e a) = v (G.source a) := by simp [graph]
@[simp] theorem graph_target (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : E) :
    (graph G v e).target (e a) = v (G.target a) := by simp [graph]

@[simp] theorem dstep_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a b : W) :
    (graph G v e).DStep a b ↔ G.DStep (v.symm a) (v.symm b) := by
  constructor
  · rintro ⟨f, hs, ht⟩
    exact ⟨e.symm f, by simpa [graph] using congrArg v.symm hs,
      by simpa [graph] using congrArg v.symm ht⟩
  · rintro ⟨f, hs, ht⟩
    refine ⟨e f, ?_, ?_⟩
    · simpa using congrArg v hs
    · simpa using congrArg v ht

@[simp] theorem dreach_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a b : W) :
    (graph G v e).DReach a b ↔ G.DReach (v.symm a) (v.symm b) := by
  constructor
  · exact Relation.ReflTransGen.lift v.symm (fun a b h => (dstep_iff G v e a b).mp h) a b
  · intro h
    have h' := Relation.ReflTransGen.lift v
      (fun a b h => (dstep_iff G v e (v a) (v b)).mpr (by simpa using h)) _ _ h
    simpa [Function.onFun, EdgeGraph.DReach, EdgeGraph.UReach] using h'

theorem acyclic (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (h : G.Acyclic) : (graph G v e).Acyclic := by
  intro a ha
  apply h (v.symm a)
  exact Relation.TransGen.lift v.symm (fun a b h => (dstep_iff G v e a b).mp h) _ _ ha

@[simp] theorem avoidReach_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (z a b : W) : (graph G v e).AvoidReach z a b ↔
      G.AvoidReach (v.symm z) (v.symm a) (v.symm b) := by
  constructor
  · rintro ⟨ha, hb, hp⟩
    refine ⟨fun h => ha (v.symm.injective h), fun h => hb (v.symm.injective h), ?_⟩
    exact Relation.ReflTransGen.lift v.symm
      (fun a b h => ⟨(dstep_iff G v e a b).mp h.1,
        fun he => h.2.1 (v.symm.injective he), fun he => h.2.2 (v.symm.injective he)⟩) _ _ hp
  · rintro ⟨ha, hb, hp⟩
    refine ⟨fun h => ha (congrArg v.symm h), fun h => hb (congrArg v.symm h), ?_⟩
    have hp' := Relation.ReflTransGen.lift (p := fun x y => (graph G v e).DStep x y ∧ x ≠ z ∧ y ≠ z) v (fun x y h =>
      show (graph G v e).DStep (v x) (v y) ∧ v x ≠ z ∧ v y ≠ z from
        ⟨(dstep_iff G v e (v x) (v y)).mpr (by simpa using h.1),
          fun he => h.2.1 (by simpa using congrArg v.symm he),
          fun he => h.2.2 (by simpa using congrArg v.symm he)⟩) _ _ hp
    simpa [Function.onFun] using hp'

@[simp] theorem dominates_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (r z a : W) : (graph G v e).Dominates r z a ↔
      G.Dominates (v.symm r) (v.symm z) (v.symm a) := by
  simp only [EdgeGraph.Dominates, avoidReach_iff]

@[simp] theorem inDegree_eq (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : W) :
    (graph G v e).inDegree a = G.inDegree (v.symm a) := by
  classical
  simp only [EdgeGraph.inDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv e
  intro f
  simp only [graph_target]
  simp only [v.eq_symm_apply]

@[simp] theorem outDegree_eq (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : W) :
    (graph G v e).outDegree a = G.outDegree (v.symm a) := by
  classical
  simp only [EdgeGraph.outDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  symm
  apply Fintype.sum_equiv e
  intro f
  simp only [graph_source]
  simp only [v.eq_symm_apply]

@[simp] theorem hybrid_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (a : W) :
    (graph G v e).IsHybrid a ↔ G.IsHybrid (v.symm a) := by
  simp only [EdgeGraph.IsHybrid, inDegree_eq, outDegree_eq]


def network (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) : RootedBinary W F X where
  graph := graph N.graph v e
  root := v N.root
  leaf := N.leaf.trans v.toEmbedding
  at_least_two_taxa := N.at_least_two_taxa
  root_degrees := by simpa using N.root_degrees
  leaf_degrees x := by simpa using N.leaf_degrees x
  internal_degrees a hr hl := by
    have hr' : v.symm a ≠ N.root := fun h => hr (by simpa using congrArg v h)
    have hl' : ∀ x, N.leaf x ≠ v.symm a := by
      intro x hx
      exact hl x (by simpa using congrArg v hx)
    simpa using N.internal_degrees (v.symm a) hr' hl'
  acyclic := acyclic N.graph v e N.acyclic
  rooted a := by simpa using N.rooted (v.symm a)
  least_stable a h := by
    have ho : ∀ x, N.graph.Dominates N.root (v.symm a) (N.leaf x) := by
      intro x
      simpa using h x
    have he := N.least_stable (v.symm a) ho
    simpa using congrArg v he


def calendar (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Calendar N.graph) : Calendar (network N v e).graph where
  age a := c.age (v.symm a)
  edge_older f := by simpa [network, graph] using c.edge_older (e.symm f)


def rates (e : E ≃ F) (r : PositivePairRates E) : PositivePairRates F where
  edge f := r.edge (e.symm f)
  edge_pos f := r.edge_pos (e.symm f)
  ancestral := r.ancestral
  ancestral_pos := r.ancestral_pos

def hybrids (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) :
    Hybrid N ≃ Hybrid (network N v e) where
  toFun h := ⟨v h.val, by simpa [network] using h.property⟩
  invFun h := ⟨v.symm h.val, by simpa [network] using h.property⟩
  left_inv h := by apply Subtype.ext; simp
  right_inv h := by apply Subtype.ext; simp

def inheritance (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (g : HybridProbabilities N) : HybridProbabilities (network N v e) where
  gamma h := g.gamma ((hybrids N v e).symm h)
  positive h := g.positive _
  below_one h := g.below_one _

theorem calendar_duration_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Calendar N.graph) (f : E) :
    (calendar N v e c).age ((network N v e).graph.source (e f)) -
      (calendar N v e c).age ((network N v e).graph.target (e f)) =
      c.age (N.graph.source f) - c.age (N.graph.target f) := by
  simp [calendar, network, graph]

theorem hazard_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (c : Calendar N.graph) (r : PositivePairRates E) (f : E) :
    (rates e r).edge (e f) *
      ((calendar N v e c).age ((network N v e).graph.source (e f)) -
       (calendar N v e c).age ((network N v e).graph.target (e f))) =
      r.edge f * (c.age (N.graph.source f) - c.age (N.graph.target f)) := by
  rw [calendar_duration_preserved]
  simp [rates]



def parents (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (h : GProgram.G2.OriginalHybridParents N) :
    GProgram.G2.OriginalHybridParents (network N v e) where
  hybrid := v h.hybrid
  isHybrid := by simpa [network] using h.isHybrid
  parent0 := e h.parent0
  parent1 := e h.parent1
  target0 := by simpa [network] using congrArg v h.target0
  target1 := by simpa [network] using congrArg v h.target1
  different := fun he => h.different (e.injective he)

def registry (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : OriginalParentRegistry N) : OriginalParentRegistry (network N v e) where
  parents h := parents N v e (H.parents ((hybrids N v e).symm h))
  original_site h := by
    have he := congrArg v (H.original_site ((hybrids N v e).symm h))
    simpa [parents, hybrids] using he

theorem parent_bit_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (H : OriginalParentRegistry N) (h : Hybrid N) (b : Bool) :
    ((registry N v e H).parents ((hybrids N v e) h)).parent b =
      e ((H.parents h).parent b) := by
  cases b <;> simp [registry, parents, GProgram.G2.OriginalHybridParents.parent]

theorem inheritance_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (g : HybridProbabilities N) (h : Hybrid N) :
    (inheritance N v e g).gamma ((hybrids N v e) h) = g.gamma h := by
  simp [inheritance]

@[simp] theorem inc_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (f : F) (a b : W) : (graph G v e).Inc f a b ↔
      G.Inc (e.symm f) (v.symm a) (v.symm b) := by
  simp only [EdgeGraph.Inc, graph]
  simp only [← v.eq_symm_apply]

@[simp] theorem ustep_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (keep : F → Prop) (a b : W) : (graph G v e).UStep keep a b ↔
      G.UStep (fun f => keep (e f)) (v.symm a) (v.symm b) := by
  constructor
  · rintro ⟨f, hf, hp⟩
    exact ⟨e.symm f, by simpa using hf, (inc_iff G v e f a b).mp hp⟩
  · rintro ⟨f, hf, hp⟩
    exact ⟨e f, hf, (inc_iff G v e (e f) a b).mpr (by simpa using hp)⟩

@[simp] theorem ureach_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F)
    (keep : F → Prop) (a b : W) : (graph G v e).UReach keep a b ↔
      G.UReach (fun f => keep (e f)) (v.symm a) (v.symm b) := by
  constructor
  · exact Relation.ReflTransGen.lift v.symm
      (fun a b h => (ustep_iff G v e keep a b).mp h) a b
  · intro h
    have h' := Relation.ReflTransGen.lift v
      (fun a b h => (ustep_iff G v e keep (v a) (v b)).mpr (by simpa using h)) _ _ h
    simpa [Function.onFun, EdgeGraph.DReach, EdgeGraph.UReach] using h'

@[simp] theorem bridge_iff (G : EdgeGraph V E) (v : V ≃ W) (e : E ≃ F) (f : F) :
    (graph G v e).IsBridge f ↔ G.IsBridge (e.symm f) := by
  change ¬ (graph G v e).UReach (fun a => a ≠ f)
    ((graph G v e).source f) ((graph G v e).target f) ↔
    ¬ G.UReach (fun a => a ≠ e.symm f) (G.source (e.symm f)) (G.target (e.symm f))
  rw [ureach_iff]
  simp only [graph, Equiv.symm_apply_apply]
  have hk : (fun a => e a ≠ f) = (fun a => a ≠ e.symm f) := by
    funext a
    apply propext
    constructor
    · intro h he
      apply h
      simpa using congrArg e he
    · intro h he
      apply h
      simpa using congrArg e.symm he
  rw [hk]

theorem cut_child_preserved (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    (hc : ∀ f, N.graph.IsHybrid (N.graph.source f) → N.graph.IsBridge f) :
    ∀ f, (network N v e).graph.IsHybrid ((network N v e).graph.source f) →
      (network N v e).graph.IsBridge f := by
  intro f hf
  apply (bridge_iff N.graph v e f).mpr
  apply hc (e.symm f)
  change (graph N.graph v e).IsHybrid ((graph N.graph v e).source f) at hf
  rw [hybrid_iff] at hf
  simpa [graph] using hf



end GProgram.G7.OriginalRelabelling

end OriginalComponent39

section OriginalComponent40
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false







namespace GProgram.G7.OriginalFiniteEncoding
open Nanuq.Source
open UnifiedLean.Source.NativeParentRouting
open GProgram.G7.OriginalRelabelling
open scoped Classical
variable {V E X ID : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype ID]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq ID]

def vertexCount (n r : ℕ) : ℕ := 2*n + 2*r - 1
def edgeCount (n r : ℕ) : ℕ := 2*n + 3*r - 2

theorem hybrid_card (N : RootedBinary V E X) : Fintype.card (Hybrid N) = hybridCount N := by
  simp [Hybrid, hybridCount, Fintype.card_subtype]

theorem original_registry_sizes (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    Fintype.card V = vertexCount (Fintype.card X) (Fintype.card ID) ∧
    Fintype.card E = edgeCount (Fintype.card X) (Fintype.card ID) := by
  have hi : hybridCount N = Fintype.card ID := (hybrid_card N).symm.trans (Fintype.card_congr ids).symm
  obtain ⟨hv,he⟩ := original_census N
  rw [hi] at hv he
  unfold vertexCount edgeCount
  omega

noncomputable def vertexNumbering (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    V ≃ Fin (vertexCount (Fintype.card X) (Fintype.card ID)) :=
  Fintype.equivFinOfCardEq (original_registry_sizes N ids).1

noncomputable def edgeNumbering (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    E ≃ Fin (edgeCount (Fintype.card X) (Fintype.card ID)) :=
  Fintype.equivFinOfCardEq (original_registry_sizes N ids).2



abbrev Code (X ID : Type*) [Fintype X] [Fintype ID] :=
  let nv := vertexCount (Fintype.card X) (Fintype.card ID)
  let ne := edgeCount (Fintype.card X) (Fintype.card ID)
  (Fin ne → Fin nv) × (Fin ne → Fin nv) × Fin nv ×
    (X → Fin nv) × (ID → Fin nv) × (ID → Bool → Fin ne)

def allCodes : Finset (Code X ID) := Finset.univ

noncomputable def encode (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) : Code X ID :=
  let v := vertexNumbering N ids
  let e := edgeNumbering N ids
  ⟨fun f => v (N.graph.source (e.symm f)),
   fun f => v (N.graph.target (e.symm f)), v N.root,
   fun x => v (N.leaf x), fun h => v (ids h).val,
   fun h b => e ((H.parents (ids h)).parent b)⟩



theorem every_original_source_has_code (N : RootedBinary V E X)
    (ids : ID ≃ Hybrid N) (H : OriginalParentRegistry N) :
    encode N ids H ∈ (allCodes : Finset (Code X ID)) := Finset.mem_univ _

noncomputable def numberedSource (N : RootedBinary V E X) (ids : ID ≃ Hybrid N) :
    RootedBinary (Fin (vertexCount (Fintype.card X) (Fintype.card ID)))
      (Fin (edgeCount (Fintype.card X) (Fintype.card ID))) X :=
  network N (vertexNumbering N ids) (edgeNumbering N ids)



theorem encoded_graph_exact (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) :
    (encode N ids H).1 = (numberedSource N ids).graph.source ∧
    (encode N ids H).2.1 = (numberedSource N ids).graph.target ∧
    (encode N ids H).2.2.1 = (numberedSource N ids).root ∧
    (encode N ids H).2.2.2.1 = (fun x => (numberedSource N ids).leaf x) := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem encoded_parent_target (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) (h : ID) (b : Bool) :
    (encode N ids H).2.1 ((encode N ids H).2.2.2.2.2 h b) =
      (encode N ids H).2.2.2.2.1 h := by
  simp only [encode, Equiv.symm_apply_apply]
  exact congrArg (vertexNumbering N ids) (registry_parent_target N H (ids h) b)

theorem encoded_parent_bits_distinct (N : RootedBinary V E X) (ids : ID ≃ Hybrid N)
    (H : OriginalParentRegistry N) (h : ID) :
    (encode N ids H).2.2.2.2.2 h false ≠ (encode N ids H).2.2.2.2.2 h true := by
  intro he
  have he' := (edgeNumbering N ids).injective he
  exact (H.parents (ids h)).different (by simpa [GProgram.G2.OriginalHybridParents.parent] using he')





end GProgram.G7.OriginalFiniteEncoding

end OriginalComponent40

section OriginalComponent41
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false









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

end OriginalComponent41

section OriginalComponent42
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false









namespace GProgram.G7.OriginalAdmission
open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding
open GProgram.G7.FiniteReachability
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

instance decidableDStep (G : EdgeGraph V E) : DecidableRel G.DStep :=
  fun a b => inferInstanceAs (Decidable (∃ e, G.source e = a ∧ G.target e = b))
instance decidableDReach (G : EdgeGraph V E) : DecidableRel G.DReach :=
  decideReach G.DStep
instance decidableTransGen (R : V → V → Prop) [DecidableRel R] (a b : V) :
    Decidable (Relation.TransGen R a b) := by
  letI : DecidableRel (Relation.ReflTransGen R) := decideReach R
  exact decidable_of_iff (∃ c, R a c ∧ Relation.ReflTransGen R c b)
    Relation.TransGen.head'_iff.symm
instance decidableAcyclic (G : EdgeGraph V E) : Decidable G.Acyclic :=
  inferInstanceAs (Decidable (∀ a, ¬ Relation.TransGen G.DStep a a))
instance decidableAvoidReach (G : EdgeGraph V E) (z a b : V) :
    Decidable (G.AvoidReach z a b) := by
  letI : DecidableRel (Relation.ReflTransGen (fun x y => G.DStep x y ∧ x ≠ z ∧ y ≠ z)) :=
    decideReach _
  exact inferInstanceAs (Decidable (a ≠ z ∧ b ≠ z ∧
    Relation.ReflTransGen (fun x y => G.DStep x y ∧ x ≠ z ∧ y ≠ z) a b))
instance decidableDominates (G : EdgeGraph V E) (r z a : V) : Decidable (G.Dominates r z a) :=
  inferInstanceAs (Decidable (¬G.AvoidReach z r a))
instance decidableInc (G : EdgeGraph V E) (e : E) (a b : V) : Decidable (G.Inc e a b) :=
  inferInstanceAs (Decidable ((G.source e = a ∧ G.target e = b) ∨ (G.source e = b ∧ G.target e = a)))
instance decidableUStep (G : EdgeGraph V E) (keep : E → Prop) [DecidablePred keep] :
    DecidableRel (G.UStep keep) :=
  fun a b => inferInstanceAs (Decidable (∃ e, keep e ∧ G.Inc e a b))
instance decidableUReach (G : EdgeGraph V E) (keep : E → Prop) [DecidablePred keep] :
    DecidableRel (G.UReach keep) := decideReach (G.UStep keep)
instance decidableBridge (G : EdgeGraph V E) (e : E) : Decidable (G.IsBridge e) :=
  inferInstanceAs (Decidable (¬ G.UReach (fun f => f ≠ e) (G.source e) (G.target e)))
instance decidableHybrid (G : EdgeGraph V E) (v : V) : Decidable (G.IsHybrid v) :=
  inferInstanceAs (Decidable (G.inDegree v = 2 ∧ G.outDegree v = 1))

variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]
abbrev NV := Fin (vertexCount (Fintype.card X) (Fintype.card ID))
abbrev NE := Fin (edgeCount (Fintype.card X) (Fintype.card ID))
def codeGraph (c : Code X ID) : EdgeGraph (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)) :=
  ⟨c.1,c.2.1⟩
def codeRoot (c : Code X ID) : NV (X:=X) (ID:=ID) := c.2.2.1
def codeLeaf (c : Code X ID) : X → NV (X:=X) (ID:=ID) := c.2.2.2.1

def BinaryValid (c : Code X ID) : Prop :=
  Function.Injective (codeLeaf c) ∧ 2 ≤ Fintype.card X ∧
  ((codeGraph c).inDegree (codeRoot c) = 0 ∧ (codeGraph c).outDegree (codeRoot c) = 2) ∧
  (∀ x, (codeGraph c).inDegree (codeLeaf c x) = 1 ∧ (codeGraph c).outDegree (codeLeaf c x) = 0) ∧
  (∀ a, a ≠ codeRoot c → (∀ x, codeLeaf c x ≠ a) →
    ((codeGraph c).inDegree a = 1 ∧ (codeGraph c).outDegree a = 2) ∨ (codeGraph c).IsHybrid a) ∧
  (codeGraph c).Acyclic ∧
  (∀ a, (codeGraph c).DReach (codeRoot c) a) ∧
  (∀ a, (∀ x, (codeGraph c).Dominates (codeRoot c) a (codeLeaf c x)) → a = codeRoot c)

instance decidableBinaryValid (c : Code X ID) : Decidable (BinaryValid c) := by
  unfold BinaryValid Function.Injective
  infer_instance

def CutChild (c : Code X ID) : Prop :=
  ∀ f, (codeGraph c).IsHybrid ((codeGraph c).source f) → (codeGraph c).IsBridge f
instance decidableCutChild (c : Code X ID) : Decidable (CutChild c) := by
  unfold CutChild
  infer_instance



def sourceOfValid (c : Code X ID) (h : BinaryValid c) :
    RootedBinary (NV (X:=X) (ID:=ID)) (NE (X:=X) (ID:=ID)) X where
  graph := codeGraph c
  root := codeRoot c
  leaf := ⟨codeLeaf c,h.1⟩
  at_least_two_taxa := h.2.1
  root_degrees := h.2.2.1
  leaf_degrees := h.2.2.2.1
  internal_degrees := h.2.2.2.2.1
  acyclic := h.2.2.2.2.2.1
  rooted := h.2.2.2.2.2.2.1
  least_stable := h.2.2.2.2.2.2.2

def binaryCutChildCodes : Finset (Code X ID) :=
  allCodes.filter (fun c => BinaryValid c ∧ CutChild c)

theorem encoded_binary_valid {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N) :
    BinaryValid (encode N ids H) := by
  let M := numberedSource N ids
  exact ⟨M.leaf.injective, M.at_least_two_taxa, M.root_degrees, M.leaf_degrees,
    M.internal_degrees, M.acyclic, M.rooted, M.least_stable⟩

theorem encoded_cut_child {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N)
    (hc : ∀ f, N.graph.IsHybrid (N.graph.source f) → N.graph.IsBridge f) :
    CutChild (encode N ids H) :=
  GProgram.G7.OriginalRelabelling.cut_child_preserved N _ _ hc

def codeSite (c : Code X ID) : ID → NV (X:=X) (ID:=ID) := c.2.2.2.2.1
def codeParent (c : Code X ID) : ID → Bool → NE (X:=X) (ID:=ID) := c.2.2.2.2.2

def RegistryValid (c : Code X ID) : Prop :=
  Function.Injective (codeSite c) ∧
  (∀ i, (codeGraph c).IsHybrid (codeSite c i)) ∧
  (∀ a, (codeGraph c).IsHybrid a → ∃ i, codeSite c i = a) ∧
  (∀ i b, (codeGraph c).target (codeParent c i b) = codeSite c i) ∧
  (∀ i, codeParent c i false ≠ codeParent c i true)
instance decidableRegistryValid (c : Code X ID) : Decidable (RegistryValid c) := by
  unfold RegistryValid Function.Injective
  infer_instance



def registeredBinaryCutChildCodes : Finset (Code X ID) :=
  allCodes.filter (fun c => BinaryValid c ∧ CutChild c ∧ RegistryValid c)

theorem encoded_registry_valid {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N) :
    RegistryValid (encode N ids H) := by
  refine ⟨?_, ?_, ?_, encoded_parent_target N ids H, encoded_parent_bits_distinct N ids H⟩
  · intro i j he
    apply ids.injective
    apply Subtype.ext
    exact (vertexNumbering N ids).injective he
  · intro i
    change (GProgram.G7.OriginalRelabelling.graph N.graph (vertexNumbering N ids)
      (edgeNumbering N ids)).IsHybrid ((vertexNumbering N ids) (ids i).val)
    simpa using (ids i).property
  · intro a ha
    have ho : N.graph.IsHybrid ((vertexNumbering N ids).symm a) := by
      exact (GProgram.G7.OriginalRelabelling.hybrid_iff N.graph _ _ a).mp ha
    refine ⟨ids.symm ⟨(vertexNumbering N ids).symm a,ho⟩, ?_⟩
    simp [codeSite,encode]

theorem every_registered_source_survives_filter {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (N : RootedBinary V E X)
    (ids : ID ≃ UnifiedLean.Source.NativeParentRouting.Hybrid N)
    (H : UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry N)
    (hc : ∀ f, N.graph.IsHybrid (N.graph.source f) → N.graph.IsBridge f) :
    encode N ids H ∈ (registeredBinaryCutChildCodes : Finset (Code X ID)) := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,encoded_binary_valid N ids H,
    encoded_cut_child N ids H hc,encoded_registry_valid N ids H⟩

open UnifiedLean.Source.NativeParentRouting



def decodedHybridMap (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    ID → Hybrid (sourceOfValid c hb) := fun i => ⟨codeSite c i,hr.2.1 i⟩

theorem decodedHybridMap_bijective (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    Function.Bijective (decodedHybridMap c hb hr) := by
  constructor
  · intro i j he
    exact hr.1 (congrArg Subtype.val he)
  · intro h
    obtain ⟨i,hi⟩ := hr.2.2.1 h.val h.property
    exact ⟨i,Subtype.ext hi⟩

def decodedIDs (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    ID ≃ Hybrid (sourceOfValid c hb) where
  toFun := decodedHybridMap c hb hr
  invFun := Fintype.bijInv (decodedHybridMap_bijective c hb hr)
  left_inv := Fintype.leftInverse_bijInv _
  right_inv := Fintype.rightInverse_bijInv _

def decodedRegistry (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c) :
    OriginalParentRegistry (sourceOfValid c hb) where
  parents h := {
    hybrid := h.val
    isHybrid := h.property
    parent0 := codeParent c ((decodedIDs c hb hr).symm h) false
    parent1 := codeParent c ((decodedIDs c hb hr).symm h) true
    target0 := by
      have he := hr.2.2.2.1 ((decodedIDs c hb hr).symm h) false
      have hs := congrArg Subtype.val ((decodedIDs c hb hr).apply_symm_apply h)
      exact he.trans hs
    target1 := by
      have he := hr.2.2.2.1 ((decodedIDs c hb hr).symm h) true
      have hs := congrArg Subtype.val ((decodedIDs c hb hr).apply_symm_apply h)
      exact he.trans hs
    different := hr.2.2.2.2 _ }
  original_site _ := rfl

theorem decoded_parent_exact (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (i : ID) (b : Bool) :
    ((decodedRegistry c hb hr).parents ((decodedIDs c hb hr) i)).parent b = codeParent c i b := by
  cases b <;> simp [decodedRegistry,GProgram.G2.OriginalHybridParents.parent]



end GProgram.G7.OriginalAdmission

end OriginalComponent42

section OriginalComponent43









namespace Astra.NativeOrderedBankLayout

variable {V E H : Type*} {nv ne nh : ℕ}


def populationEquiv (edges : E ≃ Fin ne) : Option E ≃ Fin (ne + 1) :=
  (Equiv.optionCongr edges).trans finSuccEquivLast.symm


def bankEquiv (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) : V ⊕ (Option E ⊕ H) ≃ Fin (nv + ne + 1 + nh) :=
  ((Equiv.sumCongr vertices
      ((Equiv.sumCongr (populationEquiv edges) hybrids).trans finSumFinEquiv)).trans
    finSumFinEquiv).trans (finCongr (by simp [Nat.add_assoc]))

@[simp] theorem population_some (edges : E ≃ Fin ne) (e : E) :
    populationEquiv edges (some e) = (edges e).castSucc := by
  simp [populationEquiv]

@[simp] theorem population_none (edges : E ≃ Fin ne) :
    populationEquiv edges none = Fin.last ne := by
  simp [populationEquiv]

@[simp] theorem age_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (v : V) :
    (bankEquiv vertices edges hybrids (.inl v)).val = (vertices v).val := by
  simp [bankEquiv]

@[simp] theorem edge_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (e : E) :
    (bankEquiv vertices edges hybrids (.inr (.inl (some e)))).val =
      nv + (edges e).val := by
  simp [bankEquiv, populationEquiv]

@[simp] theorem ancestral_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) :
    (bankEquiv vertices edges hybrids (.inr (.inl none))).val = nv + ne := by
  simp [bankEquiv, populationEquiv]

@[simp] theorem hybrid_index (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (h : H) :
    (bankEquiv vertices edges hybrids (.inr (.inr h))).val =
      nv + ne + 1 + (hybrids h).val := by
  simp [bankEquiv, Nat.add_assoc]


theorem ancestral_fiber (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) (q : V ⊕ (Option E ⊕ H)) :
    (bankEquiv vertices edges hybrids q).val = nv + ne ↔ q = .inr (.inl none) := by
  constructor
  · intro h
    apply (bankEquiv vertices edges hybrids).injective
    apply Fin.ext
    simpa only [ancestral_index] using h
  · rintro rfl
    exact ancestral_index vertices edges hybrids


theorem ordered_bank_positions (vertices : V ≃ Fin nv) (edges : E ≃ Fin ne)
    (hybrids : H ≃ Fin nh) :
    (∀ v, (bankEquiv vertices edges hybrids (.inl v)).val = (vertices v).val) ∧
    (∀ e, (bankEquiv vertices edges hybrids (.inr (.inl (some e)))).val =
      nv + (edges e).val) ∧
    (bankEquiv vertices edges hybrids (.inr (.inl none))).val = nv + ne ∧
    (∀ h, (bankEquiv vertices edges hybrids (.inr (.inr h))).val =
      nv + ne + 1 + (hybrids h).val) ∧
    (∀ q, (bankEquiv vertices edges hybrids q).val = nv + ne ↔
      q = .inr (.inl none)) := by
  exact ⟨age_index vertices edges hybrids, edge_index vertices edges hybrids,
    ancestral_index vertices edges hybrids, hybrid_index vertices edges hybrids,
    ancestral_fiber vertices edges hybrids⟩

end Astra.NativeOrderedBankLayout

end OriginalComponent43

section OriginalComponent44










namespace Astra.OriginalCodeBankLayout

open Nanuq.Source
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open UnifiedLean.Source.NativeParentRouting

variable {X ID : Type*} [Fintype X] [Fintype ID]
variable [DecidableEq X] [DecidableEq ID] {nh : ℕ}


noncomputable def layout (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (idOrder : ID ≃ Fin nh) :
    (NV (X := X) (ID := ID) ⊕
      (Option (NE (X := X) (ID := ID)) ⊕ Hybrid (sourceOfValid c hb))) ≃
      Fin (vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) + 1 + nh) :=
  Astra.NativeOrderedBankLayout.bankEquiv
    (Equiv.refl (NV (X := X) (ID := ID)))
    (Equiv.refl (NE (X := X) (ID := ID)))
    ((decodedIDs c hb hr).symm.trans idOrder)

theorem age_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (v : NV (X := X) (ID := ID)) :
    (layout c hb hr idOrder (.inl v)).val = v.val := by
  simp [layout]

theorem edge_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (e : NE (X := X) (ID := ID)) :
    (layout c hb hr idOrder (.inr (.inl (some e)))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) + e.val := by
  simp [layout]

theorem ancestral_position (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (idOrder : ID ≃ Fin nh) :
    (layout c hb hr idOrder (.inr (.inl none))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) := by
  simp [layout]

theorem hybrid_position (c : Code X ID) (hb : BinaryValid c) (hr : RegistryValid c)
    (idOrder : ID ≃ Fin nh) (i : ID) :
    (layout c hb hr idOrder (.inr (.inr (decodedIDs c hb hr i)))).val =
      vertexCount (Fintype.card X) (Fintype.card ID) +
        edgeCount (Fintype.card X) (Fintype.card ID) + 1 + (idOrder i).val := by
  simp [layout]


theorem parent_occurrence (c : Code X ID) (hb : BinaryValid c)
    (hr : RegistryValid c) (i : ID) (b : Bool) :
    ((decodedRegistry c hb hr).parents (decodedIDs c hb hr i)).parent b =
      codeParent c i b :=
  decoded_parent_exact c hb hr i b

end Astra.OriginalCodeBankLayout

end OriginalComponent44
