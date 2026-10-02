import G5CalendarRoutes
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Actual finite source countercheck: cut-child cannot be dropped

New source-level stress test: dot's dedicated Lean lane, 2026-10-01.
The witness has four original labelled tips, binary original degrees, a genuine
LSA root, directed acyclicity, and strictly positive contemporary-tip calendar
edges. The first hybrid's child is not a bridge. Its downstream deletion
component includes a tip that is not a directed descendant of that child.

This is a counterexample to a WEAKER RootedBinary-only source contract, not to
the accepted cut-child source theorem. No full planarity/galled admission is
claimed. The class excludes this witness precisely at the tested child-cut
premise; the accepted G5 proof already retains that premise.
-/

namespace GProgram.G5.CutChildTest

open Nanuq.Source

def graph : EdgeGraph (Fin 11) (Fin 12) where
  source e := match e.val with
    | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2 | 5 => 2
    | 6 => 3 | 7 => 4 | 8 => 4 | 9 => 5 | _ => 8
  target e := match e.val with
    | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 8 | 4 => 3 | 5 => 5
    | 6 => 4 | 7 => 5 | 8 => 6 | 9 => 7 | 10 => 9 | _ => 10

def leaf : Fin 4 ↪ Fin 11 where
  toFun x := ⟨if x.val < 2 then x.val + 6 else x.val + 7, by split_ifs <;> omega⟩
  inj' := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    dsimp at h
    split_ifs at h <;> omega

theorem edge_rank {a b : Fin 11} (h : graph.DStep a b) : a.val < b.val := by
  obtain ⟨e, hs, ht⟩ := h
  rw [← hs, ← ht]
  fin_cases e <;> decide +kernel

theorem rank_increases {a b : Fin 11} (h : Relation.TransGen graph.DStep a b) :
    a.val < b.val := by
  induction h with
  | single hstep => exact edge_rank hstep
  | tail _ hstep ih => exact ih.trans (edge_rank hstep)

theorem graph_acyclic : graph.Acyclic := by
  intro a h
  exact Nat.lt_irrefl _ (rank_increases h)

theorem graph_rooted (a : Fin 11) : graph.DReach 0 a := by
  have hu : graph.DReach 0 1 := .single ⟨0, rfl, rfl⟩
  have hv : graph.DReach 0 2 := .single ⟨1, rfl, rfl⟩
  have hh : graph.DReach 0 3 := hu.tail ⟨2, rfl, rfl⟩
  have hk : graph.DReach 0 4 := hh.tail ⟨6, rfl, rfl⟩
  have hj : graph.DReach 0 5 := hv.tail ⟨5, rfl, rfl⟩
  have hw : graph.DReach 0 8 := hu.tail ⟨3, rfl, rfl⟩
  fin_cases a
  · exact .refl
  · exact hu
  · exact hv
  · exact hh
  · exact hk
  · exact hj
  · exact hk.tail ⟨8, rfl, rfl⟩
  · exact hj.tail ⟨9, rfl, rfl⟩
  · exact hw
  · exact hw.tail ⟨10, rfl, rfl⟩
  · exact hw.tail ⟨11, rfl, rfl⟩

theorem C_path_avoids {a : Fin 11} (h0 : (0 : Fin 11) ≠ a)
    (h1 : (1 : Fin 11) ≠ a) (h8 : (8 : Fin 11) ≠ a) (h9 : (9 : Fin 11) ≠ a) :
    graph.AvoidReach a 0 9 := by
  refine ⟨h0, h9, ?_⟩
  exact ((Relation.ReflTransGen.refl (a := (0 : Fin 11))).tail
    ⟨⟨0, rfl, rfl⟩, h0, h1⟩).tail
      ⟨⟨3, rfl, rfl⟩, h1, h8⟩ |>.tail ⟨⟨10, rfl, rfl⟩, h8, h9⟩

theorem B_path_avoids {a : Fin 11} (h0 : (0 : Fin 11) ≠ a)
    (h2 : (2 : Fin 11) ≠ a) (h5 : (5 : Fin 11) ≠ a) (h7 : (7 : Fin 11) ≠ a) :
    graph.AvoidReach a 0 7 := by
  refine ⟨h0, h7, ?_⟩
  exact ((Relation.ReflTransGen.refl (a := (0 : Fin 11))).tail
    ⟨⟨1, rfl, rfl⟩, h0, h2⟩).tail
      ⟨⟨5, rfl, rfl⟩, h2, h5⟩ |>.tail ⟨⟨9, rfl, rfl⟩, h5, h7⟩

theorem graph_least_stable (a : Fin 11)
    (ha : ∀ x : Fin 4, graph.Dominates 0 a (leaf x)) : a = 0 := by
  fin_cases a
  · rfl
  all_goals first
    | exact False.elim (ha 1 (B_path_avoids (by decide) (by decide) (by decide) (by decide)))
    | exact False.elim (ha 2 (C_path_avoids (by decide) (by decide) (by decide) (by decide)))

def source : RootedBinary (Fin 11) (Fin 12) (Fin 4) where
  graph := graph
  root := 0
  leaf := leaf
  at_least_two_taxa := by decide
  root_degrees := by decide +kernel
  leaf_degrees := by intro x; fin_cases x <;> decide +kernel
  internal_degrees := by
    intro a hr hl
    fin_cases a
    · exact False.elim (hr rfl)
    · exact Or.inl (by decide +kernel)
    · exact Or.inl (by decide +kernel)
    · exact Or.inr (by change graph.inDegree 3 = 2 ∧ graph.outDegree 3 = 1; decide +kernel)
    · exact Or.inl (by decide +kernel)
    · exact Or.inr (by change graph.inDegree 5 = 2 ∧ graph.outDegree 5 = 1; decide +kernel)
    · exact False.elim (hl 0 rfl)
    · exact False.elim (hl 1 rfl)
    · exact Or.inl (by decide +kernel)
    · exact False.elim (hl 2 rfl)
    · exact False.elim (hl 3 rfl)
  acyclic := graph_acyclic
  rooted := graph_rooted
  least_stable := graph_least_stable

def calendar : GProgram.G5.Calendar graph where
  age v := match v.val with
    | 0 => 9 | 1 => 8 | 2 => 8 | 3 => 7 | 4 => 6 | 5 => 5 | 8 => 4 | _ => 0
  edge_older := by intro e; fin_cases e <;> norm_num [graph]

theorem tips_contemporary (x : Fin 4) : calendar.age (leaf x) = 0 := by
  fin_cases x <;> rfl

/-- The first hybrid has one original child edge, but a genuine alternate
undirected path makes that child edge non-cut. -/
theorem child_detour : graph.ReachWithout 6 3 4 := by
  exact ((Relation.ReflTransGen.refl (a := (3 : Fin 11))).tail
    ⟨4, by decide, Or.inr ⟨rfl, rfl⟩⟩).tail
      ⟨5, by decide, Or.inl ⟨rfl, rfl⟩⟩ |>.tail
        ⟨7, by decide, Or.inr ⟨rfl, rfl⟩⟩

theorem child_not_bridge : ¬ graph.IsBridge 6 :=
  graph.not_bridge_of_detour child_detour

theorem child_component_contains_C : graph.ReachWithout 6 4 9 := by
  exact ((graph.ureach_symm child_detour).tail
    ⟨2, by decide, Or.inr ⟨rfl, rfl⟩⟩).tail
      ⟨3, by decide, Or.inl ⟨rfl, rfl⟩⟩ |>.tail
        ⟨10, by decide, Or.inl ⟨rfl, rfl⟩⟩

theorem C_not_child_descendant : ¬ graph.DReach 4 9 := by
  let P : Fin 11 → Prop := fun v => v.val = 4 ∨ v.val = 5 ∨ v.val = 6 ∨ v.val = 7
  have hclosed : ∀ a b, graph.DStep a b → P a → P b := by
    intro a b hstep ha
    obtain ⟨e, hs, ht⟩ := hstep
    rw [← hs] at ha
    rw [← ht]
    fin_cases e <;> norm_num [graph, P] at *
  intro hd
  have h := graph.dreach_preserves hclosed hd (by norm_num [P])
  norm_num [P] at h

theorem actual_weaker_source_counterexample :
    source.graph.IsHybrid 3 ∧ source.graph.source 6 = 3 ∧
    source.graph.ReachWithout 6 (source.graph.target 6) (source.leaf 2) ∧
    ¬ source.graph.DReach (source.graph.target 6) (source.leaf 2) :=
  ⟨by change graph.inDegree 3 = 2 ∧ graph.outDegree 3 = 1; decide +kernel,
    rfl, child_component_contains_C, C_not_child_descendant⟩

/-- Stronger route-level stress test: B is a directed descendant of the first
hybrid, but its legal original route bypasses that hybrid's child population
during the purported protective interval. Every source edge duration is positive. -/
theorem actual_protective_route_failure :
    graph.DReach 3 (leaf 1) ∧
    calendar.age (graph.target 6) ≤ (13 / 2 : ℝ) ∧
    (13 / 2 : ℝ) < calendar.age 3 ∧
    EdgePath graph 0 (leaf 1) [1, 5, 9] ∧
    (6 : Fin 12) ∉ [1, 5, 9] ∧
    calendar.Active (13 / 2) 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((Relation.ReflTransGen.single ⟨6, rfl, rfl⟩).tail
      ⟨7, rfl, rfl⟩).tail ⟨9, rfl, rfl⟩
  · norm_num [calendar, graph]
  · norm_num [calendar]
  · exact .cons rfl (.cons rfl (.cons rfl (.nil 7)))
  · decide +kernel
  · norm_num [Calendar.Active, calendar, graph]

#print axioms source
#print axioms tips_contemporary
#print axioms actual_weaker_source_counterexample
#print axioms actual_protective_route_failure

end GProgram.G5.CutChildTest
