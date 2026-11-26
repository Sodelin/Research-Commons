import G6NaturalCellOrderedCompiler
import GParity.Chart
import Mathlib.Tactic.FinCases

namespace UnifiedLean.G6.TwoTipChartFixture
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
def graph : EdgeGraph (Fin 3) (Fin 2) :=
  ⟨fun _ => 0, fun e => e.succ⟩

def leaf : Fin 2 ↪ Fin 3 :=
  ⟨Fin.succ, by intro a b h; exact Fin.ext (by simpa using congrArg Fin.val h)⟩

theorem step_rank {a b : Fin 3} (h : graph.DStep a b) : a.val < b.val := by
  obtain ⟨e, rfl, rfl⟩ := h
  simp [graph]

theorem path_rank {a b : Fin 3} (h : Relation.TransGen graph.DStep a b) :
    a.val < b.val := by
  induction h with
  | single h => exact step_rank h
  | tail _ h ih => exact lt_trans ih (step_rank h)

theorem graph_acyclic : graph.Acyclic := by
  intro a ha
  exact (lt_irrefl _) (path_rank ha)

theorem graph_rooted : ∀ a, graph.DReach 0 a := by
  intro a
  fin_cases a
  · exact .refl
  · exact .single ⟨0, rfl, rfl⟩
  · exact .single ⟨1, rfl, rfl⟩

theorem graph_least_stable :
    ∀ a, (∀ x, graph.Dominates 0 a (leaf x)) → a = 0 := by
  intro a h
  fin_cases a
  · rfl
  · exact False.elim (h 1 ⟨by decide, by decide,
      .single ⟨⟨1, rfl, rfl⟩, by decide, by decide⟩⟩)
  · exact False.elim (h 0 ⟨by decide, by decide,
      .single ⟨⟨0, rfl, rfl⟩, by decide, by decide⟩⟩)

def source : RootedBinary (Fin 3) (Fin 2) (Fin 2) where
  graph := graph
  root := 0
  leaf := leaf
  at_least_two_taxa := by decide
  root_degrees := by decide
  leaf_degrees := by decide
  internal_degrees := by
    intro a hroot hleaf
    fin_cases a
    · exact False.elim (hroot rfl)
    · exact False.elim (hleaf 0 rfl)
    · exact False.elim (hleaf 1 rfl)
  acyclic := graph_acyclic
  rooted := graph_rooted
  least_stable := graph_least_stable

theorem noHybrid (h : Hybrid source) : False := by
  have hn : ∀ v : Fin 3, ¬ graph.IsHybrid v := by
    intro v
    unfold EdgeGraph.IsHybrid
    fin_cases v <;> decide
  exact hn h.val h.property


def nativeSource : GParity.Chart.Source :=
  ⟨3, 0, [⟨0, 1⟩, ⟨0, 2⟩], [1, 2], []⟩

def nativeInput : GParity.Chart.Input :=
  ⟨nativeSource, [], [], [], 4096⟩

theorem nativeSource_valid : nativeSource.valid = true := by decide


end UnifiedLean.G6.TwoTipChartFixture
