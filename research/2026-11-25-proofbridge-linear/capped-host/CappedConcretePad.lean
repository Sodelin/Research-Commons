import CappedPresentedPadding
import CappedLabeledGrid

namespace ResearchCommons.CappedConcretePad
open ResearchCommons.CappedPresentedPadding ResearchCommons.CappedLabeledGrid

def cells (n : Nat) : List (Cell n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).map fun b => (a,b)

theorem allCells {n : Nat} (c : Cell n) : c ∈ cells n :=
  List.mem_flatMap.mpr ⟨c.1,List.mem_finRange _,List.mem_map.mpr ⟨c.2,List.mem_finRange _,rfl⟩⟩

def vertices (n k : Nat) : List (Vertex n k) :=
  ((cells n).flatMap fun c => (List.finRange k).map fun l => Sum.inl (c,l)) ++
     (cells n).map Sum.inr

theorem allVertices {n k : Nat} (w : Vertex n k) : w ∈ vertices n k := by
  cases w with
  | inl w =>
    exact List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr
      ⟨w.1,allCells _,List.mem_map.mpr ⟨w.2,List.mem_finRange _,by cases w; rfl⟩⟩))
  | inr w => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨w,allCells _,rfl⟩))

def labeledPad {Time : Type} [LT Time] (stamp : Nat → Time)
    (increasing : ∀ a b, a < b → stamp a < stamp b)
    (n k : Nat) (hk : 2 ≤ k) : FinitePad (Vertex n k) Time k k where
  birth := fun w => stamp (rank w)
  edge := @ResearchCommons.CappedLabeledGrid.edge n k
  cover := vertices n k
  cover_all := allVertices
  ordered := by
    intro x y h
    cases e : ResearchCommons.CappedLabeledGrid.edge x y with
    | none => simp [e] at h
    | some l => exact increasing _ _ (rank_rises x y l e)
  label_valid := edges_use_labels hk
  parent_of_label := by
    intro v h l hl
    cases v with
    | inl r =>
      exact False.elim (h (fun x => no_edge_into_private_root x r))
    | inr c => exact every_cell_label c ⟨l,hl⟩
  children := by
    intro x
    obtain ⟨xs,hx,cover⟩ := children_covered x
    refine ⟨xs,Nat.le_trans hx hk,?_⟩
    intro y h
    cases e : ResearchCommons.CappedLabeledGrid.edge x y with
    | none => simp [e] at h
    | some l => exact cover y l e

#print axioms labeledPad
end ResearchCommons.CappedConcretePad
