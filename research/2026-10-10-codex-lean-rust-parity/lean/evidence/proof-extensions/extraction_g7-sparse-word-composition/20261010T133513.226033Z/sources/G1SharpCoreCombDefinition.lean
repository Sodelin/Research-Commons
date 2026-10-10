import G1CutChildPorts
import G1BinaryCoreBudgets
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The EXACT accepted all-n saturating family, instantiated on a binary
taxon comb. Every branching node is the original E/U/V/HL/HR module, with six
internal arcs and the two original hybrid-child ports. Contributor: dot. -/
namespace G1SharpCoreCombDefinition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open scoped Classical

abbrev Module (n : Nat) := Fin (n-1)
abbrev LocalVertex := Fin 5
abbrev LocalEdge := Fin 8
abbrev Vertex (n : Nat) := (Module n × LocalVertex) ⊕ Fin n
abbrev Edge (n : Nat) := Module n × LocalEdge

/-- Local vertex IDs E=0,U=1,V=2,HL=3,HR=4. Original arcs are ordered as in
the accepted review, with child-port IDs6/7. -/
def localSource : LocalEdge → LocalVertex := ![0,0,1,1,2,2,3,4]

def source (n : Nat) (e : Edge n) : Vertex n := .inl (e.1,localSource e.2)

def target (n : Nat) (e : Edge n) : Vertex n :=
  match e.2.val with
  | 0 => .inl (e.1,3)
  | 1 => .inl (e.1,1)
  | 2 => .inl (e.1,4)
  | 3 => .inl (e.1,2)
  | 4 => .inl (e.1,3)
  | 5 => .inl (e.1,4)
  | 6 => .inr ⟨e.1.val,by have h := e.1.isLt; omega⟩
  | _ => if h : e.1.val+1 < n-1 then .inl (⟨e.1.val+1,h⟩,0)
    else .inr ⟨n-1,by have h := e.1.isLt; omega⟩

def graph (n : Nat) : EdgeGraph (Vertex n) (Edge n) := ⟨source n,target n⟩

def taxon (n : Nat) : Fin n ↪ Vertex n := ⟨Sum.inr,Sum.inr_injective⟩

def root (n : Nat) (hn : 4 ≤ n) : Vertex n := .inl (⟨0,by omega⟩,0)

def rank (n : Nat) : Vertex n → Nat
  | .inl (i,k) => 8*i.val+k.val
  | .inr _ => 8*n

def age (n : Nat) (v : Vertex n) : ℝ := 8*n - (rank n v : ℝ)

theorem exact_vertex_count (n : Nat) (hn : 4 ≤ n) : Fintype.card (Vertex n) = 6*n-5 := by
  simp only [Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  omega

theorem exact_edge_count (n : Nat) (hn : 4 ≤ n) : Fintype.card (Edge n) = 8*n-8 := by
  simp only [Edge,Fintype.card_prod,Fintype.card_fin]
  omega

theorem original_edge_rank_increases (n : Nat) (e : Edge n) :
    rank n ((graph n).source e) < rank n ((graph n).target e) := by
  rcases e with ⟨i,k⟩
  fin_cases k
  all_goals simp [graph,source,target,localSource,rank]
  all_goals have hi := i.isLt
  all_goals first | omega | (split_ifs <;> simp [rank] <;> omega)

def calendar (n : Nat) : Calendar (graph n) where
  age := age n
  edge_older e := by
    have h : (rank n ((graph n).source e) : ℝ) < rank n ((graph n).target e) :=
      by exact_mod_cast original_edge_rank_increases n e
    dsimp [age]
    linarith

theorem graph_acyclic (n : Nat) : (graph n).Acyclic := by
  have hstrict : ∀ a b, Relation.TransGen (graph n).DStep a b → rank n a < rank n b := by
    intro a b h
    induction h with
    | single step => obtain ⟨e,rfl,rfl⟩ := step; exact original_edge_rank_increases n e
    | tail _ step ih => obtain ⟨e,rfl,rfl⟩ := step; exact ih.trans (original_edge_rank_increases n e)
  intro a h
  exact (lt_irrefl _) (hstrict a a h)

theorem original_tips_contemporaneous (n : Nat) (x : Fin n) : (calendar n).age (taxon n x) = 0 := by
  simp [calendar,age,taxon,rank]

#print axioms original_edge_rank_increases
#print axioms exact_vertex_count
end G1SharpCoreCombDefinition
