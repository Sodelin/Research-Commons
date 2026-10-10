import G1SharpCoreCombDefinition

/-! Exact ORIGINAL incoming/outgoing edge-ID sets for the accepted all-n
module family. Binary degree and hybrid census are derived from these sets. -/
namespace G1SharpCoreCombDegrees
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition
open scoped Classical

def moduleOutgoing (n : Nat) (i : Module n) (k : LocalVertex) : Finset (Edge n) :=
  match k.val with
  | 0 => {(i,0),(i,1)}
  | 1 => {(i,2),(i,3)}
  | 2 => {(i,4),(i,5)}
  | 3 => {(i,6)}
  | _ => {(i,7)}

def previousModule (n : Nat) (i : Module n) (h : i.val ≠ 0) : Module n :=
  ⟨i.val-1,by have hi := i.isLt; omega⟩

def moduleIncoming (n : Nat) (i : Module n) (k : LocalVertex) : Finset (Edge n) :=
  match k.val with
  | 0 => if h : i.val = 0 then ∅ else {(previousModule n i h,7)}
  | 1 => {(i,1)}
  | 2 => {(i,3)}
  | 3 => {(i,0),(i,4)}
  | _ => {(i,2),(i,5)}

def leafIncoming (n : Nat) (hn : 4 ≤ n) (x : Fin n) : Finset (Edge n) :=
  if h : x.val < n-1 then {(⟨x.val,h⟩,6)} else {(⟨n-2,by omega⟩,7)}

theorem exact_module_outgoing (n : Nat) (i : Module n) (k : LocalVertex) :
    Finset.univ.filter (fun e : Edge n => (graph n).source e = .inl (i,k)) = moduleOutgoing n i k := by
  ext e
  rcases e with ⟨j,l⟩
  fin_cases k <;> fin_cases l
  all_goals dsimp only [graph,source,localSource,moduleOutgoing]
  all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton,
    Sum.inl.injEq,Prod.mk.injEq]
  all_goals norm_num [Fin.ext_iff]

theorem exact_leaf_outgoing (n : Nat) (x : Fin n) :
    Finset.univ.filter (fun e : Edge n => (graph n).source e = .inr x) = ∅ := by
  ext e
  simp [graph,source]

theorem exact_module_incoming (n : Nat) (i : Module n) (k : LocalVertex) :
    Finset.univ.filter (fun e : Edge n => (graph n).target e = .inl (i,k)) = moduleIncoming n i k := by
  ext e
  rcases e with ⟨j,l⟩
  have hi := i.isLt
  have hj := j.isLt
  fin_cases k <;> fin_cases l
  all_goals dsimp only [graph,target,moduleIncoming,previousModule]
  all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,Sum.inl.injEq,Sum.inr_ne_inl,Prod.mk.injEq]
  all_goals norm_num [Fin.ext_iff]
  all_goals split_ifs
  all_goals try simp_all only [Finset.notMem_empty,Finset.mem_singleton,Sum.inl.injEq,
    Sum.inr_ne_inl,Prod.mk.injEq,Fin.ext_iff,Fin.val_mk]
  all_goals norm_num at *
  all_goals omega

theorem exact_leaf_incoming (n : Nat) (hn : 4 ≤ n) (x : Fin n) :
    Finset.univ.filter (fun e : Edge n => (graph n).target e = .inr x) = leafIncoming n hn x := by
  ext e
  rcases e with ⟨j,l⟩
  have hx := x.isLt
  have hj := j.isLt
  fin_cases l
  all_goals dsimp only [graph,target,leafIncoming]
  all_goals simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
    Sum.inl_ne_inr,Sum.inr.injEq,Prod.mk.injEq]
  all_goals split_ifs <;> simp_all only [Finset.mem_singleton,Sum.inl_ne_inr,Sum.inr.injEq,
    Prod.mk.injEq,Fin.ext_iff,Fin.val_mk] <;> norm_num at * <;> omega

theorem module_outdegree (n : Nat) (i : Module n) (k : LocalVertex) :
    (graph n).outDegree (.inl (i,k)) = if k.val < 3 then 2 else 1 := by
  rw [EdgeGraph.outDegree,exact_module_outgoing]
  fin_cases k <;> simp [moduleOutgoing]

theorem module_indegree (n : Nat) (i : Module n) (k : LocalVertex) :
    (graph n).inDegree (.inl (i,k)) =
      if k.val = 0 then (if i.val = 0 then 0 else 1) else if k.val < 3 then 1 else 2 := by
  rw [EdgeGraph.inDegree,exact_module_incoming]
  fin_cases k <;> simp [moduleIncoming]
  split_ifs <;> simp

theorem leaf_degrees (n : Nat) (hn : 4 ≤ n) (x : Fin n) :
    (graph n).inDegree (taxon n x) = 1 ∧ (graph n).outDegree (taxon n x) = 0 := by
  constructor
  · rw [EdgeGraph.inDegree]
    change (Finset.univ.filter (fun e : Edge n => (graph n).target e = .inr x)).card = 1
    rw [exact_leaf_incoming n hn x]
    simp [leafIncoming]
    split_ifs <;> simp
  · change (Finset.univ.filter (fun e : Edge n => (graph n).source e = .inr x)).card = 0
    rw [exact_leaf_outgoing]
    rfl

#print axioms module_indegree
#print axioms leaf_degrees
end G1SharpCoreCombDegrees
