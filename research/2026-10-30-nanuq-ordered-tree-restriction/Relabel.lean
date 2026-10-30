import AdjacentBlocks
set_option debug.skipKernelTC false
namespace Nanuq.Restriction

def LTree.map (f : Nat → Nat) : LTree → LTree
  | .empty => .empty
  | .tip x => .tip (f x)
  | .fork l r => .fork (l.map f) (r.map f)

theorem leaves_map (f : Nat → Nat) (t : LTree) :
    (t.map f).leaves = t.leaves.map f := by
  induction t <;> simp_all [LTree.map,LTree.leaves,List.map_append]

theorem full_map (f : Nat → Nat) (t : LTree) (h : t.Full) : (t.map f).Full := by
  induction t <;> simp_all [LTree.Full,LTree.map]

theorem mem_map_rank (palette xs : List Nat) (a : Nat) (ha : a∈palette) :
    palette.idxOf a ∈ xs.map palette.idxOf ↔ a∈xs := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x,hx,he⟩
    have hax := (List.idxOf_inj ha).mp he.symm
    simpa only [hax] using hx
  · intro hx; exact ⟨a,hx,rfl⟩

theorem cut_map_rank (palette left right : List Nat) (a b c d : Nat)
    (ha : a∈palette) (hb : b∈palette) (hc : c∈palette) (hd : d∈palette) :
    Cut (left.map palette.idxOf) (right.map palette.idxOf)
      (palette.idxOf a) (palette.idxOf b) (palette.idxOf c) (palette.idxOf d) ↔
    Cut left right a b c d := by
  simp only [Cut,mem_map_rank palette left a ha,mem_map_rank palette left b hb,
    mem_map_rank palette left c hc,mem_map_rank palette left d hd,
    mem_map_rank palette right a ha,mem_map_rank palette right b hb,
    mem_map_rank palette right c hc,mem_map_rank palette right d hd]

theorem witness_map_rank (palette : List Nat) (t : LTree) (outside : List Nat) (a b c d : Nat)
    (ha : a∈palette) (hb : b∈palette) (hc : c∈palette) (hd : d∈palette) :
    (t.map palette.idxOf).Witness (outside.map palette.idxOf)
      (palette.idxOf a) (palette.idxOf b) (palette.idxOf c) (palette.idxOf d) ↔
    t.Witness outside a b c d := by
  induction t generalizing outside with
  | empty => rfl
  | tip x =>
    simpa only [LTree.map,LTree.Witness,List.map_cons,List.map_nil] using
      cut_map_rank palette [x] outside a b c d ha hb hc hd
  | fork l r hl hr =>
    simp only [LTree.map,LTree.Witness,leaves_map,← List.map_append]
    rw [cut_map_rank palette (l.leaves++r.leaves) outside a b c d ha hb hc hd,
      hl (r.leaves++outside),hr (l.leaves++outside)]

theorem blocks_length_le (labels : List Nat) (dup : Nat → Bool) :
    labels.length ≤ (blocks labels dup).length := by
  induction labels with
  | nil => simp [blocks]
  | cons x xs ih =>
    cases hx : dup x <;> simp [blocks,hx] at ih ⊢ <;> omega

#print axioms witness_map_rank
end Nanuq.Restriction
