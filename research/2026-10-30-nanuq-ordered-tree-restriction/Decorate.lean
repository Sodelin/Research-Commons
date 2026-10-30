import SixLabels
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

def decorate : Tree → (Nat → Nat) → Nat → LTree
  | .tip,f,lo => .tip (f lo)
  | .fork l r,f,lo => .fork (decorate l f lo) (decorate r f (lo+l.size))

theorem decorate_full (T : Tree) (f : Nat → Nat) (lo : Nat) : (decorate T f lo).Full := by
  induction T generalizing lo <;> simp_all [decorate,LTree.Full]

theorem erase_decorate (T : Tree) (f : Nat → Nat) (lo : Nat) : (decorate T f lo).erase = T := by
  induction T generalizing lo <;> simp_all [decorate,LTree.erase]

theorem decorate_leaves (T : Tree) (f : Nat → Nat) (lo : Nat) :
    (decorate T f lo).leaves = (List.range' lo T.size).map f := by
  induction T generalizing lo with
  | tip => simp [decorate,LTree.leaves,Tree.size,List.range']
  | fork l r hl hr =>
    simp only [decorate,LTree.leaves,Tree.size,hl,hr,← List.map_append,List.range'_append_1]

theorem range_getD_slice (xs : List Nat) (lo len : Nat) (h : lo+len≤xs.length) :
    (List.range' lo len).map (fun i => xs.getD i 0) = (xs.drop lo).take len := by
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range',List.length_take,List.length_drop]
    omega
  · intro i hi hj
    have hil : i<len := by simpa using hi
    have hib : lo+i<xs.length := by omega
    simp only [List.getElem_map,List.getElem_range',Nat.one_mul,
      List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hib,Option.getD_some,
      List.getElem_take,List.getElem_drop]

def wholeDecorate (T : Tree) (tips : List Nat) : LTree :=
  .fork (.tip (tips.getD 0 0)) (decorate T (fun i => tips.getD i 0) 1)

theorem wholeDecorate_leaves (T : Tree) (tips : List Nat) (hn : 1≤tips.length)
    (hs : T.size=tips.length-1) : (wholeDecorate T tips).leaves = tips := by
  have hb : 1+T.size≤tips.length := by omega
  simp only [wholeDecorate,LTree.leaves,decorate_leaves]
  rw [range_getD_slice tips 1 T.size hb,hs]
  cases tips with
  | nil => simp at hn
  | cons x xs => simp

 theorem wholeDecorate_edgeWitness (T : Tree) (tips : List Nat) (hn : 1≤tips.length)
    (hs : T.size=tips.length-1) (q : Quartet) (r a b c d : Nat)
    (hparts : q.parts r=(a,b,c,d)) (hab : a≠b) (hcd : c≠d) :
    (wholeDecorate T tips).Witness [] a b c d ↔
      ∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 q r=true := by
  have hleaves := wholeDecorate_leaves T tips hn hs
  have he := whole_first_edgeWitness (tips.getD 0 0) (decorate T (fun i=>tips.getD i 0) 1)
    (decorate_full _ _ _) q r a b c d hparts hab hcd
  simp only [wholeDecorate,LTree.leaves,List.singleton_append] at hleaves
  simpa only [wholeDecorate,erase_decorate,hleaves] using he

#print axioms wholeDecorate_edgeWitness
end Nanuq.Restriction
