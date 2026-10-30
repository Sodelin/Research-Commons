import QueryTransport
set_option debug.skipKernelTC false
namespace Nanuq.Restriction
open Nanuq.AdjacentCertificate

theorem twiceMean_transport (n : Nat) (keep : Nat → Bool) (T U : Tree) (tips tips' : List Nat)
    (ht : EdgeTransport n keep T U tips tips') (x y p z : Nat)
    (hx : x∈retained n keep) (hy : y∈retained n keep) (hp : p∈retained n keep) (hz : z∈retained n keep)
    (hxy : x≠y) (hxp : x≠p) (hxz : x≠z) (hyp : y≠p) (hyz : y≠z) (hpz : p≠z) :
    twiceMean (quartets n) (codedPattern T tips n) x y p z =
      twiceMean (quartets (retained n keep).length) (codedPattern U tips' (retained n keep).length)
        ((retained n keep).idxOf x) ((retained n keep).idxOf y)
        ((retained n keep).idxOf p) ((retained n keep).idxOf z) := by
  have hq := query_transport n keep T U tips tips' ht x y p z hx hy hp hz hxy hxp hxz hyp hyz hpz
  simp only [twiceMean,hq.1,hq.2]
  simp only [relabel_side_rank,hx,hy]

/-- Exact preservation of the FROZEN anchor definition, including diagonal
and shared-anchor cases, not a newly defined auxiliary weighted metric. -/
theorem anchor_transport (n : Nat) (keep : Nat → Bool) (T U : Tree) (tips tips' : List Nat)
    (ht : EdgeTransport n keep T U tips tips') (p q x y : Nat)
    (hp : p∈retained n keep) (hq : q∈retained n keep) (hx : x∈retained n keep) (hy : y∈retained n keep)
    (hpq : p≠q) :
    anchor (quartets n) (codedPattern T tips n) p q x y =
      anchor (quartets (retained n keep).length) (codedPattern U tips' (retained n keep).length)
        ((retained n keep).idxOf p) ((retained n keep).idxOf q)
        ((retained n keep).idxOf x) ((retained n keep).idxOf y) := by
  have hxy := List.idxOf_inj hx (y:=y)
  have hxp := List.idxOf_inj hx (y:=p)
  have hxq := List.idxOf_inj hx (y:=q)
  have hyp := List.idxOf_inj hy (y:=p)
  have hyq := List.idxOf_inj hy (y:=q)
  by_cases h0 : x=y ∨ (x=p ∧ y=q) ∨ (x=q ∧ y=p)
  · simp only [anchor,hxy,hxp,hxq,hyp,hyq,h0,if_true]
  · by_cases h1 : x=p ∨ x=q ∨ y=p ∨ y=q
    · simp only [anchor,hxy,hxp,hxq,hyp,hyq,h0,h1,if_false,if_true]
    · simp only [anchor,hxy,hxp,hxq,hyp,hyq,h0,h1,if_false]
      apply congrArg Int.ofNat
      apply twiceMean_transport n keep T U tips tips' ht x y p q hx hy hp hq
      · intro h; exact h0 (Or.inl h)
      · intro h; exact h1 (Or.inl h)
      · intro h; exact h1 (Or.inr (Or.inl h))
      · intro h; exact h1 (Or.inr (Or.inr (Or.inl h)))
      · intro h; exact h1 (Or.inr (Or.inr (Or.inr h)))
      · exact hpq

#print axioms twiceMean_transport
#print axioms anchor_transport
end Nanuq.Restriction
