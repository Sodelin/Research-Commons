import Lean
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace PoolingFixture

def formula : List (List (Nat x Bool)) :=
  [[(0,true),(2,true)],[(0,true),(3,true)],[(1,true),(4,true)],[(1,true),(4,true)],
   [(5,true)],[(5,false),(2,true)],[(5,false),(4,false)],[(2,false)]]

def feasible (mask pin : Nat) : Bool :=
  (List.range 16).any fun v =>
    ((List.range 8).zip formula).all fun (i, clause) =>
      !mask.testBit i || clause.any (fun (j,s) => (pin + 4*v).testBit j == s)

def count (sw : Bool) (pin : Nat) : Nat :=
  ((List.range 256).filter fun m => m.testBit 4 == sw && feasible m pin).length

theorem counts : [count false 0, count false 2, count false 1, count false 3,
                  count true 0, count true 2, count true 1, count true 3] =
                 [96,96,128,128,50,80,60,96] := by decide +kernel

theorem gap :
   (let u := count false; let v := count true;
    u 0 * u 3 = u 2 * u 1 ? v 0 * v 3 = v 2 * v 1 ?
    517 * ((u 0 + v 0) * (u 3 + v 3)) = 511 * ((u 2 + v 2) * (u 1 + v 1)) ?
    (u 0 + v 0) * (u 3 + v 3) < (u 2 + v 2) * (u 1 + v 1)) := by decide +kernel
end PoolingFixture
#print axioms PoolingFixture.counts
#print axioms PoolingFixture.gap

