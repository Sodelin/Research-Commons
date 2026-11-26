import Lean
set_option warningAsError true
set_option maxHeartbeats 1000000
namespace PB_e1a4b96c621e46681e09c2fc7403bf93cb6d4ee298fb7fc5bd00afa8a403342b
theorem addScaled (k : Nat) {v s : Int} (hv : 0 <= v) (hs : 0 <= s) :
    0 <= (k : Int) * v + s := Int.add_nonneg (Int.mul_nonneg (by omega) hv) hs
theorem certificate (x0 x1 x2 : Int) (h0 : (-1 : Int) * x0 + (0 : Int) * x1 + (0 : Int) * x2 <= (-330 : Int)) (h1 : (0 : Int) * x0 + (1 : Int) * x1 + (0 : Int) * x2 <= (98 : Int)) (h2 : (0 : Int) * x0 + (0 : Int) * x1 + (1 : Int) * x2 <= (45 : Int)) : (-1 : Int) * x0 + (1 : Int) * x1 + (1 : Int) * x2 <= (-187 : Int) := by
  have s0 : 0 <= (-330 : Int) - ((-1 : Int) * x0 + (0 : Int) * x1 + (0 : Int) * x2) := by omega
  have s1 : 0 <= (98 : Int) - ((0 : Int) * x0 + (1 : Int) * x1 + (0 : Int) * x2) := by omega
  have s2 : 0 <= (45 : Int) - ((0 : Int) * x0 + (0 : Int) * x1 + (1 : Int) * x2) := by omega
  have combined : 0 <= (((1 : Int) * ((-330 : Int) - ((-1 : Int) * x0 + (0 : Int) * x1 + (0 : Int) * x2))) + (((1 : Int) * ((98 : Int) - ((0 : Int) * x0 + (1 : Int) * x1 + (0 : Int) * x2))) + (((1 : Int) * ((45 : Int) - ((0 : Int) * x0 + (0 : Int) * x1 + (1 : Int) * x2))) + 0))) := addScaled 1 s0 (addScaled 1 s1 (addScaled 1 s2 (Int.le_refl 0)))
  clear h0 s0 h1 s1 h2 s2
  omega
#print axioms certificate
end PB_e1a4b96c621e46681e09c2fc7403bf93cb6d4ee298fb7fc5bd00afa8a403342b
