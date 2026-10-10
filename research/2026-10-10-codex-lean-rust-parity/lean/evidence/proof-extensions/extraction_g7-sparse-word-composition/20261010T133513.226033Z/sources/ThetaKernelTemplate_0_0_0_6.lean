import ThetaFiniteSoundness

/- Kernel-only decomposition of the original finite certificate obligation.
Each coefficient/gap is proved separately to bound reduction memory.
The executable evaluator and all theorem assumptions are unchanged. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Nanuq.Theta.KernelCertificates
theorem kernel_checked_0_0_0_6 : checkTemplate ⟨0,0,0,6⟩ = true := by
  unfold checkTemplate
  rw [Bool.and_eq_true]
  constructor
  · decide +kernel
  · change ([(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)] : List (Nat × Nat)).all (fun pq =>
      ([(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)] : List (Nat × Nat)).all (fun ij =>
        decide (0 ≤ alpha ⟨0,0,0,6⟩ pq.1 pq.2 ij.1 ij.2))) = true
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true]
    repeat' apply And.intro
    all_goals first | exact True.intro | decide +kernel
#print axioms kernel_checked_0_0_0_6
end Nanuq.Theta.KernelCertificates
