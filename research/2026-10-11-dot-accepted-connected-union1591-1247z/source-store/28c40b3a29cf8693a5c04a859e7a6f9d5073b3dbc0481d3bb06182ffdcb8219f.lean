import ThetaSupport

/- Kernel-only decomposition of the original finite certificate obligation.
Each coefficient/gap is proved separately to bound reduction memory.
The executable evaluator and all theorem assumptions are unchanged. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Nanuq.Theta.KernelCertificates
theorem kernel_support_checked_0_0_0_5 : checkSupport ⟨0,0,0,5⟩ = true := by
  change ([(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(1,3),(1,4),(1,5),(1,6),(2,3),(2,4),(2,5),(2,6),(3,4),(3,5),(3,6),(4,5),(4,6),(5,6)] : List (Nat × Nat)).all (fun ij =>
    positiveAnchorAt ⟨0,0,0,5⟩ ij.1 ij.2 == displayedSplit ⟨0,0,0,5⟩ ij.1 ij.2) = true
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel
#print axioms kernel_support_checked_0_0_0_5
end Nanuq.Theta.KernelCertificates
