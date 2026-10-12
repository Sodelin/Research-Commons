import G3CriticalProjectionPolynomials
import G3CriticalSourceSliceCoprime

/-! UNCOMPILED consumer draft. This closes the semantic theorem's explicit
slice premise only by importing the actual source-certificate theorem.
Neither this file nor its source-certificate dependencies have been compiled
as a combined target at handoff. No successful verification is claimed. -/
noncomputable section
namespace GProgram.G3.CriticalCertificates

/-- Actual all-real fixed-residue strict critical-set endpoint. This is a
draft theorem awaiting the complete source certificate and kernel build. -/
theorem actual_fixed_residue_strict_critical_finite {r : ℝ} (hr : 0 < r) :
    (strictSourceCriticalSet r).Finite := by
  apply strictSourceCriticalSet_finite_of_slice_coprime hr
  simpa only [sourceSliceCoprime, sourceQAt] using actual_slice_coprime hr

#print axioms actual_fixed_residue_strict_critical_finite
end GProgram.G3.CriticalCertificates
