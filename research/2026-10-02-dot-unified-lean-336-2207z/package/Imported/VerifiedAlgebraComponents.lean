import G4BalancedForestIdentity
import G4FourRootPositivity
import G3FiniteMomentBarrier
import G3CapSixDeterminant

/-! Incremental finite algebra checkpoint. These four components do not assert
complete biological G3/G4 recognition or source-observation transfer. -/
#check GProgram.G4.balanced_residual_identity
#check GProgram.G4.balanced_coordinate_separates_cap4
#check GProgram.G4.FourRoot.exact_defect_factorization
#check GProgram.G4.FourRoot.zero_delta_forces_negative_defect3
#check GProgram.G4.FourRoot.no_common_moment_signature
#check GProgram.G4.FourRoot.rational_cap3_scalar_witness
#check GProgram.G3.MomentBarrier.exact_double_sum
#check GProgram.G3.MomentBarrier.finite_moment_inequality
#check GProgram.G3.MomentBarrier.coupled_barrier_minimal
#check GProgram.G3.MomentBarrier.coupled_barrier
#print axioms GProgram.G4.balanced_coordinate_separates_cap4
#print axioms GProgram.G4.FourRoot.zero_delta_forces_negative_defect3
#print axioms GProgram.G3.MomentBarrier.coupled_barrier_minimal

#check GProgram.G3.CapSix.LU_eq_J0
#check GProgram.G3.CapSix.exact_determinant
#check GProgram.G3.CapSix.J0_nonsingular
#check GProgram.G3.CapSix.scaled_determinant
#check GProgram.G3.CapSix.scaled_J_nonsingular
#print axioms GProgram.G3.CapSix.scaled_J_nonsingular
