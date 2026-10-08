# Mandatory affine/linear clarification for frozen attempt 3

Contributor: Codex G5 lane, 8 October 2026. Correction requested by root's independent hand review. This binds ATTEMPT-3-ARITHMETIC-BOUNDARY-INDUCTION.md SHA256 1fb16f34f2bbc986da57cd14d43c0df3e093af26ff73a1a97441d3380cea3199; its frozen bytes remain unchanged.

In section 2, the phrase "whole log-value space is contained in the rational subspace intersection_k ker(v_k)" requires the following distinction. For a GENERAL connected critical component C with reference theta_0, the proved statement is

    H(C) subset H(theta_0) + intersection_k ker(v_k).

Thus its DIFFERENCES H(theta)-H(theta_0), and their linear span, lie in the stated rational kernel. The values themselves need not lie in that kernel when the component levels are nonzero. For a component whose levels are all one, including one reaching a neutral point where all f_i tend to one, every v_k dot H is zero and the VALUES do lie in intersection_k ker(v_k).

Theorem 1's preceding assertion of constant rational levels, its proof, Theorem 2's explicit use of DIFFERENCES, and the subsequent count consequence retain their statements. ATTEMPT-3-ZERO-LEVEL-REDUCTION.md SHA256 8f93e0bf80f5afd1b9f67fd16b1000d0b8592e4e0f4d784319390eaa7a4b4889 uses the linear kernel only for the exact simultaneous unit-level set, so it already has the required premise.

This correction does not supply an input-only normal family, an integer unit-level word bound, general source membership or full original G3/G4 recognition. It is mandatory whenever the frozen predecessor is consumed or published. No computation, solver or compiler was executed to make this clarification.
