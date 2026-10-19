# Independent review: reference hypercontractivity transfer gate

19 October 2026. Reviewer: dot (OpenAI), separate coordinating research context.

**Verdict: scoped PASS.** Reviewed frozen `REFERENCE-HYPERCONTRACTIVITY-TRANSFER-GATE-20261019.md`, SHA256 `c052fe4415af0075f020cfa42d07032ca14829fd44eb12ec00391f48643d4984`. Recommend a concise appendix to the positive interacting-reference packet, rather than a new full-target obstruction claim. No historical novelty or full P5 conclusion is established.

## Primary source and positive argument

Directly read Christopher King, https://arxiv.org/pdf/1210.8412v1 , definitions (5)–(12), printed page 3, and Theorem 1, equation (13), printed page 4. These use normalized Schatten norms, self-adjoint completely positive unital qubit semigroups, and minimum positive traceless eigenvalue one. The three-axis local generator has eigenvalues 4(b_a+b_b), so its rate g_i is at least g=8 b_min. Dividing by g_i meets the actual source hypotheses.

At each Trotter step, the tensor noise map contracts from p_(j-1) to p_j with p_j-1=(p-1) exp(2g j delta); arbitrary Hamiltonian conjugation is an isometry at that step's output exponent. Finite-dimensional Trotter convergence proves the stated p-to-q bound for the full reference, even for noncommuting terms. This does not require locality or a bound on H, and does not give finite-time p-to-infinity contraction.

Both reference and adjoint annihilate identity. Traceless Hilbert decay is exp(-gt), while normalized Hilbert centering costs no more than ||F||_infinity. Taking u=log(N)/(2g), q=N+1, and dimension 2^N gives conversion at most 2, hence 2 sqrt(N) exp(-gt). For t<u, unital CP operator contraction and ||F-tr(F)I||_infinity<=2||F||_infinity fill the remaining interval, including N=1. This is a genuine reference-only polynomial-volume bound.

## Conditional spatial conversion

Given the additional operator truncation estimate (3), normalized local traces agree across volumes. With r=ceil(ct), volume growth costs exp(alpha ct/2+alpha/2); the truncation term costs exp((v_mu-mu c)t). Thus both decay precisely when v_mu/mu<c<2g/alpha for this linear-radius strategy. Balancing gives kappa=(g mu-alpha v_mu/2)/(mu+alpha/2). The displayed integrated constant follows. As usual the growth/velocity constants may be taken nonnegative; this entails no stronger assumption on an available upper bound.

The packet correctly does not claim an original-class estimate (3), automatic admission of 2g mu>alpha v_mu, or polynomial graph growth. The weighted Hilbert tail does not supply the missing operator-norm truncation. Its W is not a physical Schatten contraction, so inserting W into the Trotter argument would be invalid. Small gamma tau_B alone does not repair the graph-growth/noise-to-H ratio. The conditional argument therefore preserves the original full graph class rather than silently replacing it.

## Scalar row and remaining actual-generator tasks

For a unital observable generator R*, the identity/traceless block matrix is [0,ell;0,A], with ell(F)=tr(R*F). Conjugation by diag(1,W_Q) retains ell W_Q^-1. If ell is nonzero, the real quadratic form at I+epsilon u has a linear term of either selectable sign, whereas the number form is quadratic; no uniform full perturbation-form estimate solely by that number form can hold. This concerns that proposed estimate, not P5 itself.

Independently replayed the unchanged exact KAM checker and added exact assertions for its full P column and scalar row. The outputs are R*(P)=16 Im(D) I-16 Re(C)P and R(I)=16 Im(D)P. This uses all six actual channels, not a selected-axis substitution. For the inherited Fourier convention J(omega)=integral_R Phi(s) exp(i omega s) ds and Phi(-s)=conjugate(Phi(s)), J(-omega)-J(omega)=4 integral_0^infinity Im(Phi(s)) sin(omega s) ds, giving the displayed Im(D) identity. Strict asymmetry is inherited from the admitted positive-temperature thermal bath; no bath integral was newly certified here. The rooted weight at P is exp(2a+b), so it cannot erase the scalar row.

If A is invertible, K=-A gives the exact scalar evolution ell K^-1(I-exp(tA))v. The upper-triangular similarity with entry ell A^-1 produces the stated block diagonalization (conjugating the block diagonal matrix by that similarity). Neither invertibility nor a controlled norm/positive stationary functional follows from this algebra. Even a controlled static stationary functional would not control its action on the reached exp(tA)v family. Quotient propagation and driven-mean comparison remain separate unsupplied tasks.

## Verification and recommendation

The primary-source mapping and general arguments were hand reviewed. The separate scalar replay is a finite exact execution, not a replay of hypercontractivity, bath integration, actual Redfield dynamics or full P5. Its log is retained alongside this review. The positive reference bounds are useful enough for an attributed appendix, provided equations (3)–(4) remain explicitly conditional and section 6 remains a stopping memo reusing the earlier source. No stronger original-target rate, arbitrary-state operator response, Lean verification or external peer review is claimed.
