# Independent review: demographic interpolation and source quotient

Reviewer: Codex / laplace_recovery, 14 October 2026.
Reviewed author: Codex whole-source lane.
Pinned file: `DEMOGRAPHIC-EXACT-INTERPOLATION-AND-SOURCE-QUOTIENT.md`.
SHA256: `27b6e32c8f655d0da16ffca9bd300250b612d3c8b60fff9daa3ea4d4b984de9f`.

**Verdict: PASS, at the stated demographic and source-quotient scope.** No correction requested. This is an independent hand check of the displayed construction and its original-source applicability, not a fresh audit of the cited primary PDFs. The standard invertible transformation between the finite expected SFS and the vector of first-coalescence expectations is reused as stated.

For the degree-n polynomial in Section 2 there are exactly n+1 interval coefficients and `h=H/(n+1)`, so the step function has support precisely inside the fixed coalescent-time window. Integrating each interval gives the common factor `(1-exp(-lambda h))/lambda` times `sum a_j exp(-lambda jh)`, proving the displayed Laplace identity. Its roots cancel all `lambda_2,...,lambda_n`; strict increase of `lambda_m` ensures no cancellation for any m>n. The unchanged `c_2=1` prevents a larger-sample vector from becoming proportional to the target vector, which also establishes the normalized-SFS discrepancy.

The chosen epsilon has `epsilon |a_j|<1/2`, hence every population height is strictly between 1/2 and 3/2. Physical interval durations are `h(1+epsilon a_j)>0`. The root at 1 gives zero integral of the perturbation, so the time change fixes H exactly and is the identity thereafter. Each rival is one deterministic finite history with one tuple shared by every sample size; the constant target and physical window do not change with n.

The original-source quotient is decisive. With `t'(tau)=eta_tilde(tau)` and `eta(t(tau))=eta_tilde(tau)`, change of variables gives `integral_0^H dt/eta(t)=H`. A finite subdivision has generators that are scalar multiples of the same full labelled-forest Kingman generator. Its product is therefore exactly `exp(H Q_m)` at every finite m, including all off-diagonal genealogy coordinates. Composing any legal exterior cannot distinguish two identical boundary kernels. This is an equality of the entire permitted topology response law, so the demographic rival is not the required inequivalent G4 rival even if its extra rate-change vertices were provisionally admitted.

The extension to an ordinary population or arm path correctly requires no intervening meeting or fresh routing event. Introducing such events would leave the scalar-generator calculation and would require a new full-law proof.

This packet provides a valid fixed-target exact demographic nonforcing example and an exact failure of its direct G4 transplant. It proves neither INDEPENDENT finite forcing nor an admitted fixed-target all-prefix impossibility construction. No computation, Lean verification, or historical-novelty assessment is added by this review.
