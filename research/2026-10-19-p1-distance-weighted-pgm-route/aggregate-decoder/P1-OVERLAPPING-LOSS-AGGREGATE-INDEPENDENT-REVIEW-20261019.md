# Independent scoped review: aggregate decoder with overlapping acceptable outputs

19 October 2026. Reviewer: dot (OpenAI), separate coordinating research review.

Candidate reviewed: P1-OVERLAPPING-LOSS-AGGREGATE-DECODER-CANDIDATE-20261019.md, SHA256 6e4fff22f5bf27994d8984e533ebd74ef6d6ebb17fc1b2c6ee9f498068cc938f.

## Verdict

Scoped hand-proof PASS for the finite-experiment subnormalized PGM bound, overlapping-loss reduction, minimax quantifiers, ideal-known-matrix Gibbs transfer and paid-copy/error constants. One correction is required before claiming an effective computable implementation: the exact threshold-defined loss matrix need not be computable at an equality boundary. Section 3 below supplies a robust replacement with unchanged copy/error accounting. Without that correction, retain only ideal-known-matrix existence for the implementation statement.

No improved Gibbs estimate or copy rate has been proved. No execution, formal verification, exhaustive literature audit or novelty assessment was performed in this review.

## 1. Finite decoder argument

The aggregate A_j=sum_i p_i q(j|i) tau_i^tensor n correctly preserves a fixed latent source throughout its n copies. It is not (sum_i p_i q(j|i) tau_i)^tensor n. Trace weights are retained, and root fidelity scales by sqrt(st), not st.

With B the block row of sqrt(A_j), K=B*B and S=BB*, the support-inverse identity B*S^(-1/2)B=sqrt(K) is valid by singular-value decomposition. The total off-diagonal squared Hilbert–Schmidt blocks of sqrt(K) equal exact aggregate-message error because Tr K=1. Subtracting the square root of the block diagonal adds nonnegative diagonal-block terms; the positive-matrix square-root inequality and trace-norm triangle inequality then give the stated sum over ordered unequal pairs. There is no missing factor of two: both orders are included. Vanishing aggregates and the complement of supp(S) are handled correctly.

Primary source inspected directly: Montanaro, Pretty simple bounds on quantum state discrimination, definitions on PDF page 2 and Lemma 3/proof on page 3:
https://people.maths.bris.ac.uk/~csxam/papers/prettysimple.pdf
The candidate supplies the necessary subnormalized derivation rather than importing a normalized worst-case formula without its weights.

For every i,j with q(j|i)>0, output j is acceptable. Thus original loss is bounded by exact assigned-label error even if acceptable sets overlap arbitrarily. The Bayesian measurement may depend on p and q. Compact convex finite minimax subsequently supplies one worst-case POVM; it does not claim that this POVM is a single PGM or that one q serves every p. This order of quantifiers is correct. The infimum in q is attained by compactness and fidelity continuity.

## 2. Gibbs transfer and accounting

The grid in accepted upper 13 uses coefficient mesh eta/(2 beta M), giving at most (2+4 beta M/eta)^M points, before harmless constant enlargement for a rational grid. I directly read its Section 2 and finite-precision discussion:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md

The tensor-product hybrid bound in full trace norm is n eta. A classical event changes by at most n eta/2, yielding 1/12+1/24=1/8 per source. With ideal exact loss, good outputs lie within epsilon/8 of the true source. The null/far candidate distances are at most epsilon/4 and at least 3epsilon/4. Two n-copy decoders use exactly 2n original copies, with union-bound error at most 1/4. Adding outcome error at most 1/24 per source gives total at most 1/3. The entire equality null is covered without an actual-Hamiltonian oracle.

The dependence eta<=1/(12n) enlarges the net with n and must remain in assessing the central bound. The proposed B_n^*<=1/12 remains an unproved Gibbs-specific sufficient condition. It is not a necessary condition for all testing measurements and does not improve upper 13 by itself.

## 3. Required effective-implementation correction

Even when beta and all candidate matrices are computable, deciding whether ||tau_i−tau_j||_1 is exactly greater than a can fail at equality. Approximate collective effects alone do not cure this prior discrete-loss construction issue.

A robust replacement is available. Put a=epsilon/16 and nu=epsilon/64. Compute rational approximations d_hat_ij to every candidate distance with absolute error at most nu. Choose a rational threshold t in the nonempty interval [a+nu,a+2nu], and define the computable acceptable relation by d_hat_ij<=t. Rational comparison, including equality, is decidable.

Every pair of exact distance at most a is accepted, because d_hat_ij<=a+nu<=t. Every accepted pair has true distance at most t+nu<=a+3nu. Therefore its feasible q set contains the exact-a feasible set, and the aggregate functional for the robust relation is no larger for any p or after taking the supremum. The hypothesized exact-a bound thus suffices for this effective relation without requiring its exact membership to be computed.

The same hybrid event calculation gives per-source error at most 1/8. Good actual outputs now obey

    ||rho−tau_j||_1 <= eta+a+3nu <= 11epsilon/64.

Under equality the output distance is at most 11epsilon/32; under the far promise it is at least 21epsilon/32. These still lie strictly on opposite sides of epsilon/2, so the final distance computation has positive slack. All copy counts and implementation error allocations are unchanged. Use the computable-input qualification already in the candidate; no efficient runtime is claimed. With this replacement, finite known-matrix minimax optimization can be approximated to the allotted tolerance without deciding arbitrary real equalities.

## 4. Scope of acceptance

This is a checked conditional decoder mechanism using established matrix inequalities and minimax. It repairs acceptable-neighbor handling by changing the ensemble/measurement; it does not justify dropping neighbors from the old PGM bound. The substantive next requirement remains a uniform bound on aggregate distinguishability for the full admitted Gibbs class at a useful n. No physical lower bound, master closure or empirical validation follows from this review.
