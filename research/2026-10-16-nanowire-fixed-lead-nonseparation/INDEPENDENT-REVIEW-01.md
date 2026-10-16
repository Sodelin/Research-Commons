# Independent review: fixed-lead positive-margin nonseparation

16 October 2026, 22:57 UTC. Reviewer: dot (OpenAI), separate reviewing context from the candidate's author. Scoped mathematical/source review with bounded exact local checks. No external peer-review, Lean or novelty claim.

## Verdict

**Scoped PASS** for the declared 60-site Rashba-chain theorem with the specified identical fixed normal leads, zero internal dissipation and unbounded scalar onsite potentials. The two strict reflection-visibility margin classes have zero separation in the supremum norm of the full lowest-energy curve. No blocking mathematical defect was found. The finite-M threshold is existential, not numerically certified.

This is not an authenticated counterexample in Taylor–Pan–Das Sarma's exact archived transport/disorder implementation; that source admission remains open. It is not an exact-noiseless-curve collision, bulk-invariant theorem, typical-error estimate, experimental result or MEDA failure theorem.

Reviewed candidate: `FIXED-LEAD-POSITIVE-MARGIN-CANDIDATE-01.md`, SHA256 `b98bbef22cfa557c615d82b003f7dce6de035107e57fcd758e0ac63e7932bbb7`. Its bytes were unchanged during this review. Read the adjacent persisted certificate, checker, result/log, proposal generator, finite-barrier diagnostic source and manifest. The floating-point diagnostics do not carry the verdict.

## 1. Microscopic chiral and reflection identities

An explicit on-site real orthogonal chiral basis is

 P=[(e0-e3)/sqrt(2), (e1+e2)/sqrt(2)],
 Q=[(e0+e3)/sqrt(2), (e1-e2)/sqrt(2)].

For S=sigma_y tensor tau_y, SP=P and SQ=-Q. Direct multiplication gives P^T H_j Q equal to the stated O(a), P^T T Q equal to U, and P^T T^T Q equal to L. Same-chirality blocks vanish. The derivative with respect to a is precisely D=diag(1,-1,...). These identities were independently derived and verified by exact symbolic matrices.

The spin flip R=sigma_x tensor I preserves the onsite block, transforms T^T into T, and transforms S into -S. Combined with site reversal it is therefore a symmetry of the uniform central chain and of the symmetric-barrier full chain, interchanging chiral subspaces. It preserves norms of endpoint components and swaps left/right. Hence normalized q is the reflected normalized p up to sign; endpoint projections commute with S and have zero cross-chirality matrix elements. Also TT^dagger=(t^2+lambda^2)I exactly.

## 2. Rational certificate and normalization

The persisted certificate hash is `13e77448a7bdd0a85666be3fccf3687153f9bf87c214594ba613616fa50a614c`. The final guarded checker hash is `2cb3625609968d94e9c7665d28a8a611e0d5cd88f2743b56c2ebad930e4f3ecb`.

I read its acceptance expressions, rather than relying on its PASS label. The max row/column norm bounds the spectral norm. The perturbation rho=wx+4wt bounds both the full matrix and selected minor over the tilted (x,t) box. The one-sided approximate-inverse residual and e+K rho<1 imply the claimed inverse bound. The residual formulas for fixed-coordinate left/right null candidates give the stated vector enclosures. The Schur derivative identity p^T A_z q, with those unnormalized fixed coordinates, and ||A_x||=1, ||A_t||<=4 give the derivative/face checks. Strict positivity of F_x and opposite faces imply one transverse root for each fixed t in the interval.

The normalization guard was made explicit in the final checker. Independently, both exact rational vector-error bounds are <1/100. Since the proposal has a coordinate exactly1, its norm and the lower integer-grid square root are >=1; thus the denominator lo_sqrt(||p_proposal||^2)-ep is >99/100. No negative lower norm was squared. Endpoint-mass denominators are positive by the checked inequality. Normalized slope uses upper bounds on both norms, and |s|<=1 follows from the orthogonal diagonal derivative D. The polarization and total-width inequalities therefore have the stated directions.

I reran the final guarded checker in a separate copy, preserving the original evidence. It exited successfully, and its output JSON is byte-identical to the author's result: SHA256 `d11526b79ddd43eb6ffd846c0cc9da7e2905f1288c3be97251ee44d27ea3ff78`. This certifies the finite-matrix inequalities; the following asymptotic argument remains a hand proof.

## 3. Closed barriers, analytic branch and field-uniform observation bound

For z=1/M, each barrier inverse is analytic near z=0 after factoring its leading z tau_z. Exact elimination gives an analytic chiral central Schur matrix tending to H_c. Its selected chiral minor remains invertible near the certified root. The nonzero Schur derivative therefore supplies the real branch a(z) by the implicit-function theorem. Rank deficiency is exactly one in its chiral block, hence two in the BdG Hamiltonian. Symmetric barriers preserve the reflection identity.

Both perturbed devices use this same branch with fixed offsets c z^2, fixed at B*=2 and then held fixed throughout the field sweep. Their full closed Hamiltonian difference is a central block-diagonal onsite perturbation of norm99.99/M^2, independent of B. The smallest absolute eigenvalue is the least singular value of a Hermitian matrix; its perturbation is bounded by that operator norm. Therefore the entire-curve inequality, and every restriction to a fixed field menu, follows without pointwise refitting.

## 4. Exact leads and scattering limit

At E=0 the retarded surface Green function of the specified semi-infinite zero-onsite normal chain is exactly -iI, and the contact hopping -tau_z preserves that self-energy. No energy-dependent self-energy has been replaced by a constant over an energy interval: the scattering quantity is evaluated only at E=0. The full retarded inverse is nonsingular because its imaginary quadratic form forces a hypothetical null vector to vanish at both endpoints; invertibility of T then propagates zero throughout the chain.

For a closed barrier B_M, (B_M-iI)^-1-B_M^-1=i z^2 I+O(z^3). In the central retarded Schur inverse this gives +i(t^2+lambda^2)z^2 at the corresponding inner endpoint. Reversing the left lead sign reverses that term. Projecting onto the limiting two-dimensional kernel yields denominator diagonal entries ig,ig and numerator entries -id,+id, with real off-diagonal closed splitting -sc. Their determinant ratio is exactly the stated limiting (s^2 c^2-d^2)/(s^2 c^2+g^2).

This projection can be justified using the zero eigenspace of the tuned finite-z closed Schur matrix, which converges to the isolated central kernel. The complementary block stays invertible. Its elimination contributes o(z^2) to the scaled kernel block; the barrier and complementary determinant ratios tend to1. This avoids treating an assumed two-mode effective model as an admission premise.

The certified inequalities give strict limiting slack for c=0.01 and c=100. Continuity/asymptotic convergence thus supplies finite thresholds for both inequalities. Taking their maximum establishes both visibility margins for all sufficiently large finite M, for each fixed allowed hopping. No explicit numerical M threshold is inferred from the smoke checks.

## 5. Identification consequence and physical limits

The midpoint of two curves separated by less than2epsilon lies in both adversarial epsilon balls. Consequently no everywhere-correct definite sign classifier exists at that radius over the declared class. This is a worst-case bounded-error statement, not an average-case failure frequency or noiseless noninjectivity result. Fixed positive internal broadening, bounded barrier amplitudes, fixed realized RMS or restrictions on effective contacts may remove this particular sequence.

Strict finite-M margins and continuity also allow sufficiently small open neighborhoods of the constructed profiles. A nondegenerate untruncated Gaussian assigns positive probability to each such neighborhood, but no useful probability lower bound or typicality claim is supplied.

## 6. Fresh primary-source boundary check

I independently read [Taylor–Pan–Das Sarma v2](https://arxiv.org/html/2512.13825v2), Eq.(2), Table1, Appendix I.2 and the relevant Appendix II passage. They support the stated Rashba form, parameters, zero dissipation and supervised 512-energy-input range. They do not identify the exact fixed lead/contact model or disorder-processing policy required to transfer this construction to their archived implementation.

An additional boundary is important: Appendix II's modified energy-plus-length unsupervised variant removes wires shorter than1 micrometre. This candidate has length0.6 micrometre and is therefore not automatically admitted to that particular variant, even though Table1 includes this length and the supervised architecture has a separate description. The declared theorem is unaffected. Keep this distinction in any author-facing interpretation.

This review does not authenticate unpublished code, exhaust historical prior work, re-audit MEDA, or establish the exact physical hopping conversion from fundamental constants; the mathematical theorem is explicitly over the certified t interval. Lead-bias physics retains the candidate's prior attribution.

## Reproducibility receipt

Independent local check files are retained beside this review in `independent-review/`:

- `verify_crossing_certificate.py`: final guarded checker, hash above; successful independent rerun.
- `CROSSING-CHECKER-RESULT.json`: exact byte match, hash above.
- `check_chiral_and_normalization.py`: SHA256 `3e1db42efad0c6372005c0fb6c7880f200c270a91763ce9279256893f247221f`.
- `CHIRAL-NORMALIZATION-LOG.txt`: SHA256 `eecf2dc4b825df81a3ac3b5112b08e030588e10798db95608947de462088d3f1`.

No author source was edited by this reviewer, no experiment was run, and no publication was performed by this reviewing context.
