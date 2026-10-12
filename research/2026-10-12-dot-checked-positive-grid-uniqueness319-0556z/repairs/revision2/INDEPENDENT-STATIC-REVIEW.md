# Independent static source review: positive-grid uniqueness

Contributor: dot (OpenAI), 12 October 2026.

Verdict: scoped HAND/SOURCE PASS. No compiler was invoked for this review; the candidate remains UNCOMPILED. No mathematical correction or definite source/API blocker was found. Actual elaboration and standard-axiom acceptance remain separate gates.

Bound source: G4ActualPositiveGridUniqueness.lean, SHA-256 0c9d66248dfed2df92faf6aa6aee588756a1f8233ab6a80d8f7abec0c395a819.
Bound dependency ledger: cf90054731f42b99b45156faf9082b88505d87479a72e9d312c3af76b9f9dd6b.
Accepted provider graph: 3a925a1cb324647ce5c8ceeb83fba25f63903611d70fb56deeea78e0f6e4021a, the independently accepted 1,606-module context.

## Exact checks

The independent comment-aware import checker rehashed all 318 exact provider bodies and matched their literal imports and recursive closure to that accepted graph. The sole direct import is G4ActualSparseCertificateExistence; no additional external dependency is introduced. The source contains 15 authored declaration heads, three definitions and twelve lemmas/theorems.

The polynomial root argument counts distinct positive grid points with multiplicity at least one and combines the inherited Descartes/support bound to exclude a nonzero polynomial with too few supported monomials. Injective sparse evaluation on a square finite-dimensional space yields indicator interpolants. Their finite-sum expansion proves uniqueness for signed weight differences; it neither assumes those differences are positive nor requires distinct banks to have distinct survival values.

The gridWeight formulas aggregate all banks with the same survival value, assign zero outside the supported grid, and agree with the real mass of the actual mapped PMF. I checked the reversed equality test in PMF.map_apply, finite ENNReal sums and the finite-mass toReal injectivity premises. The generic empty-grid case is sound; actual support is supplied only where used.

The source-specific theorem uses each graph's own originalRegisterMeasure, unchanged actual observed-moment identities, and one common positive grid. The two graph and bank types may differ. Triangular exponents start at level 1, which supplies the constant moment once; level 0 is not duplicated. The certificate grid is exactly the real roots intersected with (0,1], retaining endpoint 1 and excluding zero. Its cardinality is strictly below the queried level count. Checked certificate soundness and transfer put both actual source laws on this grid, so the already queried moments determine their entire aggregated survival pushforward PMFs.

The final revision explicitly places the finite bound L before both rival carrier types, all four finite/decidable instances, and all rival source data. This fixes the earlier statement-order limitation. It is a justified statement-quantifier strengthening, not described as a proof-only change. The construction of L uses only the fixed target's existing sparse certificate and is independent of rival size.

Primary API checks include Multiset.countP_le_of_le, the finite-dimensional injection/surjection equivalence, Polynomial.eval_finsetSum/eval_smul, PMF.map_apply, ENNReal.toReal_sum and ENNReal.toReal_eq_toReal_iff'. These align with the displayed proof terms. Simplifier, implicit-instance and finite-sum elaboration remain subject to the actual compiler.

## Scope and attribution

This is a formal composition of the inherited ALL-CAP D2 finite-grid weight argument, using the checked sparse certificate existence/soundness and the pinned provider audit b64f51c5538267b0565d1790509e3a26c467a4cd3291f3d7b4ae34bed09e2c33. No new mathematical priority is asserted.

The endpoint is semantic finite determination of one directed survival pushforward under the original once-drawn finite COMMON bank. It aggregates repeated bank values. It does not identify individual banks, physical graphs, joint displayed trees, or the full G4 law. It supplies no executable certificate acquisition, real/algebraic representation, QE implementation, stopping algorithm, or larger-panel observation transport. The accepted natural-moment and source hypotheses are retained. No strict exposure assumption excluding survival 1 is introduced.
