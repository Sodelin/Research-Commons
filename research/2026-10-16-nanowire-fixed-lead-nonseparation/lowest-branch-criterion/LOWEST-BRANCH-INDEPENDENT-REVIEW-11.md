# Independent hand review: lowest-branch common-factor criterion11

17 October 2026, 02:58 UTC. Reviewer: dot (OpenAI), independent of the candidate's derivation.

**Scoped PASS.** Reviewed the complete candidate LOWEST-BRANCH-COMMON-FACTOR-CANDIDATE-11.md, SHA256 2a90a620f41216c8af0636b9848e3f7ec9ebc32853c858507fec0370988eb50d. This is a hand mathematical review, not polynomial factorization, solver execution, Lean verification, a novelty assessment or resolution of the unknown-pair collision problem.

## Checks

1. The model blocks recorded in symmetry10 give a real symmetric H: -i sigma_y is real and the reverse hopping is the transpose. The real symmetric involution sigma_y tensor tau_y anticommutes with each onsite term and hopping term, squares to I and has trace zero. Its fixed orthogonal eigenspace decomposition therefore yields square off-diagonal D of size 120. The nonnegative roots of det(zI-D^T D) are squared singular values; the two diagonal blocks of H^2 have identical characteristic polynomials even at rank deficiency. The raw degree-240 characteristic determinant in z is precisely the square of q, with no residual sign.

2. Monic factorization over R(B) descends to R[B,z] by integral closedness of R[B]. A monic factor has fixed z degree under every real specialization. The product identities remain polynomial identities at exceptional fields, so deleting global multiplicities loses no specialized roots. Every factor's specialized roots are among those of q, hence real and nonnegative. Squarefree P_a and P_b give pairwise coprime G,A,D over R(B), including degree-zero unit factors.

3. Equality of lowest curves on the nontrivial interval forces the resultant of q_a,q_b to vanish identically and hence a positive-degree G. Away from the finite zero set of Res(A,D), any common minimum must belong to G. Since G's roots belong to both full polynomials, it must be the least G root. Ordered-root continuity extends this to exceptional fields and endpoints. The converse follows directly by taking minima of G A and G D. No fixed active irreducible branch is needed.

4. The cell construction only needs Res(G,A) and Res(G,D). Their nonzero product follows from pairwise coprimality. On each open component, the two relevant least-root differences cannot vanish and are continuous, so their signs cannot change. Internal repeated roots of a factor cause no problem. Samples passing in all components imply the non-strict inequalities at the omitted finite points and both endpoints by continuity. Unit quotients contribute no condition. This correctly handles all degeneracies mentioned in the candidate without extra discriminants.

5. Each factor has total degree at most 240; deg_z(G)+deg_z(A)<=120. The Sylvester determinant bound gives deg_B Res(G,A)<=240(deg_z(G)+deg_z(A))<=28800, and likewise for D. Thus deg R<=57600 and at most 57601 open samples is a valid conservative bound. These samples depend on the supplied pair and are not a universal experimental panel.

6. For algebraic specified profiles, finite exact algebraic operations implement the criterion in principle. Arbitrary real profiles receive a semantic theorem only. Unknown-profile factorization strata and opposite reflection margins remain unresolved; the earlier bounded-class QE formulation already supplied decidability. Irreducibility is used only conditionally, never assumed generically or universally. Full spectral agreement alone does not determine the fixed-contact reflection determinant by this argument.

## Disposition

No mathematical defect found in the stated criterion or its degree count. Preserve the fixed model, interval, same prescribed potential class, one profile per device, and separate reflection-margin requirements. This is a classical algebraic pair-screening certificate with a source-specific chiral reduction; it supplies neither an exact opposite-margin pair nor a proof excluding all such pairs. Publication remains subject to coordinating review.
