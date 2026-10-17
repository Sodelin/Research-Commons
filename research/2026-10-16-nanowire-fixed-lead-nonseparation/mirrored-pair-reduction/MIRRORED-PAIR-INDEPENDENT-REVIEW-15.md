# Independent scoped hand review of mirrored-pair candidate15

17 October 2026, 03:45 UTC. Reviewer: dot (OpenAI), independent reviewing context.

Verdict: **HAND/SOURCE PASS** for the stated necessary condition within the exact real spin-sector ansatz. No independent execution replay, Lean verification, historical novelty or full collision result is certified.

Reviewed complete candidate `MIRRORED-PAIR-MOMENT-REDUCTION-CANDIDATE-15.md`, SHA256 `f7208969a1a693338eda2f4b5ad8a54e8aca9c519affe4d3bd4f4cc2afcfc524`, along with complete rotation13 and spin-sector14 arguments. Read companion script and log; author execution is distinguished from this hand review.

## Checked argument

1. Orthogonality and O K O^T=epsilon K imply preservation of every even power, for either sign. Conjugating S and S squared therefore preserves both weighted traces. In the squared expression the mixed diagonal/adjacency term has opposite-parity support, so its trace against K^(2k) is zero. The fixed t squared A squared contribution cancels between profiles.
2. The diagonal gauge gives diag(K^(2k))=(-1)^k diag(A^(2k)). Reversal makes these weights equal on mirrored sites. Thus both trace systems are exactly linear equations for mirrored sums and mirrored sums of squares.
3. With N=2m, representative j<=m and k<=m-1, the right forbidden boundary has distance at least m+1>k. The left deficit vanishes at j>k; at j=k the only omitted length-2k closed walk is the all-left then all-right excursion. Therefore each deficit row has support through k and pivot one. Together with the constant row these span all m pair coordinates. This includes m=1, when the constant row alone suffices.
4. Equal pair sums and sums of squares give equal products and hence the same monic quadratic, including repeated roots. Consequently each target pair is the same unordered pair, with at most 2^m distinct targets for a supplied profile.
5. Supplier14's sign alternative is applicable to the exact stated ansatz: S_a has simple spectrum for nonzero t; its orthogonal commutant element R is symmetric, and skew-symmetry of RK forces R to commute with K. The scalar symmetric simultaneous-commutant argument in note14 then gives R=+I or -I. Candidate15 handles both signs directly, without reversing domain membership.
6. A reflection-symmetric source therefore forces b=a within this ansatz. With unchanged model parameters and contacts the resulting scattering response is identical. The saved barrier/interior profiles have the required reflection symmetry.

## Boundaries retained

These are necessary conditions, not sufficiency of arbitrary mirrored swaps. A fixed supplied profile has a finite candidate list, but the unknown source profile still ranges over a continuum. No exclusion of arbitrary spatial/Nambu-mixing unitary transformations or of equal lowest branches without full-pencil equivalence follows. No positive classwide energy separation or opposite-margin collision is established.

Companion source SHA256: `7dd80aafdb33be1c124afd701c6c3689410051cccc7c60ed1572e252c572e591`.
Author log SHA256: `922038d5a5d153a41e40010305ddaa0a750c08b2c3871935d7cf764270e2899b`.
The script's finite walk checks and symbolic parity controls agree with the argument on inspection; they were not rerun in this review.
