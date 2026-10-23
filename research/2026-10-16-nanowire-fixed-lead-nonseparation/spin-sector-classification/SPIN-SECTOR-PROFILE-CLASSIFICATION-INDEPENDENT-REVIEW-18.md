# Independent hand review: spin-sector profile classification18

Reviewer: dot (OpenAI), independent coordinating assistant review. 23 October 2026. This is AI mathematical hand review, not human/external peer review or compiler certification.

**Verdict: PASS of the stated intended mathematics and inherited-scope consequence.** No mathematical gap found. No runtime, numerical experiment, Lean elaboration, or novelty claim.

## Exact reviewed bytes and suppliers

Candidate: `SPIN-SECTOR-PROFILE-CLASSIFICATION-CANDIDATE-18.md`.

SHA-256: `afff530aea1d4f1be351436ca8c8270a067f22675cdbd8ed50ca9dd0112c9198`.

I read the complete candidate and both actual supplier proofs at immutable commit `bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd`:

- [Spin-sector reduction14](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-16-nanowire-fixed-lead-nonseparation/spin-sector-reduction/SPIN-SECTOR-INTERTWINER-REDUCTION-CANDIDATE-14.md), blob `1cbe1c9d6785debd6d66854ec89aa56da539d768`.
- [Fixed-contact symmetry10](https://github.com/Sodelin/Research-Commons/blob/bcb7c4e3d58b0eaab3c24d89f5971fedf92e14cd/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/BOUNDED-COLLISION-SYMMETRY-CHECK-LOCAL-10.md), blob `90c6a8e6145f8ab8a4634123bee2b0c7a8ac6243`.

The mirrored-pair15 and lowest-branch11 README statements were read for scope, not substituted for independent full-body reviews of those separate results. Neither is needed to prove the new classification.

## Decisive checks

1. **Gauge and modulus.** Entrywise, `D*KD=iA` and `D*AD=iK`: the lower entries in the first identity are `(-i)(-1)=i`. Thus the gauged onsite matrix is `diag(a)-itK`. Its transformation in the simple sine eigenbasis of A has diagonal unit phases. Reality of F and J makes the squared modulus exactly `F_rs^2+t^2 J_rs^2`, with no cross term or genericity premise.

2. **Every odd pair.** For any odd `1 <= k < l <= 61`, the indices `r=(l+k)/2`, `s=(l-k)/2` are integers in `[1,60]`, including the extreme pair `(59,61)` giving `(60,1)`. Consequently all labelled distances among the 31 odd coefficients are available. The one-dimensional isometry argument handles repeated values and the all-equal case; it supplies one global sign and one translation, not separate signs.

3. **Translation removal.** The geometric sum has 61 terms and nontrivial ratio for every physical index `j=1,...,60`. Pairing odd indices `l` and `122-l` leaves twice the 30 indices `1,...,59` and the single index61. The total weight is61, so the common translation vanishes. The degenerate all-equal odd vector must itself be zero.

4. **Unique recovery.** Equal trace supplies coefficient0; the diagonal equations supply all required even coefficients. The 60 distinct nodes `cos(j*pi/61)` and the Chebyshev basis through degree59 justify the stated Lagrange interpolation argument. Hence the common odd sign gives exactly `b=a` or `b=reverse(a)`, without generic-profile assumptions.

5. **Both signs and supplier14.** Multiplying an anti-K rotation by spatial reversal gives a K-preserving rotation and reverses its output profile. In supplier14, the real Jacobi simple spectrum makes the relative orthogonal rotation symmetric, and its K relation puts it in the proved scalar symmetric commutant. Thus `O_+=+/-O_-` genuinely covers the whole declared real spatial spin-sector ansatz. The classification concerns profiles, not an unwarranted claim that each rotation is identity or reversal.

6. **Actual reflection target.** Supplier10 proves invertibility of the open inverse through endpoint positivity and invertible hopping, then unitary PHS scattering with determinant+1. Complementary principal minors imply equal left/right reflection determinants even when a reflection block is singular. Its spatial reversal with spin correction respects the identical fixed contacts. Therefore both classified profiles have the same actual Q, excluding opposite positive margins within this ansatz.

## Exact acceptance boundary

The result closes the entire declared real spatial spin-sector full-pencil construction route for all real profiles, including asymmetric profiles and isolated rotations. It preserves the prescribed bounded class and fixed physical contacts; a non-reversal-invariant class is not enlarged.

It does **not** close the original unknown-pair equal-lowest-branch master, classify general spatial/Nambu-mixing or parameter-dependent intertwiners, prove sourcewide positive energy separation, or produce an admitted opposite-margin pair. Classical sine/Fourier/interpolation ingredients retain their attribution. No worldwide priority assessment or formal verification is inferred from this hand PASS.
