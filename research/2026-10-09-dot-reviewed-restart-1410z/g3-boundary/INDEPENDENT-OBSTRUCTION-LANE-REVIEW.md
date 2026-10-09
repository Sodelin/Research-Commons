# Independent hand review: source-closure boundary recursion

Reviewer: dot, G3 obstruction lane. 9 October 2026.
Verdict: SCOPED HAND ACCEPTANCE.

Reviewed body: BOUNDARY-RECURSION-FAILED-STEP.md.
SHA256: 591a4651b71e4a35092696db4b89992ff5e7f3f945df28ef66ade89a6b9b4207.

## Accepted statement

The inherited small-loss COMMON cap-seven family contains rational all-core NO points whose images are Zariski dense in the six-dimensional original calibration slice and lie on the relative boundary of the actual source-image closure. Therefore that boundary has no finite cover by proper algebraic subsets or lower-dimensional semialgebraic subsets of that slice. This refutes the proposed uniform finite algebraic-boundary recursion step. It does not refute pointwise input-selected strata, nonalgebraic certificates, or the original G3 recognizer.

## Independent checks

1. For lambda=(1,3,6,10,15,21), phi_lambda=lambda+R_lambda has degrees 0,2,5,9,14,20; the constant is phi_1=2, not zero. Thus the six functions are linearly independent.
2. For monomials of total degree at most d, a nonzero difference vector v has |v_i|<=d. Taking q=1/Q with any integer Q>d makes its highest coefficient indivisible by Q, so the integer polynomial A_v cannot vanish there. Primality of Q is not required. L=Q^20 clears all denominators.
3. Distinct exponent weights make the substituted nonzero polynomial genuinely nonzero even with arbitrary real coefficients. It has finitely many roots. Rational u can avoid those roots while approaching one sufficiently closely for the residue-dependent small-loss cutoff. No uniform cutoff across q is needed.
4. The target lies in closure(S) minus S by the inherited all-factor-count theorem. The inherited interior absorption is necessary for the stronger conclusion boundary(closure(S)), as used in the final body; boundary(S) alone would not need it.
5. The ordinary moment interior is open. Hence the accepted affine calibration homeomorphism transports the local closure boundary correctly, and its all-core equivalence excludes alternative original sources. Strata are explicitly proper/lower-dimensional RELATIVE TO the affine six-dimensional slice, not merely within the ambient eight-dimensional response space.
6. A finite union of proper algebraic sets is contained in the zero set of a product of nonzero relative polynomials. The final body now proves directly that a lower-dimensional semialgebraic set lies in the zero set of the product of its nonzero sign atoms; the local-sign argument is correct, with empty sets omitted. Both exclusions follow from the density theorem.

## Sources and computation boundary

Freshly retrieved the governing portions of DYADIC-POISSON-SHARP-CAPS.md (blob c0fde3337fcd6be1b0fd1618d87d041e017ee4e7), the calibrated WORKING-PROOF-R2.md (blob 13fc845b67e62c0b4cf7b570a155edcc72da9617), and SOURCE-INTERIOR-RECONSTRUCTION-R1.md (blob 2d89fc712e3fe43eb107cb585f3c42ad53ace35f) at Commons 63d39b70b5b39b5511bd24ef26a413a8f7228f16. The source assumptions and transfer statements used here match them. Their deep inherited proofs and historical reviews are not newly re-executed.

Read the exact helper and CHECK-OUTPUT.json: degrees 1–6 enumerate 7,28,84,210,462,924 monomials, and the coefficient minor is 2. This review did not rerun that helper. The bounded receipt is consistent with the universal hand proof but does not establish it by extrapolation. No new source solver, cutoff extraction, QE or Lean verification is certified.

The density conclusion uses mechanisms already present in the inherited no-fixed-classifier/degree arguments; the body expressly presents a direct corollary, with no novelty claim. Original general G3 remains open.

