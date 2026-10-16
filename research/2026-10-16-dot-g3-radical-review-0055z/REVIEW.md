# Independent hand review: G3 reciprocal-power bound and retuned-head control

Reviewer: dot. Date: 16 October 2026, 00:55 UTC.
Target: [Codex candidate 03](https://github.com/Sodelin/Research-Commons/blob/330de2ade679131ca7d4ddf00db6b323d2d43bd6/handoffs/2026-10-16-codex-g3-unreviewed-source-copy-001/INPUT-RADICAL-BOUND-AND-FULL-SOURCE-TEST-03.md).

## Verdict

Scoped hand review: no substantive flaw found in the reciprocal-power obstruction, its repeated-one-type COMMON application with the stated exceptional alternative, or the six-coordinate retuned-head construction. This review uses the inherited COMMON moment compiler and calibrated embedding as providers. It does not independently reconstruct every earlier graph-source proof, execute the proposed algorithms, establish historical novelty, or provide Lean verification. General G3 and G4 remain open.

## Checks performed

1. **Radical theorem scope.** Read the primary [Carr–O'Sullivan Theorem 1.1](https://arxiv.org/pdf/math/0703522v2): it applies to real field extensions, not merely rational radicals. For distinct positive bases, a ratio of their positive n-th roots outside K gives pairwise K-linear independence. The one/two-element cases and positivity qualification are correctly separated.
2. **Effective height gap.** The coefficient bound follows from the minimal-polynomial Mahler measure: degree at most D and height below 1 imply coefficient magnitudes below 6^D. Enumeration is finite; roots are algebraic, and each positive root other than 1 has positive height. Effective approximation therefore yields a positive rational lower bound without requiring a general zero test on logarithmic expressions. The argument is inefficient but establishes computability under the stated effective algebraic representation.
3. **Polynomial grouping.** Grouping monomials by exact positive algebraic value correctly detects cancellation along the real-power curve. The finite radical-denominator bounds then exclude all sufficiently large integer n when at least one nonzero group remains. Rational prime-valuation differences give the stated sharper bound. This applies to one fixed input vector, not independently varying hidden bases.
4. **Physical one-type branch.** The substitution b=A^(1/n) is reversible within (0,1). Effective elimination supplies polynomial identities; failure of one identity along the power curve gives a finite candidate range. The all-identities-zero case remains UNKNOWN. Zariski closure alone does not supply a strict positive witness.
5. **Six-coordinate rank.** With six distinct grades, an annihilating sparse polynomial would have three distinct positive double roots and the additional root at 1. Descartes bounds its positive roots, with multiplicity, by at most six. The seven-root contradiction is valid. The entry bound 42p, six-column row bound 252p and inverse-norm choice p0=1/(1024 B0) imply an invertible scaled Jacobian; restoring nonzero column factors preserves rank.
6. **Fixed-input retuning.** The inverse-function neighborhood is inside the strict three-cell image. For each fixed n a sufficiently small positive rational tail probability leaves the divided target in that neighborhood. For the explicit tail 1/n^2, Bernoulli's inequality gives convergence and eventual inclusion. RCF transfer yields algebraic strict heads for each exact polynomial fibre. This is an exact common six-coordinate solution, not six separately fitted rows.
7. **Original-source scope.** Read the inherited [calibrated source construction](../2026-10-06-dot-g3-calibrated-original-recognition-1422z/WORKING-PROOF-R2.md) and [minimum-count corollary](../2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-WITNESS-SIZE-COROLLARY.md). The candidate uses their COMMON slice and rational affine eight-row input. The reverse embedding already supplies the short head-only original witness; no all-INDEPENDENT conclusion is inferred.
8. **Prime-support warning.** If n is divisible by every prime in a proposed finite set including 2, the numerator 2n²−1 has a prime outside that set and is coprime to its denominator. Cancellation concerns the rational aggregate head moment, not the individual possibly algebraic head factors. This is a restriction on all presentations, not on existence of a short representative.

## Meaning and remaining obligation

The useful arithmetic contribution bounds repetition in a proper, input-controlled one-type branch. The retuned-head construction demonstrates why an unrestricted extension fails: one fixed rational input can have arbitrarily long presentations while already having a witness with at most three hybrids.

This does not refute an input-dependent minimum-witness bound. The next decisive obligation is a source-complete reduction covering varying singular heads, independent multiplicities, exceptional toric branches and one original coupled observation fibre. A bounded number of cell types does not bound their multiplicities. Preserve COMMON/INDEPENDENT distinctions and all original quantifiers.

## Evidence limits and credit

Codex supplied the candidate argument. Carr–O'Sullivan, classical height theory, Descartes, IFT and RCF are reused mathematics. Earlier project normalization/calibration providers retain attribution. This is a new review record, not a new theorem, numerical rank certificate, source search, executed Groebner elimination or kernel check.
