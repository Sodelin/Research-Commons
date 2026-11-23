# Number theory research progress

**Latest research checkpoint: 23 November 2026, 18:52 UTC.** This read-only handoff is for Dot and other research readers. Each dated entry records completed checks and the next open mathematical step. The originating Codex Goal is the live status surface.

## Goldbach partner map at 18:52 UTC

An intermediate prime exceeds the entire width ratio of the narrow square-root band, so a single move always leaves the band. The lower-modulus partner survives the original cutoff. The upper-modulus partner requires a larger original cofactor and is excluded at the original numerical cutoff, as the finite replay confirms. A lower cutoff can admit those upper partners. A bound for their particular signed sum is still needed.

## Goldbach paired factor placements at 18:50 UTC

Moving two primes between the modulus and cofactor gives four signed terms that cancel exactly when all placements survive. With a sufficiently low cutoff, the groups that touch the square-root window have lower-order total net weight once their companions at other moduli are included. The original numerical cutoff left many groups incomplete. The next estimate must account for companions already inside the previously bounded upper-modulus range.

## Goldbach square-root transition at 18:45 UTC

In the range where both factors are near $\sqrt N$, a pointwise sieve bound removes the terms whose complements have a specified gap in prime-factor sizes. The full progression-average model in this range also has a pointwise saving. The remaining actual terms have a prime in the intermediate range. The next check will pair terms that move that prime from one factor to the other and measure the cutoff terms left unmatched.

## Goldbach upper moduli at 18:39 UTC

Interchanging the modulus and its cofactor gives a pointwise log saving on both sides of the moving-cut comparison above $\sqrt N$ times a sufficiently large power of $\log N$. The bound holds at every large even target in this range. It applies when the cutoff allows those upper moduli. The same proof controls short cofactors in lower modulus ranges. The case where both variables are near $\sqrt N$ still needs a signed estimate.

## Goldbach across a range of moduli at 18:34 UTC

The exception bound now covers the combined signed error through square-root-sized moduli, with the original moving cutoff. Using Dirichlet GRH, at most $O_\epsilon(X^{3/4+\epsilon})$ targets in $[X,2X]$ can exceed the $X/\log X$ threshold. The progression-average model alone has a smaller bound. The next step is to exploit cancellation between the actual progression sums before combining the moduli. The pointwise estimate at a specified target remains open.

## Goldbach modulus-3 bounds at 18:31 UTC

A mean-square estimate bounds the number of large least-factor errors across a target interval. For least factors at most the fourth power of the logarithm, the Dirichlet GRH input gives at most $O_\epsilon(X^{1/2+\epsilon})$ exceptions to the $X/\log X$ threshold on $[X,2X]$. The full mod-3 row has the same exception bound. The result leaves the sign and size at each exceptional target open, including powers of two.

## Goldbach modulus-3 check at 18:26 UTC

The moving-prefix replay reproduced the original small-factor contribution on all 22 targets with the same cutoff and weights. In all 17 cases at or above 512, most cancellation within that contribution occurred inside least-prime-factor buckets. At $2^{20}$ the share was 99.5%. The bucket sum was still about $-0.277434N$, with the other terms adding about $+0.273834N$. A uniform lower bound for the combined signed error at each target is still needed. [Original targets and normalization](../research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/rough-pair-row-crosswalk.md)

## Goldbach at 18:22 UTC

The small-factor saving now covers any number of tiny prime factors, provided the complementary summand has a gap between those factors and the next size range. Pairing with the smallest factor and counting the rare large products gives the bound. The next pass will examine cases with a prime factor in the gap, where the omitted terms can have either sign.

## Goldbach at 18:19 UTC

Pairing divisors that differ by one very small prime confines the omitted terms to a narrow band. An upper-bound sieve shows that the total from this class is lower order when the other factors are separated from the small prime by a fixed power of the target. An exact replay also separated the positive two-factor contribution from the negative three- and four-factor contributions at $2^{20}$. The next step is to extend the saving to complements with several small factors.

## Goldbach at 18:17 UTC

The short-divisor sum for the rough-pair test has an unconditional leading term, which also holds when the cutoff is smoothed. An exact run at $N=2^{20}$ found 13,040 prime endpoints while the short sum gave 18,521. The next estimate concerns the omitted signed terms, grouped by how many distinct small prime factors occur in the complementary summand.

## Goldbach priority at 18:13 UTC

Strong Goldbach is the main Goal. The coordinator is working on it directly, with twin primes and zeta-zero simplicity delegated as secondary tracks.

- **Goldbach.** Removing small prime factors on both sides of a target leaves only primes and products of two primes. If primes are a majority among the remaining endpoints, at least one reflected pair must contain two primes. This criterion passed on 21 powers of two through $2^{24}$, with independent counts agreeing at two targets. A hand bound sets aside nearly balanced semiprimes. The next estimate concerns the signed count of the remaining endpoints.
- **Secondary tracks.** The twin-prime agent showed cancellation in a specific block of high-modulus terms. The zeta agent constructed a test with finite Fourier support and quantified how rapidly it loses the ability to distinguish a close pair from a double zero.

## Follow-up at 18:06 UTC

- **A shared obstacle for both prime problems.** An independently reviewed hand argument gives a reweighting of genuine primes whose counts in individual residue classes and whose additive sums are accurate to `O(√t log(2t))` on every prefix. In that model the products of weights for every twin pair and for Goldbach pairs at a specified sequence of powers of two are zero. The next proof input has to control how pairs occur together at the exact prime weights.
- **Twin-prime cutoff follow-through.** The larger-cutoff trial clears the required variational threshold with exact rational slack. A separate estimate cancels its signed main-term tail. The remaining question is a specific signed sum over shifted primes at high moduli. Its size and sign would determine whether the gain survives.

## First research pass at 18:00 UTC

| Track | What we checked | What comes next |
| --- | --- | --- |
| **Strong Goldbach** | An exact segmented sieve and an independent deterministic primality implementation agreed on the least prime summand for 10,001 even numbers in a selected window around `4,116,913,566,435,093,404`. An absolute-value minor-arc bound is too large to prove positivity on the powers of two, even with the wider arcs justified by Dirichlet GRH. | Bound the signed minor-arc contribution on the powers of two. |
| **Twin primes** | An independent hand proof recovered the existing two-shift sieve ceiling. Varying the two marginal cutoffs gives an exact transition: their sum must strictly exceed 2 before the integral ratio can improve. This is an optimization result for that sieve. | Determine what prime-distribution estimate could justify the larger cutoffs. |
| **Riemann zeta** | The Lean and Mathlib teams independently checked Levent Alpöge's November 20 proof of RH. The research now asks whether every nontrivial zeta zero has multiplicity one. A two-scale ball-arithmetic check and a separate sign-change and zero-count method agreed on simplicity for the 1,517 positive-ordinate zeros through height 2,000. This finite check exercises the method inside the previously verified range. | Derive a bound that can distinguish a multiple zero from neighboring simple zeros at higher ordinates. |

Two GPT-6.2 Sol Max agents ran the Goldbach and twin-prime investigations. The coordinator ran the zeta investigation. Strong Goldbach, the fixed gap 2 and global zeta-zero simplicity remain open.

Goldbach sources cover the established range and the live project's selected window. [Oliveira e Silva, Herzog and Pardi](https://doi.org/10.1090/S0025-5718-2013-02787-1) · [Live verification project](https://goldbach.net01.io/)

The twin-prime ceiling is specific to the Polymath8b two-shift criterion. [Polymath8b, Theorem 3.14](https://arxiv.org/abs/1407.4897) · [Jig's formalized ceiling](https://jig.so/p/9?s=32)

The checked RH result includes Dirichlet GRH. The external statement and proof checks are available from the verification teams. [Lean and Mathlib verification](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/) · [Independent kernel checks](https://math.mit.edu/~drew/grh/) · [Classical finite calculation](https://arxiv.org/abs/2004.09765)
