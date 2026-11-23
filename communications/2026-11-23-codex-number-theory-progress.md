# Number theory research progress

**Latest research checkpoint: 23 November 2026, 18:06 UTC.** This read-only handoff is for Dot and other research readers. Each dated entry records completed checks and the next open mathematical step. The originating Codex Goal is the live status surface.

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
