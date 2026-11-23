# A threshold check for the asymmetric Goldbach route

**Status:** Elementary sufficient criterion and finite audit, not a new prime-distribution estimate. Neither a solution nor Lean-verified. No claim of priority or VibeMath submission.

[Li and Liu, Theorem (1+1.9) on the Goldbach Conjecture](https://arxiv.org/abs/2606.05224) use the representation N = p + r q with primes p,q, r either 1 or prime, and r ≤ q^β. This is their (1+a) notation with β=a−1. Their reported unconditional exponent β=0.9, and β=0.4 under Elliott–Halberstam, are fixed constants. The project's [Lean exposition](https://subfish-zhou.github.io/goldbach-lean/report/index.html) describes its formalization of the fixed β=0.9 result. Our check does not reverify it.

## The gap is a uniform starting threshold

Suppose that for every sufficiently small real β>0 there is a threshold K(β) beyond which such a representation is guaranteed for every even N. For each β, the explicit window

    K(β) ≤ N < exp(log(2)/β)

contains only successful Goldbach targets: q < N, so r ≤ q^β < 2 and the positive integer r must be 1. If K(β) ≤ A exp(c/β) for constants A>0 and 0≤c<log(2), choose a with c<a<log(2) and take β=a/log(N). For all sufficiently large N this β is in the allowed range, K(β) ≤ A N^(c/a) ≤ N, and q^β < exp(a) < 2. This proves eventual Goldbach under that stronger assumption. It does not settle the finite range. An independent effective threshold and verified coverage below it would still be needed for a complete theorem covering every even N greater than 2.

The criterion is a way to audit a proof strategy, not a prediction that this bound holds. Even a theorem at every fixed positive β would not justify setting β=0 or substituting β(N) without controlling the thresholds or proving coverage by their windows. The published fixed exponents do not give the required sequence of bounds near zero. If the argument guarantees an odd first prime p, the same elementary test replaces log(2) by log(3), since a composite residual is then odd and r ≥ 3.

## Finite diagnostic

The replay uses smallest prime factors, counts prime partners and two-factor partners separately, and uses exact integer comparisons r^b ≤ q^a for each β=a/b. Prime squares count as two factors. Each p determines a unique residual and each semiprime has a unique choice of its smaller factor, so neither category double-counts a single p. Both orderings of a prime-prime pair count when distinct. The comparison β=0.4 is a definition in this finite test; its exhaustive finite evaluation is not an application or test of Elliott–Halberstam.

A finite scan over 7,501 even targets shows the tighter constraint filtering near-misses. At β=0.1, all remaining semiprime partners in this range must in fact have r=2 (3^10 > 16000 > q), so p=2 is forced by parity. Thus the apparent success of the tight filter is mostly a consequence of the small range and this boundary case, not evidence of the asymptotic uniform estimate.

Replay: `python3 -B replay.py | diff -u REPLAY.txt -`. The proof of the threshold implication is the calculation above, not the replay.
