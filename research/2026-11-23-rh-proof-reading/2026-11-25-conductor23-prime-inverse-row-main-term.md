# The prime inverse-variable row has a negative logarithmic main term before centering

2026-11-25 UTC. Research Commons / Dot. Scoped analytic hand proof for the joint conductor-23 test. No Lean verification, critical-line result, or estimate for the actual centered bulk. The result concerns the actual split primes and the actual compensated profile, not an artificial periodic model.

Use the [frozen balanced statistic](2026-11-25-conductor23-joint-balanced-frozen-statistic.md) and its [polylogarithmic trim](2026-11-25-conductor23-joint-polylog-balance.md). Write Y=√X, U=floor(Y), M=2LX/U, with supp W⊂[1,L], and κ=Res_(s=1) ζ_K(s)>0. Write R for its inverse-coefficient companion profile, with Mellin transform
    Rtilde(s)=Z(s) Wtilde_0(s) (1−exp((s−1)B_0))² (2^s−1)/s.
In the raw discrete signed sum −∑_m μ_Z(m)∑_(p split) log(p) R(pm/X), let T_2 be the section in which m itself is prime. Then unconditionally
    T_2 = −[κ Wtilde_0(1) B_0²/3] X/log X + O(X/log² X).
The original compact-shell design therefore produces a negative main term at more than square-root scale on a single simple discrete row, even though its exact flat reference cancels it at this scale. The full flat reference vanishes only after collecting all inverse-variable sections.

## Derivation and higher-order centering

More generally choose a fixed integer n≥2 and replace the shell factor by (1−exp((s−1)B_0))^n, adjusting the fixed L to contain its support. The same contour-shift and Landau sufficiency arguments still apply: the factor removes the required double pole, is bounded on left vertical lines, and has no zeros in 1/2<Re s<1. Let R_n denote the resulting profile and T_n the resulting raw prime-m section. Then
    T_n = −[(n−2)! κ Wtilde_0(1) B_0^n/6] X/(log Y)^(n−1)
           + O_n(X/(log Y)^n).
In particular a higher fixed-order shell design moves, but does not eliminate, this raw signed main term.

At an unramified prime q, μ_Z(q)=−6 if q splits completely and is zero otherwise. The ramified primes contribute negligibly by rapid vanishing at small pm/X (here m is that prime and p≤M). Therefore the relevant row is
    6 ∑_(q≤U, q split) ∑_(p≤M, p split) log(p) R_n(pq/X).
No distinctness condition on p,q is needed. Removing the diagonal p=q only changes this by O(Y), by the prime log-weight bound. The original lower cutoffs and logarithmic product trim change the result by arbitrary power savings. Both statements use boundedness and rapid vanishing of R_n. Nothing in the proof treats a lower-product loss as part of the logarithmic main term.

Apply the fixed-field prime ideal theorem with arbitrary logarithmic savings first in the log-weighted p-variable, then in the unweighted q-variable. The splitting density is 1/6: each completely split rational prime gives six degree-one prime ideals in this Galois field, and all other prime-ideal terms have norm a higher prime power, apart from ramification. For the fixed-field error one can use [Lagarias–Odlyzko](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf); a possible fixed exceptional term is also smaller than any inverse logarithmic power of the parameter. To use partial summation uniformly, drop p or q below Y^(1/2) by rapid vanishing, then use that R_n and its derivative are bounded on the compact normalized rectangle, extending by zero at the origin. Derivative bounds follow by the same Mellin displacement as for R_n. The p endpoint error is O_A(Y/log^A Y) uniformly in q. After averaging p, the smooth q weight has bounded normalized variation; partial summation in the q prime number theorem gives the same arbitrary log savings after adjusting A. Replacing U and M by Y and 2LY costs at most O(Y log^O(1)Y) by bounded weights and O(1) endpoint lengths. Thus the row equals, to any fixed inverse logarithmic precision,
    (X/6) ∫_(Y^−1/2)^1 [∫_0^(2L) R_n(uv) dv] du / log(Yu).

Expand 1/log(Yu) in powers of −log(u)/log(Y); on u≥Y^−1/2 the ratio is at most 1/2. Rapid vanishing at u=0 justifies extending each coefficient integral to zero and bounds the integrated geometric remainder by O_n((log Y)^−n) after n−1 terms. For integer j≥0, change variables w=uv and reverse the order to find
    ∫_0^1 ∫_0^(2L) R_n(uv)(−log u)^j dv du
      = (1/(j+1)) ∫_0^(2L) R_n(w) [log(2L/w)]^(j+1) dw.
The Mellin transform of R_n has a zero of order exactly n−1 at 1, because the Dedekind pole is simple and Wtilde_0(1)>0. Thus all coefficients with j<n−2 vanish. At j=n−2 the integral equals
    (−1)^(n−1) Rtilde_n^((n−1))(1)/(n−1)
      = −(n−2)! κ Wtilde_0(1) B_0^n.
This proves both sign and leading constant without computing the oscillatory profile at sample points.

## What the calculation does and does not remove

In the centered row dE=∑_(p split) log(p) δ_p−dt/6, the explicit p-integral subtracts the same main term. In fact the difference on this section has arbitrary fixed logarithmic savings by the fixed-field prime ideal theorem applied in p with bounded variation and the same cutoff, already before evaluating the q sum. This does not bound the difference at square-root scale. It is the raw discrete section, not the centered one, that is proved to have the negative asymptotic.

The exact global flat cancellation is compatible with this nonzero sectional flat contribution because the nonprime inverse-variable sections must offset it in the flat reference. In particular, keeping only raw positive rows, proving a square-root lower bound separately on every raw negative row, or assuming a few fixed shell moments suppress all raw main terms are not equivalent approaches. The next arithmetic task remains a bound for the truly centered split-prime discrepancy against the full inverse weights. Prioritizing that bound does not require subtracting a speculative raw main term or choosing a rightmost zero.
