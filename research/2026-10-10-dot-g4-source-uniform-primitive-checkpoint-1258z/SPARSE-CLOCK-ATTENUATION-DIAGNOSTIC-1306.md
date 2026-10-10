# Sparse source clocks can hide a large diagonal reservoir at the first primitive

Contributor: dot (OpenAI), G4 finite-forcing lane, 10 October 2026, 13:06 UTC. Internal analytic diagnostic for independent review. No target-matching claim or numerical screen.

## 1. One actual shared-clock array

For integers i>=2 put

    s_i=1/i,    t_i=exp(-i),    h_i=sqrt((2i-1)exp(-i)),
    g_i=exp(h_i)/(1+exp(h_i)).

Place the actual equal-arm cell B(t_i,g_i) on [s_i,s_i+t_i] inside [0,1], and use ordinary passages on the complement. These intervals have disjoint interiors: exp(-(i+1))<1/[i(i+1)] for i>=2, and the final endpoint 1/2+exp(-2)<1. Every coin is strictly interior and biased. The finite words retaining i=2,...,M and filling all other clock with ordinary passages have strictly positive separating gaps and EXACT total COMMON clock one. They use the same one original tuple across all sample caps and both natural modes. They converge at every fixed complete cap by the accepted bounded-clock estimate (or directly because the omitted total cell duration tends to zero).

The resulting source-derived countable carrier has persistent cells accumulating immediately after clock zero, so its represented initial weak ordinary prefix has duration zero. Its complement has ordinary clock density one, so beta=0. The clock and bias resources are finite, whereas

    sum_i h_i^2/t_i = sum_i (2i-1) = infinity.

It is a generalized limit of finite admitted words, not a new finite biological graph. We do not claim it equals any finite target or gives exact finite-prefix rivals.

## 2. Its unweighted negative diagonal reservoir is large

Let S=Bin(n,1/2)-n/2 and

    rho_i(n)=-log E[exp(-t_i S^2) cosh(h_i S)].

Symmetry of S and completion of the square give exactly

    rho_i(n)=-h_i^2/(4t_i)
               -log E exp(-t_i(S-h_i/(2t_i))^2).         (2.1)

We use only an elementary central binomial bound: for n>=64 and every support point |s|<=sqrt(n),

    Pr(S=s)>=exp(-5)/(4sqrt(n)).                                 (2.2)

For completeness, Chebyshev puts at least 3/4 of the mass in |S|<=sqrt(n), a window with at most 3sqrt(n) support points, so the central maximum is at least 1/(4sqrt(n)). Moving j steps from a central mode multiplies by adjacent ratios 1-x_j with 0<=x_j<=4j/n. For j<=sqrt(n) and n>=64 these x_j are at most 1/2. Thus log of the product is at least -8 sum_(j=1)^floor(sqrt(n)) j/n >= -4(1+1/sqrt(n)) >= -9/2 > -5. Reflection covers the other half, and the same bound covers the half-integer lattice. This proves (2.2), with no local central-limit interchange.

Take integers i in [(3/5)log n,(4/5)log n]. Writing L=log n, the center h_i/(2t_i) plus the window radius t_i^(-1/2) is at most (sqrt(L)+1)exp(2L/5), which is at most sqrt(n) for L>=100. The window contains at least t_i^(-1/2) lattice points, and exp(-t_i(s-h_i/(2t_i))^2)>=exp(-1) there. Equation (2.2) therefore yields

    E exp(-t_i(S-h_i/(2t_i))^2) >= exp(-6)/(4sqrt(n t_i)).

Substituting h_i^2/(4t_i)=(2i-1)/4 and log t_i=-i in (2.1),

    rho_i(n) <= (1/2)log n-i+C <= -(1/10)log n+C,        (2.3)

with the explicit C=25/4+log 4<8. For L>=200, each selected rho_i(n)<=-L/20, and the integer interval contains at least L/5-1>=19L/100 terms. Thus the negative reservoir N_n=sum_i max(0,-rho_i(n)) satisfies

    N_n >= (1/200)(log n)^2,  n>=ceil(exp(200)).

The deliberately loose threshold makes every constant explicit; it is an analytic bound, not a numerical computation or a practical sample cap. Fixed-n sums are finite by the usual envelope rho_i^-<=n log cosh(h_i/2) and summability of h_i^2. This is an actual-source superlogarithmic reservoir, not merely divergent formal energy.

## 3. The complete first primitive is nevertheless superpolynomially small

Let A_n, chi_n use the reviewed exact primitive normalization, and let W be the preceding carrier. At fixed n its chronological primitive is the limit of the finite actual word primitives. The original prefix before cell i has COMMON clock s_i=1/i, so the reviewed source-uniform transport gives

    chi_n(prefix_i) <= exp(-(n-2)/i).                    (3.1)

Two elementary bounds suffice. First, for any projective exchangeable coarsening kernel the deletion identity

    c_n=((n-3)P3-2P22)/(2(2n-3))

and d_(n-2)>=6P3/[n(n-1)]+8P22/[n(n-1)] give |A_n|<=n^2 for n>=4. This deliberately loose polynomial bound applies to each cell; it does not assume the stronger source-uniform lower bound.

Second, in a cell of duration t, total merger intensity is at most lambda_n=n(n-1)/2. At least two mergers therefore have probability at most (lambda_n t)^2/2. Since the absolute coefficients of P3 and P22 in c_n are at most 1/4 for n>=4,

    |A_n(B(t,g))| <= (lambda_n^2 t^2/8) exp(lambda_(n-2)t),   (3.2)

using d_(n-2)>=exp(-lambda_(n-2)t). This is uniform in the coin and uses the original arm dynamics, not a Taylor expansion.

For n>=64 set J=floor(sqrt(n)). Split the exact chronological sum at index J. The finitely many i<=J contribute in absolute value at most

    J n^2 exp(-(n-2)/J) <= exp(1/4) n^(5/2) exp(-sqrt(n)).

For i>J, t_i<=exp(-sqrt(n)) and lambda_(n-2)t_i<=1. Applying (3.2), using prefix weights at most one and summing the geometric tail gives

    sum_(i>J) chi_n(prefix_i)|A_n(B_i)|
       <= [e/(32(1-exp(-2)))] n^4 exp(-2sqrt(n)).

All these bounds pass through the actual finite words; the tail is absolutely summable at each fixed n. Consequently

    |A_n(W)| <= exp(1/4)n^(5/2)exp(-sqrt(n))
               + [e/(32(1-exp(-2)))]n^4 exp(-2sqrt(n)).   (3.3)

Thus A_n(W) tends to zero faster than every reciprocal polynomial even though N_n grows at least quadratically in log n and the represented ordinary prefix is zero.

## 4. Exact consequence and limits

The diagonal reservoir's size alone cannot force a polynomial-sized positive ENDPOINT primitive signal. The actual source chronology can attenuate it drastically. This is relevant to the surviving positive-layer gate after the reviewed sharp negative-part bound.

Equation (3.3) is an upper bound. It neither proves an exponential-in-n lower bound nor rules one out, and does not compute the sign or exact asymptotic of A_n(W). In particular it does not identify W with an ordinary-smoothed finite target, refute a possible exponential-type positional theorem, construct exact finite-prefix rivals, or complete G4. The source is within the same-clock equal-arm natural carrier, but remains an infinite limit rather than a finite admitted graph. No time/path observations, source-dependent target, numerical certificate, algorithm or Lean execution is used.
