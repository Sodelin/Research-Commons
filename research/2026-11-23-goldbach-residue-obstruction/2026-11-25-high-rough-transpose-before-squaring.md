# Goldbach high-rough row: transpose before squaring

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof using classical Möbius estimates. No new Lean verification or signed estimate for the true endpoint profile.

Write N=2^k, H=sqrt(N), I=(H/2,H]. For a real product profile P, set

    v_P(q,h)=1_(q odd squarefree) 1_((h,2q)=1) μ(h) log(h/q) P(qh),  q,h in I,
    T_P(q)=∑_(h in I) v_P(q,h).

Exact ordered transposition in the [additive model note](2026-11-25-high-rough-additive-model-null.md) shows that ∑_q T_P(q) is twice the one-representative sum with q<h and μ(qh)=-1. This holds both for P=C_N, the full actual signed product profile (including all endpoint tests), and for a model P. It does not identify their moments taken before summing over q.

## Transpose-first covariance is unchanged by a low divisor model

For each A,K there is B such that P of the form in the [sieve-model note](2026-11-25-high-rough-sieve-model-null.md), with coefficient variation norm at most log^K H and D≤sqrt(H)/log^B H, satisfies

    ∑_q sup_(subinterval J⊂I) |∑_(h in J) v_P(q,h)| ≪_(A,K) H²/log^A H,
    ∑_q |T_P(q)|² ≪_(A,K) H³/log^A H.

The earlier proof bounds each q contribution in absolute value before summing q. It applies with a separate choice of J for each q: the small-e Abel summation uses the same maximum over prefixes at both ends of J, and the large-e CRT error and interval length are bounded by their full-I counterparts. This proves the first bound. Pointwise, count h in one reduced class modulo each d (or no h if (d,q)>1), to obtain

    |T_P(q)| ≪ log^K H ∑_(d≤D)(H/d+1) ≪ H log^(K+1) H.

The second bound follows with a larger input A. For additive models in the earlier note, the identical two conclusions follow if the total norm is polylogarithmic; the earlier fixed-q Davenport estimate is already uniform over interval endpoints.

For the actual P=C_N, the single-root endpoint sieve keeps its absolute envelope |T_C(q)|≪H(q/φ(q))²: odd q and squarefree h are enforced by v_C, and dropping the removed μ(qh) parity mask only increases the absolute majorant. Its fourth Euler-product moment is bounded on average, as in the [mask transfer](2026-11-25-high-rough-first-to-second-mask-transfer.md). Hence ∑_q |T_C(q)|²≪H³. Cauchy–Schwarz with a doubled log exponent gives, for the same sufficiently restricted D,

    ∑_q |T_C(q)−T_P(q)|² = ∑_q |T_C(q)|² + O_(A,K)(H³/log^A H).

This statement concerns the full row square, not a comparison for an arbitrary pair-masked cross term. For the actual v_C alone, the earlier diagonal, short-gap and shared-endpoint-prime absolute estimates still apply on the full ordered box: their proof uses only |v_C|≪log H and least prime >N^(1/10), not which of q,h is smaller. Thus one can estimate this genuine coprime separated covariance without the original outside sign projector, while retaining exactly the same target first moment.

## Squaring in the original orientation need not kill even a constant model

Take the synthetic comparison profile P=1 (not the actual endpoint profile). On q<h write the original model row as

    R(q) = (1/2)∑_(h∈I,h>q,(h,2q)=1) [μ(h)−μ(q) μ(h)²] log(h/q)

when q is odd squarefree, and zero otherwise. The formula is exact by inserting the μ(qh)=-1 projector. Then ∑_q |R(q)|² ≍ H³ despite its negligible signed total.

Indeed consider q∈(H/2,3H/5] odd squarefree with q/φ(q)≤M, M an absolute constant chosen large enough. There are ≫H such q: odd squarefree integers have positive density by the μ² square-divisor expansion and the count with q/φ(q)>M is O(H/M) by the bounded divisor mean. For every such q the squarefree h coprime to 2q in (4H/5,H] number ≫H uniformly. Explicitly, the count on an interval of length L in [1,H] is

    L φ(2q)/(2q) ∏_(p∤2q)(1−p^(-2)) + O(√H τ(2q)).

Expand μ(h)²=∑_(a²|h) μ(a), keep (a,2q)=1, count multiples in the interval by inclusion-exclusion, then extend the absolutely convergent main term beyond a=√H. Here τ(2q)=H^o(1), and all these h have log(h/q)≥log(4/3). Every other h>q contributes nonnegatively to the unsigned squarefree sum. The μ(h) sum is o(H) uniformly on these q by the fixed-q estimate in the additive model note, including Abel summation for the log ratio. Thus |R(q)|≫H on ≫H rows. The upper bound follows from |R(q)|≪H everywhere.

By contrast the transpose-first row square for P=1 has arbitrary log savings. The example isolates exactly a fixed-q sign that the original orientation may square before it can cancel across q. It does not say the true original row square is large. It shows why an apparent variance bottleneck in that representation is not evidence that the required signed first moment is large.

The surviving actual signed coprime, separated pair estimate for v_C remains open. No Goldbach implication beyond its sufficiency.
