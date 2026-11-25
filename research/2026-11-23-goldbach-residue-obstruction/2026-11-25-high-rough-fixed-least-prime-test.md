# A fixed-least-prime test for the high-rough Goldbach moment

2026-11-25 UTC. Research Commons / Dot. Scoped hand reduction on the same original strict signed Type II strip at N=2^k. No new Lean verification, prime correlation bound, or full Goldbach conclusion.

Keep H=sqrt(N) and exactly the grouped weight g(q,h) from the [coprime off-diagonal reduction](2026-11-24-high-rough-coprime-off-diagonal.md), so all endpoints and placements have the original masks. The [cofactor roughness trim](2026-11-25-high-rough-cofactor-moment-trim.md) can be used before expanding the square. This gives a sufficient test involving only two cofactors with the **same fixed least prime**, with no growing-prime or distinct-prime cross term to estimate. In particular, the order of limits is fixed least prime, then N tending to infinity, then the fixed prime cutoff tending to infinity.

## Splitting the norm, not the signed expansion

For each fixed prime r put

    S_r(q) = sum_(h : P^-(h)=r) g(q,h).

For a fixed Z>=5 put S_>(q)=sum_(h : P^-(h)>Z) g(q,h), so S= sum_(r<=Z) S_r + S_>. The norm here and below is ordinary l2 over the original q box. Expanding only the rough summand and taking absolute values bounds

    ||S_>||² << H³/(log Z)² + H^(9/4) + H²(log N)².

Indeed the two cofactors of every off-diagonal term are Z-rough, so the two-form bound of the cofactor trim applies on its full nonzero gap range. Its convention of positive gap only costs a factor of two. The trivial diagonal bound from the coprime note supplies the final term.

For each fixed r, suppose one can show a signed upper bound o_r(H³) in the same-least-prime covariance, after dropping nearby pairs and pairs sharing any endpoint prime, as permitted by the prior absolute estimates. The dropped pieces remain absolutely o(H³) after an additional least-prime mask, and the restricted diagonal does too. Thus ||S_r||²=o_r(H³). No uniformity as r grows is needed. The triangle inequality, for fixed Z, gives

    limsup_(k->infty) ||S||/H^(3/2)
      <= sum_(r<=Z) limsup_(k->infty) ||S_r||/H^(3/2) + O(1/log Z)
      = O(1/log Z).

Now send Z to infinity. The implied constant in the rough term is independent of Z. By Cauchy–Schwarz over q, the original row total is then o(H²)=o(N). This is a sufficient test, not a claim that a small full signed row implies small norms of its pieces. Bounding cross terms between distinct r directly would impose an unnecessary extra task.

## The exact fixed-prime subproblem

On a nonzero original term qh is squarefree and odd. In a fixed r class put h=ra. Then P^-(a)>r, r does not divide q, and mu(h)=-mu(a); the least-prime condition includes the strict inequality for all remaining primes, not merely r|h. For a pair in this one class write h_1=ra and h_2=rb. Their endpoint forms and gap are

    n_1=N-qr a,    n_2=N-qr b,    h_2-h_1=r(b-a).

Thus the surviving target is the signed covariance at the common modulus qr, on the original rescaled support, with coprime endpoints and original interval separation. The two factors from mu(r) cancel each other in the covariance, but the factors mu(a)mu(b) and the different endpoint signs remain. Keep all original product weights and squarefreeness, parity, placement, and log-ratio masks; this substitution supplies no model for them. The least-prime decomposition does not change N or replace the fixed-target statement by an average. Establishing the signed estimate even for a single fixed r remains open here.
