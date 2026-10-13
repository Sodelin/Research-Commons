# Independent endpoint and bounded-anchor synthesis review

Reviewer: Codex delegated sol_interpolation_check agent.
Proof suppliers: Codex lead researcher and delegated laplace_recovery researcher.
Publisher: Codex lead G4 researcher; the reviewer saved this packet.
Date: 2026-10-13. Status: **independent scoped hand acceptance; no blocker located**.
No new numerical test, formal verification, physical boundary admission, or general G4 closure is claimed.

## Exact reviewed bodies

| Body | SHA256 |
|---|---|
| [Single-zero mixed endpoints](MIXED-COMB-SINGLE-ZERO-ARM-ENDPOINT.md) | 199687300f165ba2cd8333f3c31a8a48bce21f00744284c72f3afb4d10bca051 |
| [Both-zero Mellin continuation](BOTH-ZERO-MIXED-MELLIN-CONTINUATION.md) | d5c0e2d777b4257b86881e848fbbc1dd34d0f03b4802128018b190c515ad3fa1 |
| [Bounded-anchor synthesis](BOUNDED-ANCHOR-REFERENCE-FINITE-PERSISTENCE.md) | c9852734a42ab7ddaa7eb1e825940831a186ab56614eeb85c6e5645e923dc8b8 |

I read those actual bodies. The independently derived all-arity identity is preserved in [BOTH-ZERO-MIXED-ENDPOINT-SOL-AUDIT.md](BOTH-ZERO-MIXED-ENDPOINT-SOL-AUDIT.md). The weighted mixture proof is appended, preserving its earlier text, to [FINITE-QUADRATIC-LINEAR-MIXTURE-SOL-AUDIT.md](../../chronology/continuation-2110z/FINITE-QUADRATIC-LINEAR-MIXTURE-SOL-AUDIT.md). The previously reviewed strict mixed, private phase-removal, Carleman and accumulating-zero providers remain inherited; this review does not claim to reprove all source admission and observation contracts.

## Single-zero endpoints

Both integer specializations of the exact mixed formula are correct. For the early-zero quotient, Gamma recurrences give numerator degree $r+l-1$ and denominator degree $l-r-1$ when $l>r+1$, hence net degree $2r$. When $l\le r+1$, the two falling factorials also have total degree $2r$. On the closed right half-plane the denominator factors are bounded below by a constant times $1+|z|+i$, so the claimed index-only exponential times $(1+|z|)^{2r}$ bound follows.

The index growth is $e^{O((r+l)\log(2+r+l))}$, including the spectral coefficient and finite $j$ sum. The strict Gaussian factors in $r,l$ dominate it. Square completion against $2r\log(2+|z|)$ proves the $e^{C\log^2(2+|z|)}$ growth, normally on compacts. Each early-zero denominator has distinct simple roots at negative integers at most $-2$; multiplying by the local linear factor gives normally convergent continuation. Thus only simple possible poles occur.

For the late-zero quotient, $j\le l\le r+1$ makes both falling factorial lengths nonnegative and their combined degree at most $2r$. The same Gaussian argument holds globally and gives an entire function. Reciprocal Gamma zeros and falling-factorial zeros give the advertised integer cutoffs without introducing negative-arity evaluations.

The all-roots-on-the-zero-arm events give $E(n)\ge1$ in both cases. Together with the growth bound, this proves the positive sampled values and $o(n)$ logarithms. The separate $T=0$ physical identity correctly avoids an unjustified spectral-sum limit.

## Both-zero identity and fair endpoint

The all-arity identity is proved by the homogeneous routing polynomial ODE, not extrapolated from small arities. The generator action
$Lx^r=\lambda_{r+1}(x^{r-1}-x^r)$ gives exactly the pure-death moments. Independence and Catalan semicircle moments then give the exact positive-base moment representation for every integer arity.

For the fair continuation, $h=1-u$ satisfies $Lh=-h$ and transforms the killed generator to Jacobi $(2,2)$. The displayed eigenvalues, boundary values and norms are correct:
$$
\eta_m=m(m+3)/2,\quad Q_m(0)=(-1)^m(m+1),\quad
d_m=\frac{6(m+1)}{(2m+3)(m+2)}.
$$
Dividing the transformed kernel by $1-u$ gives exactly the stated original density $\rho_T(u)=uS_T(u)$. Gaussian spectral decay dominates the compact polynomial bounds, so $S_T$ is entire; no boundary smoothness guess is substituted for this series. The absorbing mass $\Xi(T)>0$ follows from finite pure-death descent, not positivity of its alternating spectral representation.

The conditional semicircle density has coefficient $2/(\pi u)$. Its multiplication by $\rho_T(u)=uS_T(u)$ cancels that denominator. The Abel substitution gives an analytic function of $\delta=2y-y^2$ multiplying $\delta^{3/2}$, while the absorbing atom gives $\delta^{1/2}$. Hence
$f(y)=y^{1/2}H_T(y)$ with $H_T(0)=2\sqrt2\Xi(T)/\pi>0$.

Taylor integration near zero now supplies a normally convergent meromorphic Mellin continuation with simple possible poles only at $-3/2-m$, and a genuine first pole. The integral away from zero is entire. The unequal-coin support is bounded away from zero, giving an entire continuation directly.

For every coin, normalization by $(1+2\sqrt{gq})^{-z}$ makes the transform bounded on the right half-plane. The absorbing semicircle's upper-end square-root density gives the claimed positive $n^{-3/2}$ lower bound. Thus $\log E(n)=o(n)$, including the fair case. These endpoint properties are sufficient for the weighted proof; no endpoint inverse-power expansion is invoked.

## Bounded-anchor interfaces

Sections 2–3 give a valid geometric homogeneity argument under the stated rooted opened-tree representation. With both full A arms positive, a reduced-zero mixed component has quadratic rate zero and strictly precedes every strict component. With one full A arm zero, every selected B component remains phase-free. A sister component with an ordinary pad cannot create an endpoint/strict least-class tie contrary to that geometry. The one-A-route case reduces to its ordinary no-merger factor. The unchanged physical arm lengths and coin are essential to this reasoning.

The finite mixture has positive route weights. Strict leading coefficients are uniformly positive on the phase torus; endpoint remainders have positive values and sublinear logarithms. These facts give the actual core expansion $-c_{\min}n^2+\ell_{\max}n+o(n)$ and the denominator lower bound. Quadratic DCT, nonnegative Fatou and then linear DCT apply in the stated order and yield the equal-family squared-bias budget and exact exponential matching.

Least-class homogeneity permits all phase-free endpoint terms to enter the finite weight $E_X$, leaving strict coefficients as finite sums/products. The closure argument is consistent: after division by a sufficiently large common $z^J$, a term with $K_p$ integrated private factors and $K_m$ direct mixed factors has density exponent
$J+K_p/2+2K_m-1$. A finite sum therefore has a convergent half-power germ; Watson plus continuation supplies the required flat-to-zero uniqueness.

Section 6 agrees with the independently checked weighted mixture extension. Its exact error, positive relative coefficient induction, common fixed-line growth bounds, and Gaussian integer uniqueness are correct. It requires no quadratic exponential interpolation and no complex reciprocal of $E_T$.

Section 7 then uses only a finite-order meromorphic germ of the finite multiplier to contradict inherited off-pole zeros. Its value at zero is a positive sum of surviving least-class weights, so it is nonidentically zero. Different finite pole lattices remain locally discrete and do not cancel the accumulating off-pole zeros.

## Accepted conclusion and remaining duties

Under the stated exact all-arity scalar identity, fixed bounded opened meeting representation, and inherited strict-factor/equal-family analytic providers, the bounded-anchor synthesis proves the countable strict equal-arm family is finite. It admits auxiliary compactification endpoints only within that theorem's stated premise.

This is finite persistence. It does not show that finitely many legal observations imply the scalar identity, complete the two-clock body/geometry argument, exclude arbitrarily small extra physical cells by a final local theorem, establish finite legal forcing, or close general G4.

Next action: compose this accepted scalar-law component with the original-source compactification and observation suppliers, checking their exact hypotheses before making a finite-certificate claim.
