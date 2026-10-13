# Independent primitive review and the compact-uniform parabolic limit

Contributor: Codex fixed-target-negative subagent, 13 October 2026. **Independent hand review plus hand-derived limit theorem.** The same limiting formula was independently obtained by the chronology subagent during this review; neither independent derivation is reattributed as exclusive. The uniform proof below is this lane's contribution. No Lean verification or source simulation.

## Review of the fixed-cell calculation

I re-read the exact inherited [ordered two-merger integral](../../2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/SOURCE-TWO-MERGER-TIME-INTEGRAL.md) and [uniform ratio transport](../../2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/UNIFORM-DIAGONAL-RATIO-TRANSPORT-1244.md), then independently checked [the chronology candidate](../chronology/FIRST-PRIMITIVE-LARGE-ARITY.md).

Reviewed chronology candidate SHA256: `d253234438401aef99750f06d10b6befb0272f67376e08e72a81e6f3b1d68044`.

**Hand verdict: the fixed strict-cell asymptotic, its parity constant, and its finite-word leading-pad rate are correct at their stated scopes.** In particular, with `r=1-g`, `p=gr`, `m=n-2`, `k=m/2+X`, `l=m/2-X`,

    kl J(infinity) = g^2 l/(2k+1) + r^2 k/(2l+1) - p,

and its mean equals

    (1-4p)/2
      +[-2(2g-1) E X -(1-2p)/2]/m + O(m^-2).

The outer factor is `n/8+1/16+O(n^-1)`. Its constant contribution and the constant from the `1/m` term combine to exactly `-1/32`; the other constant is `-(2g-1) mu_e/4`. The mean `mu_e` is the discrete Gaussian mean on the correct parity lattice, not the continuous Gaussian approximation. At a fair coin that mean term vanishes by symmetry and the limit is `-1/32`.

For fixed `t>0,h`, the central-binomial ratio estimate and the Gaussian tail supply all needed dominated moments; the finite-integral tail is exponentially small. The source cocycle and the uniform cell ratio bound give an exponentially smaller downstream finite-word contribution. Hence the claimed eventual sign and `-log|A_n(W)|/(2n) -> a` hold. They do not apply uniformly as the first cell varies toward a boundary.

## New uniform moving-cell statement

Let `s>0`, `u` be real, and define one actual equal-arm cell by

    t_n = s/n,         h_n = u/sqrt(n),
    g_n = exp(h_n)/(1+exp(h_n)).

Use the exact original primitive `A_n=c_n/d_(n-2)` and current-root source convention. Then

    A_n(B(t_n,g_n)) -> F(s,u),                         (1)

where

    F(s,u) = u^2 s^2/[64(s+2)^2]
              - [s-2+(s+2)exp(-s)]/[32(s+2)].         (2)

Convergence is uniform for `(s,u)` in every compact rectangle

    s0 <= s <= S,       |u| <= U,       0<s0<=S<infinity.

No infinite source is admitted by this theorem. Each expression before the limit is the primitive of the displayed single strict cell. The limit is an estimate for moving parameters, not an exact rival construction or an observed auxiliary variable.

## Uniform tilted-binomial control

Put `m=n-2`, `X=k-m/2` and `Y=X/sqrt(n)`. Let `E_0` denote the unbiased `Binomial(m,1/2)` law. The actual no-merger tilted law is exactly

    E_* f(Y) = E_0[f(Y) exp(uY-sY^2)]
                    / E_0[exp(uY-sY^2)].             (3)

For every real `v`,

    E_0 exp(vY) = cosh(v/(2sqrt(n)))^m <= exp(v^2/8).

Thus all moments of `|Y|` times `exp(U|Y|)` are bounded uniformly in `n`, for every fixed `U`. The denominator of (3) is at least `exp(-S/4)` by Jensen, since `E_0 Y=0` and `E_0 Y^2=m/(4n)<=1/4`.

The ordinary central limit theorem gives `Y -> Normal(0,1/4)` under `E_0`. The exponential-moment bound gives uniform integrability for every polynomial times the tilting factor. For varying `(s_n,u_n)` in the compact rectangle, take a convergent parameter subsequence; uniform integrability and the CLT identify its tilted-moment limit. This subsequence argument proves uniform convergence of the first two tilted moments throughout the rectangle. The limiting tilted normal law has

    mu = u/[2(s+2)],
    variance = 1/[2(s+2)].                            (4)

This argument also uniformly bounds every fixed higher tilted moment used in the remainder estimates. The parity lattices merge in this scaling; no fixed-lattice approximation is used.

## Expansion of the exact ordered integral

Write the two scaled merger times as `a=n times first_time` and `b=n times second_time`, so `0<a<b<s`. The inherited cell integrand is

    g_n^2 exp(-(k+1)a/n-kb/n)
      +(1-g_n)^2 exp(-(l+1)a/n-lb/n)
      -p_n exp(-ka/n-lb/n)
      -p_n exp(-la/n-kb/n),                           (5)

where `p_n=g_n(1-g_n)` and

    k=n/2-1+sqrt(n)Y,       l=n/2-1-sqrt(n)Y.

Taylor expansion of (5), retaining its cancellations before estimating, gives

    exp(-(a+b)/2)/n times
      [u^2/4-a/2+Y^2 ab-uY(a+b)/2]
      + R_n(a,b,Y).                                  (6)

Uniformly on the parameter rectangle and on the integration triangle,

    |R_n(a,b,Y)| <= C n^(-3/2)(1+|Y|^3).

To justify the uniform bound, observe that the exact support has `|Y|<=sqrt(n)/2`. Hence every exponential Taylor remainder has uniformly bounded exponential prefactor when `a,b<=S`; the logistic expansion is uniform for `|u|<=U`. The preceding tilted-moment bounds then control its expectation.

The rescaled factor multiplying this integral is

    C_n kl/n^2,       C_n=n(n-1)/[4(2n-3)],
    C_n/n -> 1/8,     kl/n^2=1/4-(1+Y^2)/n+1/n^2.

These are exact algebraic identities except the displayed limit. The zero-routing endpoints cause no difficulty: there `kl=0`, so the actual contribution vanishes; no negative-count state or denominator is introduced.

Combining (3)–(6), the primitive differs by `o(1)`, uniformly, from

    (1/32) integral_(0<a<b<s) exp(-(a+b)/2)
       [u^2/4-a/2
         +ab{1/[2(s+2)]+u^2/[4(s+2)^2]}
         -u^2(a+b)/[4(s+2)]] da db.                 (7)

The direct integral expansion has an `O(n^-1/2)` expectation remainder; only qualitative uniform convergence is asserted for the tilted moments. No unproved Berry–Esseen rate is inserted.

For an independent check of (7), put `q=exp(-s/2)`. The four needed ordered integrals are

    I_1   = 2(1-q)^2,
    I_a   = 2[1-4q+(s+3)q^2],
    I_a+b = 8(1-q)^2+4s(q^2-q),
    I_ab  = 2[(s+2)q-2]^2.

Substitution gives (2). In particular the coefficient of `u^2` simplifies exactly to `s^2/[64(s+2)^2]`; retaining the binomial tilt is necessary for this simplification.

## Strict positivity on the bad-reservoir parabolic sector

The source bad-cell condition `h_n^2>=2t_n` is exactly `u^2>=2s`. Since the coefficient of `u^2` in (2) is positive,

    F(s,u) >= [s^3-s^2+4-(s+2)^2 exp(-s)]
                       /[32(s+2)^2] > 0.            (8)

For the final strict inequality, multiply its numerator by `exp(s)`. The constant, linear and quadratic coefficients of

    exp(s)(s^3-s^2+4)-(s+2)^2

vanish. Its coefficient of `s^j`, for every `j>=3`, is

    [4+j(j-1)(j-3)]/j! > 0.

Thus the whole series is strictly positive for `s>0`. This is an exact sign proof, not a numerical plot.

Consequently, for any fixed nonempty compact parameter set with `s0<=s<=S`, `|u|<=U`, and `u^2>=2s`, there is one `N` such that every displayed actual cell has `A_n>0` for `n>=N`. This is the uniform intermediate-scale statement that follows directly. It does not cover unbounded `nt` or `sqrt(n)|h|`, and by itself does not compare transported positive and negative contributions of an arbitrary countable carrier.

## Executed algebra and remaining scope

SymPy was used once to integrate the four elementary terms in (7), simplify the coefficients, and expand the positive-sector expression near zero. It returned (2) and initial series `s^3/192-s^4/192+s^5/240+...` at `u^2=2s`. This is an algebraic consistency check; the all-s positive proof is the coefficient argument above. No source compiler or genealogy simulation was run, and no check supplies the uniform CLT proof.

The original G4 master remains open. This note supplies a controlled asymptotic in one moving-cell regime and independently checks the fixed-cell calculation. Any application to unrestricted sources still needs the whole-source legal observation bridge, original shared-parameter semantics, and control of all remaining scales and chronological cancellations.
