# Resource normalization with finitely many unequal factors

Author: Codex lead G4 researcher, 13 October 2026. Hand-proof candidate for
review; no computation or formal verification is substituted for the limits.

## Statement

Suppose for every integer n>=0 there is an exact scalar identity

    exp(-A_T lambda_n) product_(l finite) d_n(a_l,b_l,g_l)
      = exp(-A_R lambda_n) product_(k finite) d_n(a'_k,b'_k,g'_k)
                            product_i d_n(t_i,t_i,g_i),           (1)

where lambda_n=n(n-1)/2, all listed arms are positive, all coins interior,
A_T,A_R are finite real constants, and sum_i t_i<infinity. The countable
product is well defined since exp(-lambda_n t_i)<=d_n(t_i,t_i,g_i)<=1.
The ordinary constants are algebraic bookkeeping; this statement does not
admit negative physical durations or use a new observation.

Then sum_i h_i^2<infinity, where h_i=logit(g_i), and the quadratic and linear
normalizations of all factors match. If every factor in the two finite lists
has rational balance b/(a+b), the countable family is finite by the companion
[Gamma interpolation theorem](UNEQUAL-GAMMA-INTERPOLATION.md).

The first conclusion allows arbitrary real balances. Rationality enters only
the continuation step, and must hold on both finite lists, not just a target.

## Proof

For an equal-arm factor use the inherited quantities

    phi_i(n)=log[exp(lambda_n t_i)d_n(t_i,t_i,g_i)],
    psi_i(n)=t_i n^2/4-phi_i(n),
    b_i=log cosh(h_i/2).

The established scalar bounds and limits are

    0<=phi_i(n)<=t_i n^2/4,  phi_i(n)/n^2 -> t_i/4,
    0<=psi_i(n)/n<=b_i+t_i/4,  psi_i(n)/n -> b_i.        (2)

For each fixed arbitrary unequal factor, the notation of the companion
construction gives the real-arity asymptotic

    log d_n(a,b,g)=-c n^2+ell n-(1/2)log n+O(1).       (3)

This holds without rationality. For clarity, write u=j-alpha n after
completing the square. The factor left after exp(-c n^2+ell n) is

    sum_j exp(-t u^2+h u) binom(n,j) exp[-n H(alpha)].

Stirling on a fixed central interval and entropy concavity bound its central
part above by C n^(-1/2) sum_u exp[-t u^2+(h+H'(alpha))u]. The remaining
tails have |u|>=epsilon n and are exponentially small in n^2 even using
binom(n,j)<=2^n. The Gaussian lattice sum is uniformly bounded in its
fractional shift. The nearest integer to alpha n supplies a lower bound
c0 n^(-1/2), with c0>0. This proves (3) uniformly over the integer sequence.

Taking logarithms in (1) and moving the finitely many factors and ordinary
terms to the other side yields

    sum_i phi_i(n)=R(n),
    R(n)=r2 n^2+r1 n+O(log n).                         (4)

Dominated convergence using the first bound in (2) gives
r2=sum_i t_i/4. Subtract this quadratic term to get

    sum_i psi_i(n)=-r1 n+O(log n).                     (5)

All summands on the left are nonnegative. Fatou and their pointwise linear
limits give sum_i b_i<=-r1<infinity. The second bound in (2) is now summable,
so dominated convergence, this time at the linear scale, gives
sum_i b_i=-r1. Since log cosh(h/2) is comparable to h^2 near zero, this also
gives sum_i h_i^2<infinity. No sum h_i^2/t_i is assumed or deduced.

For equal arms the exact normalization is

    d_n(t,t,g)=exp[-t n^2/4+(t/2-b)n] U(n/2;t,h)

at even n. The just-proved quadratic and linear equalities therefore cancel
all exponential prefactors in (1). Choose n=Lm, with L even and divisible
by every rational denominator of the finite factors. Their normalized
remainders are F(Lm/Q); the equal factors are U(Lm/2). Thus (1) becomes
exactly the normalized identity required by the multiplier theorem, which
excludes infinitely many strict equal-arm factors.

## Master boundary

This is a law-level lemma with its displayed factorization premise. It does
not assert that arbitrary legal original-source observations expose (1), or
that compactified unequal factors have rational balance. It proves the
resource budget and normalized identity once that premise is supplied. The
finite COMMON core/palette and the original observation bridge are separate
contracts. The all-real-balance continuation and general G4 master remain
open.
