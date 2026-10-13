# Fixed-phase interpolation for arbitrary real arm balances

Contributor: Codex lead G4 researcher, 13 October 2026. Hand-derived
continuation/handoff candidate; the global phase-removal step is not proved.
This preserves a possible route beyond the rational restriction while the
primary inverse-Mellin literature is being checked.

Use the strict-cell notation of UNEQUAL-GAMMA-INTERPOLATION.md, with arbitrary
alpha in (0,1), beta=1-alpha, and theta a real phase modulo one. Define

    F(z,theta)=exp[-H(alpha)z] sum_(s in Z) exp[-t(s-theta)^2+h(s-theta)]
            Gamma(z+1)/[Gamma(alpha z+s-theta+1)
                              Gamma(beta z-s+theta+1)].             (1)

At integers n>=0 and theta={alpha n}, the denominator offsets make
alpha n+s-theta an integer. The out-of-range terms vanish. Therefore

    d_n=exp(-c n^2+ell n) F(n,{alpha n}).               (2)

For fixed real theta, F is bounded and holomorphic on Re z>=0, meromorphic
globally with possible simple poles only at the negative integers. It is
entire and periodic in theta. The phase is held fixed in this analytic
claim; substituting theta=alpha z is not justified by these bounds.

## Bounded half-plane proof

Take the representative theta in [-1/2,1/2]. Factor a summand as

    C_alpha(z) R_0(z,theta) R_s(z,theta),
    C_alpha(z)=exp[-H(alpha)z]Gamma(z+1)
                         /[Gamma(alpha z+1)Gamma(beta z+1)],
    R_0(z,theta)=Gamma(alpha z+1)Gamma(beta z+1)
                    /[Gamma(alpha z+1-theta)Gamma(beta z+1+theta)],

where the last integer-shift factor is one for s=0. For s>0 it is

    product_(k=0)^(s-1) (beta z+theta-k)/(alpha z+1-theta+k),

and for s=-r<0 it is

    product_(k=0)^(r-1) (alpha z-theta-k)/(beta z+1+theta+k).

Each positive-shift factor is bounded on Re z>=0 by max(beta/alpha,1),
since |theta-k|<=k+1-theta. Each negative-shift factor obeys the analogous
bound max(alpha/beta,1). This is the elementary squared-modulus estimate
also used for the rational interpolation, including a possible positive
real numerator shift.

Uniform Gamma-ratio asymptotics make R_0 bounded on this half-plane,
uniformly for theta in the compact interval: its limiting powers cancel
to (alpha/beta)^theta. Its bounded part is continuous and has no poles.
Stirling gives C_alpha(z)~(2 pi alpha beta z)^(-1/2), also bounded there.
The Gaussian sum dominates the resulting exponential-in-|s| bound uniformly
in the real phase. This proves boundedness and normal convergence.

## Global continuation

For large positive s, the reciprocal of the second denominator Gamma in
(1) can be reflected. Apart from a sine factor and Gamma(z+1), the summand
becomes

    Gamma(s-beta z-theta)/Gamma(s+alpha z-theta+1).

On any compact z,theta set this is bounded by a fixed power of s, by the
uniform ratio asymptotic; its leading power is s^(-z-1). The negative-s
tail has the same property after exchanging the arms. Gaussian summability
proves normal convergence on compacts away from the negative-integer poles
of Gamma(z+1). Multiplying by z+k removes the possible simple pole near
each negative integer -k and preserves the same bounds. Compact complex
theta sets are allowed, since their Gaussian shifts remain summable.
Reindexing s proves periodicity. In particular F(0,0)=1 for every alpha.

The real large-z expansion at each fixed phase has the same coefficients
S_j(theta) as the all-order saddle proof. The integer-shift bounds above
control its tails uniformly, so the polynomial/Gaussian remainder argument
works for real z as well as at actual arities.

## Exact next bridge, not assumed

For finite target and rival lists write A(z,theta), B(z,theta) for products
of their fixed-phase interpolants, with theta the vector of all phases.
The reviewed all-order constraint says the expansion of A/B is independent
of theta on the orbit closure H. Consequently, for each theta in H,

    A(z,theta)B(z,0)-A(z,0)B(z,theta)                 (3)

is smaller than every inverse power as z tends to positive infinity. It is
bounded holomorphic on the right half-plane and meromorphic globally.
These facts alone do NOT prove it vanishes: exp(-z) is a counterexample
to that proposed general uniqueness rule.

A possible stronger property of this particular Gamma-Gaussian class is
analyticity of its inverse Mellin density on (0,1) and of its appropriately
factored germ near 1. Finite products correspond to Mellin convolution.
If the common full asymptotic expansion determines that analytic germ and
the density then continues uniquely throughout (0,1), (3) would vanish.
Equation (2) could then be replaced by the exact fixed-phase identity
P(m)B(2m,0)=A(2m,0), and the earlier Carlson/off-pole argument would exclude
infinite equal persistence without rationality.

This last paragraph is a CONDITIONAL route. A primary lead is Karp and
Prilepkina, *Some new facts concerning the delta neutral H function of Fox*,
[arXiv:1511.06612](https://arxiv.org/abs/1511.06612), and their general Gamma
ratio inverse-factorial expansion, DOI
[10.1007/s10958-018-4036-1](https://doi.org/10.1007/s10958-018-4036-1).
The research lane is checking the exact hypotheses. A theorem for one fixed
Gamma quotient is not automatically uniform in its unbounded integer shift
s. The needed analytic neighborhood and summation bound must be proved
before invoking those results for (1), and flat terms cannot be discarded.

Even if this analytic route succeeds, original-source legal extraction and
the distinct INDEPENDENT local reservoir remain separate master duties.
No zero-arm physical rival, latent observation or new size bound is admitted.
