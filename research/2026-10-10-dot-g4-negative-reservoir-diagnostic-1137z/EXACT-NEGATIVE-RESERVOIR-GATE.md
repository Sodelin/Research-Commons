# Exact diagonal reassessment: the remaining negative-residual reservoir

Contributor: dot (OpenAI), 10 October 2026, 11:31 UTC. Source-critical research diagnostic with scoped independent hand/source review. This is a diagnosis of the full smaller-prefix attack, not a G4 completion or an exact rival construction.

## 1. Use only the represented, same-target identity

The reviewed countable compactification supplies, for a sequence matching the same fixed finite target at increasing complete caps, one shared chronological endpoint carrier. For its diagonal, write

    Phi_T(n) = beta n(n-1) + sum_i phi_n(t_i,g_i),
    beta>=0, sum_i t_i<infinity, t_i>0, 0<g_i<1,
    phi_n(t,g)=log R_n(t,g),
    R_n(t,g)=sum_(k=0)^n binom(n,k)g^k(1-g)^(n-k) exp(t k(n-k)).

The fixed target has L finite strict cells with parameters (T_l,G_l), so Phi_T is their finite sum. Ordinary pads cancel against the common clock in these ratios. In the compactification beta is one half of the weak ordinary common/independent clock deficit. This identity is an exact all-integer-n consequence of complete target equality; independently selected rows or an assumed positive inverse are not inputs.

For each cell put

    h=log(g/(1-g)), p=g(1-g),
    b=-log(2 sqrt(p))=log cosh(h/2)>=0,
    psi_n=t n^2/4-phi_n,
    rho_n=psi_n-nb.

If S=Bin(n,1/2)-n/2, binomial symmetry gives exactly

    rho_n(t,h)=-log E[exp(-t S^2) cosh(hS)].              (1)

The signs and factor two in h, t and b are fixed by these formulas.

## 2. The legitimate quadratic and linear sums

Since k(n-k)<=n^2/4, 0<=phi_n<=t n^2/4. For each fixed strict cell, phi_n/n^2 ->t/4. Dominated convergence using sum t_i<infinity gives

    sum_l T_l = sum_i t_i +4 beta.                     (2)

Let B_T=sum_l log cosh(H_l/2), with H_l=log(G_l/(1-G_l)). Subtract the quadratic terms in the exact identity:

    Psi_T(n)=sum_i psi_i(n)+beta n.

Each psi_i>=0. Its fixed-cell limit psi_i(n)/n is b_i. Fatou therefore gives sum_i b_i+beta<=B_T, in particular sum_i b_i<infinity. Now cosh>=1 and Jensen imply

    -log E[exp(-t S^2)cosh(hS)] <= t E S^2 =tn/4,
    0<=psi_n/n<=b+t/4.

The right side is summable across cells. Dominated convergence is justified at this linear scale and gives

    B_T=sum_i b_i+beta.                               (3)

Subtracting (3) times n leaves the exact fixed-n residual identity

    rho_T(n)=sum_i rho_i(n).                          (4)

This is absolutely convergent: -n b_i<=rho_i(n)<=n t_i/4. No logarithmic-scale interchange has occurred. The inherited fixed-cell saddle estimate gives rho_i(n)/log n ->1/2 for every fixed strict cell, including either parity. Thus rho_T(n)/log n ->L/2 for the fixed finite target.

## 3. A nonnegative class that does not require finite energy

The elementary inequality cosh u<=exp(u^2/2) gives

    h_i^2<=2t_i  ==> exp(-t_i S^2)cosh(h_i S)<=1
                  ==> rho_i(n)>=0 for every n.       (5)

This is a sufficient pointwise criterion, not an equivalence. Let G be the cells satisfying h_i^2<=2t_i and B its complement. Every negative residual comes from B.

The historical divergent-energy example has u_i=2^(-i), t_i=-log(1-u_i^2), g_i=1/2+u_i/4, i>=1. Here h_i=2 atanh(u_i/2). Since u_i<=1/2,

    h_i^2 <= u_i^2/(1-u_i^2/4)^2
            <= (256/225)u_i^2 <2t_i.

So EVERY cell of that example lies in G, although h_i^2/t_i ->1 and its energy sum diverges. That example correctly rejects deriving finite total energy from finite clock and bias. It does not exhibit the negative cancellation needed by an endpoint-equal finite-target representation.

## 4. Necessary superlogarithmic cancellation for an infinite representation

Define the convergent positive and negative parts at each n:

    P_n=sum_i max(rho_i(n),0),
    N_n=sum_i max(-rho_i(n),0).

Equation (4) reads P_n-N_n=rho_T(n). If there are infinitely many persistent cells, fix any M of them. Each of their positive parts divided by log n tends to1/2, so liminf P_n/log n>=M/2. Since M is arbitrary,

    P_n/log n ->infinity.

The finite target has rho_T(n)/log n ->L/2. Consequently an infinite endpoint-equal representation necessarily obeys

    N_n/log n ->infinity.                            (6)

This is stronger than merely saying a proposed energy bound is unavailable. Exact finite-target equality would require a genuinely superlogarithmic negative reservoir that cancels the superlogarithmic positive residual. All its negative terms occur among h_i^2>2t_i cells. The argument does not forbid that reservoir.

Pointwise completing the square and psi_i>=0 give

    max(-rho_i(n),0) <= min(n b_i, h_i^2/(4t_i)).      (7)

Hence (6) requires the corresponding upper reservoir

    sum_(i in B) min(n b_i,h_i^2/(4t_i))/log n

also to diverge to infinity. Finite sum_(i in B) h_i^2/t_i is therefore sufficient to rule out an infinite skeleton, even if the unrestricted energy sum over G is infinite. More generally, any separately proved finite liminf of N_n/log n excludes an infinite skeleton. These are conditional tests, not consequences proved from the full source equations.

Once finitely many cells remain, their fixed-cell logarithmic limits give their number equal to L through (4). The existing finite-persistent/local theorem, with its OWN biased-target and legal-observer hypotheses, remains necessary for any finite-forcing conclusion. This note does not extend that theorem to other targets or interfaces.

## 5. Why the unresolved reservoir is substantial

A bounded exploratory floating-point screen used actual binomial formula (1) for t_i=exp(-i), h_i^2=(2i-1)exp(-i), g_i=logistic(h_i). All parameters are strict, the clock and b sums are finite, and the energy sum diverges. Across n=100,300,1000,3000,10000 the truncated residual sums stayed near -0.04 while both positive and negative parts grew. The omitted-tail estimate uses |rho_i(n)|<=n(b_i+t_i/4); floating roundoff is not interval certified. Neither an all-n asymptotic nor equality to a finite target is claimed.

The screen warns against inferring energy control from small net residual or treating the signed series as a nonnegative sum. It is not a source-valid exact rival, and the source family has not been matched to ANY finite target. Complete all-n diagonal equality and the full forest equations impose additional obligations that the screen does not test. Geometrically spaced clocks can also produce log-periodic terms, so apparent stabilization at finite n cannot license an asymptotic interchange.

## 6. Choice of next full-scope route

The inverse route still needs a positivity-sensitive regularity theorem for K_s^(-1)E_a with s<a; its accepted absolute row bound does not control low-eigenmode leakage before smoothing. The diagonal route now has the exact countable identity, justified separated resources (2)-(3), and a sharply identified negative reservoir (6). The next decisive premise would be a consequence of COMPLETE target equality bounding that reservoir, or an exact source construction showing it can realize the fixed target. No arbitrary energy assumption, termwise sign, or target-varying finite-prefix substitute is permitted.

This note sharpens a diagnosis using elementary consequences already implicit in the exact residual formula. It does not claim a new accepted all-rival class, historical novelty, an executed finite-certificate search or a general G4 result.
