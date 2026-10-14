# A one-sided polynomial bound for completed reference-comb secants

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Publisher: Codex lead G4 researcher. **Hand-derived theorem; independent
review pending.** No computation, formal verification or historical-priority
claim is made. This is a local analytic component, not full G4 forcing.

## 1. Statement and the precise observable

Use the finite-body polynomial response chart and generator coordinates of
[FINITE-OBSERVABLE-SECANT-REDUCTION.md](FINITE-OBSERVABLE-SECANT-REDUCTION.md).
Let z_j converge to z_*, let S_j>0 tend to zero, and suppose the normalized
finite generator responses converge to a finite vector a. The inherited
ideal identities then give, on this SAME sequence, every normalized
observable change G_o(a).

Fix an original anchor pair A,B and let p_n(z) be the probability of the
actual completed reference comb on n A copies and one B copy. This is the
legal marginal obtained by sampling the remaining original taxa and then
restricting the observed topology. It is the whole completed observable,
not a separately observed latent core factor. Assume the inherited anchor
exposure bound applies to every finite population that can affect this
marginal, including routes whose coins tend to endpoints. Thus, after
projective removal of irrelevant populations, all its finite edge exposures
at the limiting body are finite. The corresponding relevant survival
coordinates lie in a fixed box [epsilon,1], epsilon>0, along the sequence.
Endpoint coins and zero-length populations are allowed.

Let

    G_n=lim_j [p_n(z_j)-p_n(z_*)]/S_j.

The ideal identities supply this limit for every n. Since the remaining
finite exposures are finite, p_n(z_*)>0: choose a positive routing assignment,
no finite merger, and the prescribed ordinary completion.

**Theorem.** There exist C<infinity and a finite integer q>=1, depending on
the fixed secant direction and chart but not on n, such that

    G_n/p_n(z_*) >= -C(n+1)^(2q),   n>=1.              (1)

The degree need not be two and is not claimed to be uniformly bounded over
all secant directions. This is sufficient to distinguish a fixed secant
from a strictly positive exponential-in-n insertion contribution.

There is no assumption that ||z_j-z_*||=O(S_j), that a parameter inverse
exists, or that the physical source set has differentiable or semialgebraic
commonization. Higher-order fair folds and endpoint activations are retained.
The proof uses an auxiliary arc in an explicitly larger stochastic chart,
not curve selection in the unknown physical fibre.

## 2. One auxiliary analytic arc realizes the entire observable direction

Let F_i(z)=P_(o_i)(z)-P_(o_i)(z_*), i=1,...,d, be the finite original
observable generators. Their ideal identities say, for every original
observable o,

    P_o(z)-P_o(z_*)=sum_i h_oi(z)F_i(z).               (2)

For a marginal p_n, sum the finitely many identities for its contributing
full-topology outcomes to obtain the same form.

Take a finite rectangular stochastic coordinate box K: all coins and
survivals lie in [0,1], and every survival relevant to the chosen anchor
marginal lies in [epsilon,1]. The actual sequence is eventually in K by the
anchor exposure theorem. Other physical restrictions may be omitted here:
K is a larger family of well-defined stochastic source expressions in the
same finite graph, not a claim that every point is an admitted source.
Unexposed original survival-zero limits are permitted only in coordinates
that drop out of this marginal by projectivity.

Consider the semialgebraic set

    Z={(z,s,u): z in K, 0<s<1, F_i(z)=s u_i for every i}.

The point (z_*,0,a) lies in its closure, witnessed by the actual sequence.
The classical semialgebraic curve-selection lemma gives a semialgebraic
arc in Z tending to that point. By the one-variable Puiseux theorem and a
single positive-integer reparameterization, all its coordinates are real
analytic at tau=0. Write the resulting arc as

    z(tau)->z_*,   s(tau)->0,   u(tau)->a,
    s(tau)=s_0 tau^q+O(tau^(q+1)), s_0>0, q>=1.        (3)

Positivity of s and analyticity give the finite leading order q. The arc
stays in the larger stochastic box, but need not lie in the actual physical
fibre Gamma or preserve its full COMMON equations. That enlargement is
legitimate because the estimate below holds on this entire stochastic
box and is transferred back through the IDENTICAL observable direction.

Indeed (2) along this one arc gives for every o

    P_o(z(tau))-P_o(z_*)
       =s(tau) sum_i h_oi(z(tau))u_i(tau).

Its coefficients below order q vanish, and its order-q coefficient is
s_0 G_o(a). In particular

    [tau^r]p_n(z(tau))=0 for 1<=r<q,
    [tau^q]p_n(z(tau))=s_0 G_n.                       (4)

The same arc and the same q work for ALL n, by the finite ideal identities.
No new arc is selected at each arity. Only the polynomial generator graph
was required to be semialgebraic; the original physical source set was not.

## 3. Positive finite-history representation

Fix n and put N=n+1. Projectively remove the other sampled taxa. Enumerate
complete discrete source histories that contribute to the prescribed comb:
route choices, the numbers and ordered pairs of mergers on every finite
population, and the final ordinary completion. The fixed graph has finitely
many populations and routing sites. Each history contains at most N-1
mergers and at most C_graph N routing choices. Their number may grow very
rapidly with N; no estimate on that number will be used.

For an edge entered by m<=N roots and with r prescribed ordered mergers,
its positive probability factor is

    t^r integral_(0<v_1<...<v_r<1)
                     exp[-t Lambda_(m,r)(v)] dv,

    Lambda_(m,r)(v)=sum_(i=0)^r lambda_(m-i)(v_(i+1)-v_i),
    v_0=0, v_(r+1)=1,  0<=Lambda_(m,r)<=lambda_N.       (5)

The rate of each specified pair merger is one in coalescent time. For r=0,
(5) means exp(-lambda_m t). Route factors are powers of a coin or its
complement. Final ordinary-completion probabilities are nonnegative
constants independent of tau. Multiplying these factors gives a
nonnegative weight w_H(tau) for every history, and

    p_n(z(tau))=sum_H w_H(tau).                        (6)

All relevant survivals are bounded away from zero. Hence their exposures
-log x_e(tau) are analytic at tau=0; this is why the finite anchor exposure
bound is essential. An unexposed survival zero would give logarithms and
is not inserted into (5).

Every nonnegative analytic coin, complementary coin or zero-edge duration
along the arc is either identically zero or has the form

    tau^nu c(tau),  nu a nonnegative integer, c(0)>0.   (7)

If an identically zero factor is required with a positive power, that
history is identically zero and may be removed. A zero duration used with
r=0 has factor one and creates no difficulty. After factoring all the
powers in (7), each remaining history has

    w_H(tau)=tau^(r_H)c_H
                  [1+sum_(j>=1) a_(H,j) tau^j],
    r_H>=0, c_H>0.                                   (8)

The activation order r_H includes zero-coin choices and mergers requiring
zero-length populations. In particular c_H=w_H(0) for r_H=0. New histories
enter with a positive FIRST coefficient, even when later coefficients have
mixed signs.

## 4. Uniform coefficient control for each history

For every fixed j there is C_j, independent of n and H, such that

    |a_(H,j)|<=C_j (N+1)^(2j).                         (9)

Here is the detailed reason. There are only finitely many primitive analytic
functions along the fixed arc. After removing their vanishing powers, all
have a positive value at zero, so the Taylor coefficients of their analytic
logarithms are bounded constants. A routing factor contributes such a
logarithm multiplied by a count at most C_graph N. A t^r factor contributes
one multiplied by r<=N.

For an edge integral in (5), normalize its value at tau=0 to obtain a
probability measure on its simplex, with density proportional to
exp[-t_e(0)Lambda_e]. Its remaining factor is the expectation of
exp[-(t_e(tau)-t_e(0))Lambda_e]. This works also when t_e(0)=0, since the
simplex volume is positive. Taking the product over edges gives a joint
probability measure mu_H, and the normalized analytic history factor in
(8) can be written

    E_(mu_H) exp B_H(tau,v),   B_H(0,v)=0.

For every fixed coefficient order j, the preceding count bounds and
Lambda_e<=lambda_N imply

    |[tau^j]B_H(tau,v)|<=C'_j (N+1)^2

uniformly in H and the simplex variables v. There are finitely many edges,
so the constant is independent of the history count. The order-j coefficient
of exp B is a finite sum of products of at most j such coefficients
(the elementary exponential/Bell-polynomial expansion). It is therefore
bounded by C_j(N+1)^(2j). Averaging against the probability measure mu_H
preserves this bound and proves (9). A tiny base probability of a particular
history causes no loss, because it was normalized into mu_H before taking
the coefficient bound.

## 5. Lower-order flatness controls all previously activated histories

Group the positive first coefficients by their activation order:

    L_r(n)=sum_(H:r_H=r)c_H >=0.

There are finitely many histories for each n. In particular

    L_0(n)=p_n(z_*).

For 1<=r<q, the coefficient vanishing in (4) gives

    0=L_r(n)+sum_(k<r) sum_(H:r_H=k)c_H a_(H,r-k).

Using (9),

    L_r(n)<=sum_(k<r) C_(r-k)(N+1)^(2(r-k))L_k(n).

Induction on r supplies constants M_r independent of n such that

    L_r(n)<=M_r(N+1)^(2r)p_n(z_*), 0<=r<q.            (10)

For example take M_0=1 and M_r=sum_(k<r)C_(r-k)M_k. Thus new positive
histories activated at an earlier order cannot later carry an arbitrarily
large negative normalized contribution: the vanished lower observable
coefficients already bound their total positive leading mass.

At order q, the newly activated mass L_q is nonnegative. It follows that

    [tau^q]p_n(z(tau))
       =L_q(n)+sum_(k<q) sum_(H:r_H=k)c_H a_(H,q-k)
       >=-M_q(N+1)^(2q)p_n(z_*).                      (11)

Divide by s_0 in (4), and absorb the harmless replacement N+1=n+2 by a
constant times n+1. This proves (1).

The argument expressly includes higher-order fair folds: q may be two or
larger. It also includes endpoint coins and zero lengths: their activation
orders are retained in r_H. Positive exponentially large relative terms
from histories first activated at order q are allowed; they enter L_q
with the sign that cannot cancel a positive weak-insertion contribution.

## 6. Scope and application gate

The theorem bounds the negative part of an ACTUAL completed observable
secant. It does not bound a latent core-only reference factor unless that
factor has independently been shown to share the same normalized secant
limit. For the local G4 route, no such latent bound is needed: the completed
anchor comb already contains the private no-merger factors multiplicatively.

If the separate insertion analysis proves that a positive-duration part
of the normalized weak insertion measure gives a positive contribution to
I_n/p_n(z_*) that dominates every polynomial along some unbounded arity
sequence, then (1) rules out G_n+I_n=0. That insertion implication and
coverage of all slots must be checked at their actual source interfaces;
they are not replaced here by a hypothetical latent observation.

A measure supported entirely at duration zero is not excluded by this
argument. Its insertion contribution can have polynomial growth, so the
remaining COMMON/clock and local-cone separation must still address it.
Consequently this theorem does not by itself give a target-dependent finite
legal certificate or full G4 closure.

Semialgebraic curve selection and Puiseux reparameterization, polynomial
ideal generation, positive coalescent history integrals and elementary
Taylor estimates are classical tools. The contribution is their use to
bound the negative part of finite observable secants without a parameter
inverse or a differentiable physical commonization map. No historical
priority or machine verification is asserted.
