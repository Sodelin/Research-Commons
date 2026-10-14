# Exact demographic interpolation and the topology-source quotient

Contributor: Codex whole-source lane, 14 October 2026.

Status: primary applicability audit plus a hand-derived exact control. No new
G4 forcing or impossibility theorem. The construction below uses one fixed
constant demographic target and finite strictly positive deterministic rivals,
but its direct source translation has the SAME complete topology law at every
arity. This identifies the failed implication more precisely than an analogy
with approximation or external mixtures. Independent review is pending; no
historical novelty or formal verification is claimed.

## 1. Primary results and previous coverage

Bhaskar–Song, [*Descartes' rule of signs and the identifiability of population
demographic models from genomic variation data*](https://arxiv.org/abs/1309.5056v3),
Annals of Statistics 42 (2014), DOI
[10.1214/14-AOS1264](https://doi.org/10.1214/14-AOS1264), was already audited in
the October 8 [grouped-mixture record, Section 6](../../../2026-10-08-dot-g4-grouped-mixture-attempt-1435z/WHOLE-PROOF-LITERATURE-APPLICABILITY.md)
and our [0622z primary comparison](../../../2026-10-13-codex-g4-lead-finite-forcing-0622z/MASTER-ATTEMPT-AND-PRIOR.md).
The primary PDF was reread here at equations (2)–(4), Theorems 6 and 11,
Corollary 7, and Section 2.6.

Write `lambda_m=binom(m,2)`. For pair rate `1/eta(t)`, define

    tau = R_eta(t) = integral_0^t 1/eta(s) ds,
    eta_tilde(tau) = eta(R_eta^(-1)(tau)).

The expected first-coalescence time in a sample of size m is

    c_m = integral_0^infinity eta_tilde(tau) exp(-lambda_m tau) dtau.   (1)

The expected SFS for a sample of size n is an invertible linear transform of
`(c_2,...,c_n)` before normalization. Normalization retains the vector up to
one common positive factor. Theorem 6 identifies a class of at most K pieces
when `n >= 2K+(2K-1)S(F)`; the piecewise-constant case has `n>=2K`. Both compared
models belong to that bounded class. These are not target-K bounds against
unbounded rival K.

Rosen–Bhaskar–Roch–Song, [*Geometry of the sample frequency spectrum and the
perils of demographic inference*](https://arxiv.org/abs/1712.05035v1), primary
PDF Proposition 2.1 and Theorem 4.3 with its proof, supplies a stronger relevant
positive-realization statement: for each n, the SFS image of arbitrary finite
piecewise-constant demographies is already the image of at most `kappa_n`
epochs, with `ceil(n/2)<=kappa_n<=2n-1`. The result concerns one deterministic
demography, not merely a mixture of demographies. Its positive-cone structure
comes from the linear dependence on epoch heights when breakpoints are fixed
in cumulative coalescent time. The discussion extends this to general
histories; no such extension is needed below.

The query for Myers–Fefferman–Patterson's original paper resolved instead to
Bhaskar–Song, so no direct read of the Myers paper is claimed. Bhaskar–Song
Section 2.6 explicitly describes the increasingly oscillatory, non-finite-epoch
construction. Rather than import that infinite history, Section 2 gives an
elementary finite-epoch construction with the exact fixed-target quantifier.

## 2. An exact finite-epoch rival for each finite SFS prefix

Fix ONCE the target `eta(t)=1` and a window length `H>0`. For each integer
`n>=2`, put `h=H/(n+1)` and define the degree-n polynomial

    P_n(z) = (z-1) product_(m=2)^n (z-exp(-lambda_m h))
           = sum_(j=0)^n a_j z^j.

Let `f_n(tau)=a_j` on `[jh,(j+1)h)` for `0<=j<=n`, and let it be zero for
`tau>=H`. Choose, for example,

    epsilon_n = 1 / [2(1+sum_j |a_j|)],
    eta_tilde_n(tau) = 1 + epsilon_n f_n(tau).

Every population height lies strictly between `1/2` and `3/2`. There are only
finitely many epochs; the final epoch is the constant 1. The elementary exact
Laplace identity is

    integral_0^H f_n(tau) exp(-lambda tau) dtau
      = (1-exp(-lambda h)) P_n(exp(-lambda h)) / lambda,             (2)

for every `lambda>0`. Consequently

    c_m(eta_n) = 1/lambda_m                    for 2<=m<=n,
    c_m(eta_n) != 1/lambda_m                   for every m>n.        (3)

The second assertion follows because all roots of P_n have been listed and
`exp(-lambda_m h)` is a new positive value for every `m>n`. Thus the expected
unnormalized SFS agrees through sample size n and differs at every larger
sample size. The normalized larger-sample SFS also differs: the unchanged
`c_2=1` rules out a nontrivial common scale factor.

The change back to physical time is

    t(tau) = integral_0^tau eta_tilde_n(u) du,
    eta_n(t(tau)) = eta_tilde_n(tau).

This is a strictly increasing piecewise-linear time change. All physical
epoch durations are positive. Moreover,

    integral_0^H f_n(tau) dtau = h P_n(1) = 0,

so `t(H)=H`, and `t(tau)=tau` after H. Both ends of the perturbed physical
window therefore stay fixed. One deterministic positive parameter tuple
defines each rival for every m simultaneously. No boundary population,
external random selector, approximation, or moving target is used.

This is a finite-SFS nonforcing control in the demographic model. It is not
an admitted G4 counterexample.

## 3. Why its direct original-source translation loses all inequivalence

Let `Q_m` be the ordinary Kingman generator on the complete labelled-forest
state space with at most m current opaque roots. On an isolated population
edge with time-varying pair rate `r(t)>0`, the generator is always the same
matrix times a scalar, `r(t) Q_m`. The endpoint forest kernel is therefore

    K_m = exp[Q_m integral r(t) dt].                               (4)

For a finite piecewise-constant history, (4) is also the direct product of
its positive ordinary kernels; all its factors commute. It preserves full
genealogical forest tokens, not just a no-merger probability.

In Section 2, the coalescent exposure of the fixed physical window is exactly

    integral_0^H 1/eta_n(t) dt = H.

Thus its complete endpoint kernel is `E_H=exp(H Q_m)` for EVERY m, identical
to the fixed constant target. Every legal exterior composed with this edge
receives precisely the same full forest law, at all sample sizes. This remains
true when that exterior has genuine reticulations and fresh current-root
routing. Nothing later can recover within-edge calendar durations from an
identical boundary forest distribution.

The original strict graph grammar does not in general admit arbitrary rate
change vertices inside one edge. Even granting these changes provisionally,
their ordinary segments suppress to the admitted original edge with exposure
H. The reduced original source is the target itself. Hence this construction
fails the required later-law inequivalence, independently of that admission
restriction. It cannot be repaired merely by retaining the demographic epoch
count as a hidden source size.

The same quotient applies separately to ordinary populations and arm paths
with no intervening routing or population-meeting event. To turn demographic
epochs into actual extra hybrid cells would replace scalar-rate evolution by
fresh route/coalesce/forget operations. The linear identity (1)–(2) would then
no longer describe the full observable forest law. No cited demographic
realization theorem performs or justifies that replacement.

## 4. What this settles and what remains

The demographic negative analogy can satisfy fixed target, finite rivals,
strict positivity, deterministic parameters and exact equality. Those
requirements alone are not its decisive missing premise. The missing premise
is a response-faithful translation: expected calendar-time/SFS coordinates are
different from the declared original topology laws, and the direct population
history translation erases the very differences used by the counterexample.

Conversely, Bhaskar–Song's positive sign-change bound needs one shared scalar
Laplace density with a rival-uniform sign-change bound. Neither the
route/coalesce/forget word nor its unknown cell count supplies that bound.
Rosen et al.'s finite-SFS realization does not restore the omitted chronological
forest coordinates or create the required reticulation factors.

An actual negative solution still needs one fixed original target and, at
every finite legal prefix, one strict finite source with the exact same
topology responses and some different later topology response. An actual
positive solution still needs the target-relative finite INDEPENDENT bridge.
The calculation above excludes the direct deterministic-demography transplant
as a route to the former; it supplies neither master conclusion.

Verification: raw primary PDF passages, inherited source semantics, and the
displayed hand algebra. No numerical parameter search, source compiler,
Lean execution, Git operation or independent acceptance is claimed.
