# Full-forest third-jet cancellation along the cap-three-neutral cell

Contributor: Codex lead G4 researcher, 13 October 2026; independent
full-forest coefficient audit and exposition by Codex general-algebra
lane. **Hand-derived addendum.** This sharpens Section 1 of the
[frozen curvature-gate note](INDEPENDENT-LOCAL-CURVATURE-GATE.md), without
changing that note or its review. Its inherited source-generator identity
and source interface remain in force. No higher-order exclusion, exact
all-prefix rival family, Lean verification or G4 closure is asserted.

## 1. A source-derived full second derivative at every coin

Use the same full labelled forest algebra, ordinary generator `Q`, and
equal-arm cell `B(t,p)`. Define

    r=1-2p,   s=1-3p,   c=s-r^2=p(1-4p).

These are respectively the probability that two initial roots choose the
same arm, that three initial roots choose the same arm, and the covariance
of two distinct overlapping same-arm pair indicators. Distinct disjoint
pair indicators are independent.

Let `C` be the signed graft operator with the following row on `k`
entering opaque roots:

    unchanged forest:                       6 binom(k,3),
    each specified one-pair merger:        -3(k-2),
    each specified rooted triple tree:      1,
    each disjoint double-pair forest:        0,
    every other changed forest:             0.

For `k<3`, this is zero. Equivalently, it sums the local operator
`Q_3^2+Q_3` over each triple of entering roots, preserving every rooted
triple topology and leaving all other roots unchanged. This signed
operator is an algebraic derivative, not an admitted stochastic factor.

The exact identity is

    B_tt(0,p) = r^2 Q^2 - 2pr Q + c C.              (1)

Here is an exhaustive coordinate proof, retaining chronology shapes.
Put `lambda_k=binom(k,2)`. Conditional on the initial routing, let `M`
be the number of same-arm pairs. The no-merger second derivative is
`E[M^2]`. Counting identical, overlapping and disjoint pairs gives

    E[M^2] = r^2 lambda_k^2
              +(r-r^2)lambda_k+6c binom(k,3),

the diagonal of (1), because `r-r^2=2pr`.

For a specified merged pair `ab`, the second derivative is minus the
expected sum of the initial and post-merger holding rates, conditional
on the pair being in one arm and weighted by that event's indicator.
If `L` counts other entering roots in the same arm as `a,b`, their
holding rates differ by `L+1`. With `I_ab` the same-arm indicator,

    E[I_ab M]
      = r+2(k-2)s+binom(k-2,2)r^2,
    E[I_ab(L+1)] = r+(k-2)s.

Consequently the specified-pair coordinate is

    -r-3(k-2)s-(k-2)(k-3)r^2.                      (2)

On the right of (1), `Q^2` has specified-pair coefficient
`-(lambda_k+lambda_(k-1))=-(k-1)^2`. Substituting this and `c=s-r^2`
gives exactly (2).

A specified rooted triple tree has one possible two-merger history,
and all three roots must share an arm. Its coefficient is `s=r^2+c`,
as in (1). A specified disjoint double-pair forest has two possible
merger orders, each with route probability `r^2`; its coefficient is
`2r^2`, again as in (1). At second order there are no other changed
forest shapes. The calculation treats prebuilt entering subtrees as
opaque roots and so proves the complete graft identity at every cap.

## 2. The full fair third derivative and cancellation

Differentiate (1) with respect to `p` at fairness. Since
`r=1/2`, `r_p=-2`, `(-2pr)_p=0` and `c_p=-1`,

    B_ttp(0,1/4) = -2 Q^2-C.                        (3)

The inherited all-cap Wright--Fisher source identity is

    Q B(t,1/4) = 2 B_t(t,1/4)-B_p(t,1/4)/4.

Differentiating it twice in `t`, and using
`B_tt(0,1/4)=(Q^2-Q)/4` from the frozen note, gives

    B_ttt(0,1/4) = (Q^3-3Q^2-C)/8.                 (4)

For arbitrary nearby `p`, let `tau(t,p)=-log d2(t,p)` be the exact
pair clock. At `t=0`, `tau_t=r` and `tau_tt=-2pr`; hence (1) implies

    B(t,p)-E_(tau(t,p)) = (c/2)t^2 C+t^3 F(p)+O_m(t^4),

where `F` is analytic and the remainder is uniform for `p` near `1/4`
at each fixed full cap `m`. At fairness,
`tau=t/2-t^2/8+O(t^4)`, so the ordinary third derivative is
`(Q^3-3Q^2)/8`. Equation (4) therefore gives

    F(1/4)=-C/48.                                   (5)

Now take any physical curve

    p(t)=1/4-t/24+O(t^2),     t>0 sufficiently small.

Then `c=p(1-4p)=t/24+O(t^2)`. Its second-order term above is
`t^3 C/48+O_m(t^4)`, canceling (5). Thus

    B(t,p(t)) = E_(tau(t,p(t)))+O_m(t^4)              (6)

in the complete forest kernel for every fixed cap. The same physical
curve `p(t)` works at all caps; no coordinate-dependent fit is used.
The constants in (6) are cap dependent. There is no assertion uniform
in unbounded cap.

## 3. Exact cap-three neutrality has precisely this tangent

The exact neutral branch in the frozen note solves

    3 exp(-t)(1-4p)-8p^2(1-exp(-t))=0.

At `(t,p)=(0,1/4)`, its derivative in `p` is `-12`, so the usual
analytic implicit-function theorem gives a unique nearby analytic
branch. Differentiating the equation gives `p'(0)=-1/24`. For small
positive `t`, this branch is strictly admitted and (6) applies. It is
exactly ordinary through complete cap three, while its full kernel
at every higher fixed cap has at least fourth-order contact with the
matched ordinary passage.

The contact is exactly fourth order once cap four is included. Indeed
the exact factorization from the frozen note,

    d4-d2^6 = -1728 p^6(4p-1)^4(32p^2-32p+9)
                      /(3-12p+8p^2)^6,

and `p(t)=1/4-t/24+O(t^2)` give

    d4-d2^6 = -t^4/16+O(t^5).                       (7)

Padding this cell by fixed positive ordinary passages preserves the
all-cap order estimate and its strict cap-four disagreement.

As a diagnostic only, replace the fair cells in the frozen note's
`N`-cell approximation by these cap-three-neutral cells with `t_N=c0/N`,
where `0<c0<2H`. Choose positive ordinary gaps of total
`H-N tau(t_N,p(t_N))`. Every such word is exactly equal to `E_H`
through complete cap three; stochastic telescoping of (6) gives error
`O_m(N^-3)` at every fixed cap, with physical exposure still tending
to `H+c0/2`. Each finite word has a strict cap-four diagonal deficit.
Consequently this remains an approximation diagnostic, not an exact
arbitrary-prefix rival construction.

## 4. Precise consequence and verification boundary

The all-cap cancellation rules out a universal third-order transverse
coercivity assertion along all weak directions after pair-clock removal,
just as the frozen note ruled out the corresponding second-order claim.
It does not rule out fourth- or higher-order positive invariants,
nonlinear finite certificates, or full chronological separation of
arbitrary weak arrays. It also does not claim that ordinary-target
cap-four diagnostics settle general reticulate targets.

Correctness rests on the exhaustive full-forest coefficient calculation
and the inherited all-cap generator identity. The lead lane proposed
(1)--(6); the general-algebra lane independently audited the diagonal,
single-pair, rooted-triple and disjoint-double-pair coefficients before
accepting the derivation. The exact rational cap-four identity retains
the frozen note's separate computational receipt. No new numerical
screen, Lean proof or Rust verification is presented here. Historical
novelty is unassessed.
