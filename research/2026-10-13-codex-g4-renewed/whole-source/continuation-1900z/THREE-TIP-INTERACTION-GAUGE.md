# Exact gauge rigidity for a genuine three-tip meeting interaction

Contributor: Codex whole-source lane, 13 October 2026.
**Hand proof candidate; independent review requested.** This is a component
of the finite meeting-shape classification required by the general source
bridge. It is not a replacement restricted G4 problem or a claim that the
four-tip/cross-shape gauge is settled. The companion
[legal invariant theorem](ANCHOR-AND-MEETING-INVARIANT.md) derives the bounded
meeting shapes from every admitted COMMON-compatible original source.

## 1. One interacting shape and its exact parameters

Consider the opened meeting tree ((A0,B),A1), with independent per-root A
routing probabilities g,q=1-g, 0<g<1. Let x0,x1 in (0,1] be the A-tip
population survivals up to their respective first branch points. Let
z in (0,1) be the survival on the A0/B internal population. The strict
inequality z<1 means that this is a genuine early A/B interaction. An
ordinary B pendant survival b in (0,1] is also present; other ordinary input pads
can remain with the private prefixes. The infinite ordinary completion is
above the three-tip root. No hidden route assignment is observed.

Write lambda_k=binom(k,2), kappa_k=1/product_(ell=2)^k lambda_ell,
and Q_k(tau) for the ordinary completed probability of a rooted labelled
topology on k singleton roots. In particular a labelled caterpillar has
probability kappa_k. Write p_(k,r)(z) for the ordinary pure-death probability
of r surviving roots after k enter a population with pair survival z.
All these functions and conventions are inherited from the exact compiler.

**Claim.** Within this interacting shape, its complete normalized two-colour
meeting table R identifies z,g,x0,x1 exactly. Its only remaining gauge in
the displayed parameters is the ordinary B pendant factor b^lambda_m.
In fact allocations (2,2) and (2,3) in R suffice. The same result holds
after exchanging the colours. This is a within-shape result: comparison
with a genuinely four-tip meeting core remains open.

## 2. Separate the split-A term algebraically

For an allowed no-monochromatic-clade topology tau with 2 A and m B leaves,
condition in the calculation on the two A routes. If both A roots take
the early tip, their pendant pair survival is x0. They then meet every B
root at the same vertex, so the entire remaining topology probability is
Q_(m+2)(tau), independent of the length of that now-common population.
If both take the late tip, their pendant survival is x1; all m B roots must
survive the internal population separately, contributing z^lambda_m.

Let S_m(tau;z) be the SUM, with unit coefficients, of the two ordinary-tree
probabilities when exactly one A root takes each tip. There is no A-arm
pair-survival factor in these two configurations. Hence

    V_(2,m)(tau)
      = b^lambda_m [(g^2 x0+q^2 x1 z^lambda_m) Q_(m+2)(tau)
                     +gq S_m(tau;z)].                       (1)

For 1 A and m B, that one A root either meets B early or late. Thus the
reference caterpillar probability is

    w_m = b^lambda_m kappa_(m+1) (g+q z^lambda_m).     (2)

Let v2 be the positive (2,1) reference probability. Combining (1)–(2) with
the legal normalized invariant gives

    R_(2,m)(tau)
      = [(g^2 x0+q^2 x1 z^lambda_m) Q_(m+2)(tau)
                             +gq S_m(tau;z)]
          / [v2 kappa_(m+1)(g+q z^lambda_m)].         (3)

This is conditioning only within the proof. All uses of R below are legal
ratios of actual whole-source output probabilities. No assignment-specific
probability S is treated as a supplied observation.

## 3. Colour-pattern contrasts isolate pure-death coordinates

For j=1,...,m define T_j as the labelled caterpillar whose initial mixed
cherry is (A1,B1), followed in order by B2,...,Bj, then A2, then
B_(j+1),...,Bm. All T_j have ordinary probability kappa_(m+2), so their
differences annihilate the first term of (3). They are distinct colour
patterns, not antisymmetric relabellings within an exchangeable colour.

When A1 is the early A root, the internal population initially contains
A1 and all m B roots. A merger history compatible with T_j can complete
exactly r=0,...,j prescribed B-spine mergers there. Its probability is

    p_(m+1,m+1-r)(z)
       / product_(ell=m+2-r)^(m+1) lambda_ell.

The remaining m+2-r roots then complete one caterpillar, with probability
kappa_(m+2-r). When A2 is the early root, no pre-root merger is compatible
with T_j, since the required initial cherry involves late A1. Consequently

    S_m(T_j;z)
      = 2 z^lambda_(m+1) kappa_(m+2)
        + sum_(r=1)^j
          p_(m+1,m+1-r)(z) kappa_(m+2-r)
              / product_(ell=m+2-r)^(m+1) lambda_ell.  (4)

Subtract successive terms, and use the definition of kappa, to obtain

    S_m(T_j;z)-S_m(T_(j-1);z)
      = kappa_(m+1) p_(m+1,m+1-j)(z)
                         /lambda_(m+2-j),    j>=2.   (5)

Every difference is strictly positive when 0<z<1. Equations (4)–(5)
retain coalescences on the early mixed population; they would fail if
that population were incorrectly replaced by a private A diagonal.

## 4. Recover z, the routing coin, and both A-arm survivals

At m=3, equations (3) and (5) give the observable ratio

    [R_(2,3)(T3)-R_(2,3)(T2)]
       /[R_(2,3)(T2)-R_(2,3)(T1)]
       = 3 p_(4,1)(z)/p_(4,2)(z).                    (6)

The inherited pure-death polynomials are

    p_(4,1)=1-(9/5)z+z^3-(1/5)z^6,
    p_(4,2)=(9/5)z-3z^3+(6/5)z^6.

Both are positive on 0<z<1. Direct polynomial differentiation gives

    p'_(4,1)p_(4,2)-p_(4,1)p'_(4,2)
      = -(9/5)(z-1)^4(z^2+z+1)(z^2+3z+1) < 0.       (7)

Thus (6) is strictly decreasing in z and uniquely determines it. This
argument has no generic-parameter exception.

With z determined, for m=2,3 define from legal quantities

    d_m = [R_(2,m)(T_m)-R_(2,m)(T_(m-1))]
                                  /p_(m+1,1)(z).

Equations (3),(5) say

    d_m = gq/[v2(g+q z^lambda_m)].                    (8)

Let k=d2/d3 and r=q/g. Then

    k=(1+r z^3)/(1+r z),
    r=(1-k)/(kz-z^3)>0.                              (9)

The map r to k is strictly decreasing, so g=1/(1+r) and q are determined.
Equation (8) then determines the positive scalar

    v2=gq/[d2(g+qz)].                                (10)

For each m=2,3, use any one T_j in (3) to recover

    c_m = [R_(2,m)(T_j) v2 kappa_(m+1)(g+q z^lambda_m)
                               -gq S_m(T_j;z)]/kappa_(m+2)
        = g^2 x0+q^2 x1 z^lambda_m.                  (11)

Since z!=z^3, these two equations uniquely determine g^2 x0 and q^2 x1,
and hence x0,x1. All S values needed here are computed by the exact
ordinary model (4), rather than observed as latent terms. This proves the
claim. Finally (1) and the same finite compiler for arbitrary n,m show
that varying b alone multiplies every V_(n,m) by b^lambda_m, exactly an
ordinary pendant gauge.

## 5. Relation to the complete finite meeting classification

A rooted ordinary opened tree with at most two tips of each colour either
has a same-colour cherry or has only mixed cherries. A same-colour two-tip
subtree can be contracted in the selected-lineage calculation: on an
Omega outcome it contributes its finite two-arm no-merger diagonal, plus
any ordinary pad. This is a bounded physical private-cell factor; no
unbounded word is fabricated. After such contractions, the remaining
genuine four-tip shapes are the mixed balanced shape
((A0,B0),(A1,B1)) and mixed caterpillars such as (((A0,B0),A1),B1), with
their colour exchanges and port relabellings. There are finitely many.

The theorem above identifies genuine three-tip interactions internally;
the two mixed four-tip forms and equivalences across forms are the next
missing classification. It does not assert that a four-tip core cannot
have the same R as a three-tip core. Zero internal length z=1 collapses
the interaction to a private A two-arm factor and ordinary completion;
then all contrasts (5) vanish, so the divisions above are not used. At a
strict original genuine interaction, the internal population has positive
length and z<1. Zero lengths in limit cores need this collapsed treatment.

The general G4 transfer also still needs the finite-unequal-cell/private
persistence issue after any gauge classification. This note establishes
neither an infinite-size bound nor the full response-law certificate.

## Evidence and attribution

The pure-death formula and finite ordinary topology compiler are inherited
from [forest_algebra.py](../../../2026-10-01-g4-admitted-testers-0819z/forest_algebra.py).
The contrast calculation, exact parameter recovery and within-shape gauge
claim above are hand derivations. A local SymPy calculation factored the
polynomial derivative in (7) exactly; that finite algebra check is not a
source theorem or a Lean verification. The source-valid bounded meeting
reduction and permitted observations are those of the companion invariant
theorem. Independent hand review is pending at submission.

The separate exact script `three_tip_contrast_checks.py` independently
composed finite forest transition laws at three rational z values and
checked all 15 split-sector topology values for m=2,3 against (4), including
the successive differences. It also checked complete rational recovery of
g,v2,x0,x1 on two parameter controls, one with x0=x1=1. All checks passed;
the receipt is `three-tip-contrast-results.json` and pins the unmodified
inherited forest compiler. These finite controls are separate from the
general hand proof and do not verify the unresolved four-tip classification.
