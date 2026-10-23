> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Exact paired cap-three one-cell quartic

Authored 2026-10-22 UTC by the existing G3 owner. HAND proof with executed
exact symbolic identities and exact algebraic controls. No new source-law,
Lean elaboration, original-source admission or all-word recognition claim.
This continues G3-PAIRED-CAP3-COUPLED-LOWER-BOUNDARY.md and reuses its full
cap-three paired-kernel boundary, rather than fitting the two modes separately.

## Statement and strict physical domain

Let (C,D,Q,R) be the COMMON pair/triple and INDEPENDENT pair/triple survival
coordinates of one fresh natural private word, on at most three entering
current roots. Each cell has a fresh original inheritance bit, common only
within that cell in COMMON mode. One physical arm/rate/coin tuple must supply
both modes. Ordinary passages have survival in (0,1), both arms have survival
in (0,1), and the first-parent probability p is in (0,1). The original compiler
uses parent1 probability gamma=1-p. No clock cost or fixed-source-rate menu is
being imposed in this scalar private-word interface.

For one cell, with h=1-p and ordinary-bank product A in (0,1), the coordinates
are

    C = A (p x+h y),             D = A^3 (p x^3+h y^3),
    Q = A (p^2 x+h^2 y+2ph),
    R = A^3 (p^3 x^3+h^3 y^3+3ph(p x+h y)).

These four coordinates identify the full capped forest kernels only through
the retained cap-three source/forest theorem and freshness/grafting premises.
The new theorem below is an exact algebraic equivalence for this physical
one-cell parameterization. It does not supply that source receiver.

Write

    P(C,Q) = 3 C Q^2-3 C^2 Q+C^3,
    Delta = R-P(C,Q).

The previous lower-boundary result already handles Q=C, Delta<0 and Delta=0
with their explicitly stated all-finite-private-word conclusions. Assume here

    0<C<Q<1,                 Delta>0.

Set the target-dependent constants

    S = 2Q-C,                g = 4 Delta/(3C)>0.

For one unknown ordinary bank A define

    Z = A-S,                 W = Z^2+g,                 T = S Z-g,
    N(A) = C^3 W(W+Z^2)-6 C^2 W T Z
           +3 C T^2(W+Z^2)-2 T^3 Z,
    F(A) = N(A)-D g^2.

There is a strict physical one-cell word with exactly the supplied FOUR
coordinates if and only if there is a real A such that

    0<A<1,
    4(Q-C)(A-Q)>g,
    C^2 W>T^2,
    F(A)=0.

F has degree exactly four: its leading coefficient is 16(C-Q)^3, which is
strictly negative in this branch. This is a one-variable real-algebraic test.
It is complete for at most one cell; no fixed-dimensional quantifier search
over unrelated COMMON and INDEPENDENT witnesses is used.

## Forward derivation

Start with a physical one-cell witness. Put c=C/A, q=Q/A,

    u=p(1-x),     v=h(1-y),     delta=u-v,     e=A delta.

The retained exact coupled identity is

    R-P(C,Q)=3ph C A^2 delta^2.

Delta>0 implies delta!=0. Exchanging the two fresh arms and their probabilities
preserves all four coordinates, so assume e>0. Direct expansion gives

    Z = (2p-1)e,
    g = 4ph e^2,
    W = e^2,
    T = e(Ap x-Ah y).

Hence

    p = (1+Z/e)/2,
    x = (C e+T)/(A(e+Z)),
    y = (C e-T)/(A(e-Z)).

As g>0, e>|Z|. Positivity of the two arms is exactly C^2 W>T^2. Their strict
upper bounds reduce to A-C>e. In the current domain this is equivalent to

    (A-C)^2-W = 4(Q-C)(A-Q)-g >0.

For the COMMON triple coordinate, substitution gives

    A^3(p x^3+h y^3)
      = [(C e+T)^3(e-Z)^2+(C e-T)^3(e+Z)^2]/(2e g^2)
      = N(A)/g^2.

Thus F(A)=0 and all the displayed strict constraints follow.

## Reverse construction and strictness

Conversely take a real A satisfying the four constraints. Let e=sqrt(W)>0
and use the same formulas for p,x,y. Since W=Z^2+g and g>0, both e+Z and e-Z
are positive, and 0<p<1. Since C>0 and C^2 W>T^2, both arm numerators are
positive. The linear strict constraint forces

    A>Q+g/[4(Q-C)]>Q>C,
    (A-C)^2>W,

so A-C>e. In the two upper-arm tests the numerator differences are
e(A-C+e) and e(A-C-e), respectively. Both are strictly positive; hence
0<x,y<1. No equality or limiting zero-length arm has been admitted.

The four coordinate formulas now reconstruct C and Q directly, reconstruct
R as P(C,Q)+3Cg/4, and reconstruct D as N(A)/g^2. They are the supplied
coordinates, on ONE shared tuple. Two strict bookends suffice:

    z=(1+A)/2,                a=2A/(1+A),                za=A.

Both z and a lie in (0,1). Since C<Q, an ordinary-only word cannot supply the
pair. Every successful one-cell witness therefore has minimum private count
exactly one, even if longer words can also realize the same tuple.

## Consumer, execution and bounds of the result

PairedCap3OneCell.wl reuses the exact input/decision helpers in
Cap3PrivateWordCertificate.wl and the physical four-coordinate verifier in
PairedCap3LowerBoundary.wl. It exposes the quartic polynomial/formula and an
exact algebraic witness constructor. Each successful witness is checked
again by direct evaluation of ALL FOUR physical coordinates and every strict
parameter. Inexact or nonalgebraic inputs are refused. Failure to resolve or
return a witness remains Failure.

The generic negative result is explicitly

    NO_AT_MOST_ONE_PAIRED_CAP3_PRIVATE_CELL,
    LongerWords -> OPEN_BY_THIS_TEST.

The earlier proved all-word lower-boundary exclusions retain their separate
status when delegated to that consumer. The generic quartic's empty feasible
set is not an unrestricted private-word NO, and none of these statuses is an
all-original-source G3 NO.

VerifyPairedCap3OneCell.wl actually passed 13 exact controls in the existing
Wolfram mathematical evaluator: three rational biased/unequal-arm witnesses,
one genuine real-algebraic witness, the degree/known-bank constraint, lower
boundary and ordinary delegation, the universal coupled exclusion and pair
rigidity, a genuine strict two-cell word rejected by the one-cell solver,
tampered-coordinate rejection, and inexact/nonalgebraic refusals. The four
new generic witness counts were 1,1,1,1. No original Source, native parser,
Lean/Lake or model suite was executed for these controls.

The reconstruction identities independently returned {0,0,0,0}. The leading
coefficient, strict-constraint polynomial identity and expanded COMMON triple
numerator were also checked exactly. New runtime records were encrypted with
the existing featurectl identity before first persistence:

    [encrypted runtime receipt retained privately]
    ciphertext SHA256
    51070f60571f1ea382b42e70d96395019f7769e904d487a497f3f174be566cee

    [encrypted runtime receipt retained privately]
    ciphertext SHA256
    5690f2a6524d788baf056a19680f30b1b6377c9f4b6cd83a8cc64a931401d2e4

The evaluator's undefined-symbol prevalidation warning is retained in the
second record; the returned 13 named controls all passed. This is executed
exact algebra, alongside a HAND proof, and is not a Lean/kernel pass.

Remaining work: the generic strict interior can require two or more private
cells. This quartic supplies a small exact YES path and a bounded exclusion,
not a bound for those larger words. Higher entering-root caps, arbitrary
coupled panels, actual graph/reflection/readout suppliers and the original
all-input H/terminating-NO objective remain open.
