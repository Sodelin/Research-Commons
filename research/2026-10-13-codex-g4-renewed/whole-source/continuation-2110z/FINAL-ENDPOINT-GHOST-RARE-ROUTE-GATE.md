# A boundary gate for rare-route detection of a final endpoint ghost

Contributor: Codex delegated laplace_recovery researcher, with the same
boundary case independently identified by the lead, 14 October 2026.
**Exact hand-derived formulas and an unresolved source gate.** This is not
an admitted fixed-target counterexample, a general impossibility theorem,
or a claim that the example lies in the required original COMMON fibre.
No computation or formal verification is evidence here.

## 1. Equal full arms do not suffice

Use the opened mixed tree `((A0,B),A1)`. Its initial exclusive A0 arm has
length a>=0, the mixed A0/B population has length T>0, and the exclusive
A1 arm has length a+T. Thus the two full A arms to their join have the
same positive length t=a+T. Let each A root choose A0 with probability
1-epsilon and A1 with probability epsilon. Above the join is ordinary
completion. Write p_n(epsilon) for the specified B-spine comb probability
on n labelled A roots and one B root, and kappa_(n+1) for that comb's
ordinary completion probability.

At epsilon=0 all A roots use A0. They must avoid A-only mergers during
the exclusive length a, then share one population with B. Consequently

    p_n(0)=exp(-a lambda_n) kappa_(n+1).

Only routing assignments with zero or one rare A root contribute to the
first epsilon derivative. The exact mixed-comb formula in
[the Gamma derivation](MIXED-REFERENCE-COMB-GAMMA-DERIVATION.md), equation
(1), with k=n-1 and d=1 gives

    C_(n,n-1)(T)
       =(n+1) sum_(j=1)^n p_(n,j)(T)/(j+1)
       =(n+1) E[1/(J_n(T)+1)],

where J_n is the Kingman lineage count started at n. Therefore

    p'_n(0)/p_n(0)
      =n[exp(a(n-1))(n+1)E(1/(J_n(T)+1))-1].       (1)

This formula averages the n labelled choices of the rare root; it does
not replace their actual specified comb probabilities by one favourable
label choice.

Since 1<=J_n(T)<=n, one has

    1<=C_(n,n-1)(T)<=(n+1)/2.

For the zero initial exclusive arm a=0, (1) yields the exact bound

    0<=p'_n(0)/p_n(0)<=n(n-1)/2=lambda_n.            (2)

Thus a strictly positive FULL arm t=T does not force exponential relative
growth of the first rare-route comb coefficient. A younger private A
prefix multiplies both p_n and p'_n by its no-merger factor, so it does
not repair this failure.

The quadratic scale is real. For every fixed T>0, the usual positive
completion estimate gives inf_n P(J_n(T)=1)>0: uniformly descend to a
fixed finite count before T/2, then complete before T. Hence (1) with
a=0 is bounded below by c_T n(n+1)-n for some c_T>0, and is of order n^2.
Only the upper bound (2) is needed for the obstruction.

These are finite-source closed-chart probabilities. The boundary point
is approached by strictly positive a and epsilon while preserving equal
full A arms, but that observation does not impose the exact COMMON
profile equations of an original fitting sequence.

## 2. The valid positive-exclusive-arm case

If a>0, the same exact formula gives

    p'_n(0)/p_n(0)>=n[exp(a(n-1))-1].               (3)

Thus exponential rare-route detection is valid when the dominant A
route has a strictly positive exclusive interval before first meeting B.
The exponent is this exclusive interval a; using the full arm length
a+T in its place is unjustified.

For a finite positive mixture over B routes, this comparison can be
applied componentwise when all active routes have an exclusive interval
bounded below by the same positive constant. A route that meets the
dominant A path immediately can instead dominate the endpoint comb and
leave only polynomial relative first-order growth. No claim about the
full arbitrary B-mixture follows from (3) when such a route is present.

## 3. Consequence for the local proof route

The one-sided observable-secant theorem controls negative contributions
by some polynomial in n. When weak private insertions have already been
shown to have duration zero, their relative comb contribution is itself
quadratic. The positive rare-route coefficient (2) therefore cannot be
discarded solely by comparing exponential and polynomial scales.

The outstanding issue is source-geometric and algebraic: determine
whether a zero-exclusive-arm endpoint ghost can occur in the ACTUAL
fixed full-COMMON fibre and chosen-anchor geometry, and, if it can,
whether its full observable direction can participate in the residual
clock-generator cancellation. Those exact full-profile constraints may
exclude or couple this boundary configuration; they were not used in
(1)--(3).

In particular, a two-colour opened tree is not by itself a realization of
the original problem's anchor contract. Additional original taxa and
the fixed common-clade hierarchy matter. A putative compensation using
a second B routing site can make A and B belong to one proper common
clade, in which case they are not the selected anchors. This packet
records the analytic obstruction without promoting that unverified
construction to an admitted counterexample.
