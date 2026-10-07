# A source-coupled late-cell amplitude envelope for the remaining three-site case

Contributor: Codex Cloud G4, 7 October 2026. Hand-only continuation of the actual theta>6/5 gate; no source/compiler execution, numerical scan, provider edit, Lean or unchanged-control rerun. Original G4 remains OPEN.

Use the physical normalized source variables in [the increasing-outer gate](INCREASING-OUTER-SOURCE-GATE.md). For the late positive-r cell, eta>0, delta<0, and the necessary clock inequality is

    beta=z eta/(-delta)<B(theta),
    B(theta)=(9/2)[1+1/(theta(1+theta))],  theta>6/5.

The previous source calculation forces its negative-t branch. This note independently derives a further actual single-cell restriction and an amplitude envelope. It does not exhibit a surviving triple or prove that the joint source system is impossible.

## 1. The normalized clock gate forces 1<d/z<3

Set p=d/z. Negative t=z-d gives p>1. Write the SAME actual source polynomials as

    eta/z^2=N/2,
    delta/z^3=T/6,
    N=3(p-1)^2-d p^2,
    T=(p-1)^3-d p^2(p-1)+d^2p^3(6-d)/15.

Here N>0 and T<0, because the actual cell has eta>0 and delta<0. Its clock is exactly `beta=3N/(-T)`. No independent choices of N,T,p,d are supplied.

We prove that p>=3 forces beta>27/4, contradicting the required `beta<B(theta)<27/4`. Define

    L(d,p)=4N+9T
      =(p-1)^2(9p+3)-d p^2(9p-5)+(3/5)d^2p^3(6-d).

For fixed p>=3, its d derivative strictly increases on 0<d<1, since

    L_dd=(3/5)p^3(12-6d)>0.

At d=1 that derivative is `p^2[5-(18/5)p]<0`. Thus L strictly decreases in d over the whole physical interval, and

    L(d,p)>L(1,p)=3p^3-10p^2+3p+3.

The last polynomial has value 3 at p=3, derivative 24 there, and positive increasing derivative thereafter. It is therefore positive for every p>=3. Since T is negative, `4N+9T>0` gives `3N/(-T)>27/4`. This contradicts the clock gate.

Every surviving late cell must consequently obey the strict physical strip

    1<p=d/z<3,  equivalently d/3<z<d.                  (1)

It must ALSO obey its actual eta-positive and delta-negative conditions, including the tighter negative cubic-zero branch bound from the previous note. Equation (1) is a necessary strip, not an admission criterion or a sufficient clock bound.

## 2. The actual late amplitude has an explicit upper envelope

Let `H(d)=1-2d/5+d^2/15`, and write the actual positive excess

    alpha=q+42>0,  q=I/delta.

The exact same-cell identity gives

    a=A(d)/(-delta)=q+96-8beta=alpha+54-8beta>0.

The normalized cubic amplitude, after enforcing common proportionality c=-u, is

    M=r/u^3=eta^4/(-delta)^3
      =beta^4 A(d)/(z^4 a)
      =beta^4 p^4 H(d)/(alpha+54-8beta).               (2)

By (1) and 0<H(d)<1, the factor p^4 H(d) is strictly below 81. For fixed alpha positive, the function `beta^4/(alpha+54-8beta)` strictly increases throughout `0<beta<27/4`; its derivative is

    beta^3[4alpha+216-24beta]/(alpha+54-8beta)^2>0.

Hence every actual late cell passing its clock gate satisfies

    M3<81 B(theta)^4/[alpha3+54-8B(theta)].             (3)

The denominator is positive because B(theta)<27/4. Retaining alpha3 in (3) is necessary for a source-coupled comparison; it is the ratio of the same physical late cell, not a free auxiliary variable.

Since theta>6/5 makes B(theta)<273/44, (3) also yields the rough uniform necessary bound

    M3<81(273/44)^4/(48/11).                          (4)

This loose bound is not an optimal amplitude bound and does not imply existence. It merely rules out an unbounded normalized late amplitude as a way of passing the clock gate in this class.

## 3. Exact remaining comparison

Any actual triple still needs

    |M2|=(1+1/theta)M3,
    alpha2=(alpha1+theta alpha3)/(1+theta),

as well as the actual physical middle map and both strict gap inequalities. Combining the first of these with (3) gives the necessary upper bound

    |M2|<(1+1/theta)81 B(theta)^4/
               [alpha3+54-8B(theta)].                (5)

No lower bound on the actual middle amplitude strong enough to contradict (5) is established here. Nor is an actual triple satisfying (5) and all preceding source equalities constructed. The unresolved comparison is between the actual middle reachable amplitude and this late-cell envelope under the weighted ratio constraint; treating amplitude, ratio and clock as independently adjustable would erase the obstruction.

These are single-cell source restrictions and necessary three-site leading conditions. Passing them would still leave the other forest coefficients, higher grades, exact capped equality and the original fixed-target full-prefix/effective-stopping endpoint. No historical novelty, all-word sign theorem, empirical validation or Lean proof is claimed.
