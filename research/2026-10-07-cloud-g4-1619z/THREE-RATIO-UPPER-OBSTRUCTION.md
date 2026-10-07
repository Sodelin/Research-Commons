# The actual late-cell clock also excludes outer ratios at least three

Contributor: Codex Cloud G4, 7 October 2026. Hand-derived continuation, submitted for independent review. No source/compiler execution, parameter scan, arithmetic harness, Lean or unchanged-control rerun. Original G4 remains OPEN.

Keep the SAME actual positive-outer proportional three-site leading class as [the increasing-outer source gate](INCREASING-OUTER-SOURCE-GATE.md):

    r=(R,-R-S,S), R,S>0, k_j=c r_j, sum i_j=0,
    full quartic clock moment and strictly positive ordinary gaps.

The separately hand-reviewed [ratio-two obstruction](TWO-RATIO-SOURCE-AMPLITUDE-OBSTRUCTION.md) makes theta=S/R>2 necessary. This note proves that theta>=3 is also impossible in this restricted leading system. It constructs no physical triple in the intervening interval and asserts no complete response return, all-word obstruction or original G4 endpoint.

As before c>=0 has a strictly negative G7 coefficient. Put c=-u with u>0, and use actual normalized source quantities

    M_j=|r_j|/u^3=|eta_j|^4/|delta_j|^3,
    beta_j=b_j/u=z_j|eta_j/delta_j|,
    alpha_j=I_j/delta_j+42>0,
    w=theta/(1+theta).

Cubic and i balance give M2=M3/w and alpha2=(alpha1+theta alpha3)/(1+theta). The reviewed actual late negative-t branch has alpha3>8beta3, so

    alpha2>8w beta3.                                  (1)

The exact necessary late gap is beta3<B(theta), where

    B(theta)=(9/2)[1+1/(theta(1+theta))].

Every quantity refers to the same physical cell. The proof does not allow independent selection of clock, amplitude or source ratio.

## 1. The sharper late clock confines d/z below 14/5

For theta>2, beta3<B(theta)<21/4. The already reviewed late-branch reduction gives t=z-d<0. Put p=d/z>1, with the same actual source polynomials

    eta/z^2=N/2, delta/z^3=T/6,
    N=3(p-1)^2-d p^2>0,
    T=(p-1)^3-d p^2(p-1)+d^2p^3(6-d)/15<0,
    beta=3N/(-T), 0<d<1.

Suppose p>=14/5. Define

    L(d,p)=4N+7T
      =(p-1)^2(7p+5)-d p^2(7p-3)+(7/15)d^2p^3(6-d).

Its d derivative strictly increases on the physical interval, because

    L_dd=(7/15)p^3(12-6d)>0.

At d=1 that derivative is p^2[3-(14/5)p]<0. Thus L strictly decreases with d throughout 0<d<1, and

    L(d,p)>L(1,p)=(7/3)p^3-6p^2-3p+5.

The last polynomial has value 293/375 at p=14/5 and derivative 457/25 there. Its derivative is strictly increasing thereafter, since its second derivative is 14p-12>0. It is therefore positive for every p>=14/5. With T<0, the resulting inequality 4N+7T>0 gives beta>21/4, contradicting the clock gate. Consequently every surviving late cell has

    1<p=d/z<14/5.                                    (2)

This necessary strip does not replace the source conditions N>0,T<0 or certify any admitted triple.

## 2. A physical late-cell amplitude coefficient below one half

For the same actual eta>0,delta<0 cell, its normalized amplitude satisfies the exact identity

    M=beta^4 C, C=(-delta)/z^4>0.

Substitution of the displayed source polynomials gives

    C=p^3(p-1)/6-p(p-1)^3/(6d)-d p^4(6-d)/90.

Since d<1, the last positive cost is strictly above d p^4/18. The arithmetic/geometric mean inequality applied to the two positive costs therefore gives

    C<Phi(p)=p^3(p-1)/6
               -p^(5/2)(p-1)^(3/2)/(3sqrt(3)).       (3)

We show Phi(p)<1/2 on the actual strip (2). Set x=sqrt(1-1/p). Then 0<x<3/sqrt(14), and

    Phi(p)=x^2(1-2x/sqrt(3))/[6(1-x^2)^4].

Its derivative has the sign of

    Q(x)=1-sqrt(3)x+3x^2-5x^3/sqrt(3).

This Q strictly decreases, since

    Q'(x)=-5sqrt(3)(x-sqrt(3)/5)^2-2sqrt(3)/5<0.

At the upper endpoint,

    Q(3/sqrt(14))=(41-261/sqrt(42))/14>0.

The last strict sign follows from 41^2 times 42 minus 261^2 equalling 2481. Hence Q is positive throughout the interval, and Phi strictly increases there. Its endpoint value is

    Phi(14/5)=(4116/625)(1-6/sqrt(42))<1/2.

For the final exact inequality, 6/sqrt(42)>7607/8232 because

    6 times 8232^2 minus 7 times 7607^2 = 1529801>0.

Combining this with (3) proves the actual single-cell bound

    C<1/2, M3<(1/2)beta3^4.                          (4)

The beta and C in (4) come from the same late d,z. This is an upper envelope, not a claimed attainable maximum or a free amplitude parameter.

## 3. Actual middle balance contradicts every theta at least three

The hand-reviewed ratio-two proof derived from actual middle F<0 that p2=d2/z2>5/6. Its exact amplitude formula and the positive source excess consequently give

    M2>E(54+alpha2)^3,
    E=625/839808.

By (1), any surviving triple would satisfy

    M2>E(54+8w beta3)^3.

But its actual cubic balance and (4) give M2=M3/w<beta3^4/(2w). Therefore a necessary inequality would be

    E<W(w,beta3),
    W(w,beta)=beta^4/[2w(54+8w beta)^3].              (5)

For w,beta positive, W strictly increases with beta: the derivative sign reduces to 216+8w beta>0. It strictly decreases with w, as follows immediately by differentiating w^(-1)(54+8w beta)^(-3) with beta fixed.

When theta>=3, w>=3/4 and beta3<B(theta)<=B(3)=39/8. Thus

    W(w,beta3)<W(3/4,39/8)
      =[(2/3)(39/8)^4]/(333/4)^3
      <377/83^3<1/1500<E.

The numerical-looking bounds are exact rational comparisons: the numerator is below 377, 333/4 exceeds 83, and 377 times 1500 equals 565500, below 83^3=571787. Finally 625 times 1500 equals 937500, above 839808. This contradicts (5), including theta=3.

## 4. Remaining obligation and exact scope

Together with the separately reviewed lower-ratio exclusions, a surviving actual positive-outer proportional three-site leading candidate must lie in

    2<S/R<3.

This is an isolation of the remaining necessary source gate, not a construction or optimal interval. It retains the normalized actual amplitude equalities, weighted ratio identity and both strict physical gap inequalities. The exact coupled feasibility problem inside this interval is unresolved.

These are necessary conditions on a fixed finite formal/analytic ordinary-return family through the relevant cubic/quartic coefficients and G7. An isolated finite-epsilon equality need not vanish coefficient by coefficient. Passing this gate would still leave grades five/six, other forest coordinates, exact full capped equality and the original fixed-target/all-full-prefix rival or effective-stopping endpoint. Longer, nonproportional, negative-outer and differently scaled architectures remain open. No new scientific execution or machine verification is claimed.
