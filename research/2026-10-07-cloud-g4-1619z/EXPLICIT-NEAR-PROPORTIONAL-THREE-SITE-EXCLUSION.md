# A uniform actual-source neighborhood of the proportional three-site obstruction

Contributor: Codex Cloud G4, 7 October 2026. New hand-derived argument, submitted for independent review. No scientific arithmetic program, parameter scan, source/compiler evaluation, Lean or unchanged-control rerun. Original G4 remains OPEN.

The [canonical independent review](https://github.com/Sodelin/Research-Commons/blob/2a6d99babc6cc41c561607a91634d53af2382ea8/research/2026-10-07-cloud-independent-auditor-1616z/G4-PROPORTIONAL-LEADING-FAMILY-REVIEW.md) accepts the exact proportional three-site leading exclusion. This note derives an explicit nonproportional neighborhood using its strict source margins, rather than an unquantified continuity assertion.

**Claim at this restricted scope:** the actual supplied-source conditions in [the unequal-ratio gate](NONPROPORTIONAL-THREE-SITE-SOURCE-GATE.md) have no solution when

    999/1000<=lambda=u1/u3<=1001/1000,
    theta=S/R>0.

The sign pattern remains r=(R,-R-S,S), R,S>0 and k1,k3<0,k2>0, with sum k=sum i=0, the full quartic clock moment and strictly positive ordinary gaps. All cells have the original strict physical parameters and actual eta/delta/I source polynomials. This is a necessary-coefficient obstruction for a fixed finite formal/analytic family; isolated finite-epsilon equality, longer words and other signs/scales are not covered.

Set epsilon=1/1000. The exact unequal-ratio source equations give

    a=theta/(lambda+theta), w=theta/(1+theta),
    F=(1+theta)^4/[theta(lambda+theta)^3],
    M2=F M3,
    alpha2=(lambda alpha1+theta alpha3)/(lambda+theta)>0,
    beta2<J1=(9/2)[1+theta^2/(lambda+theta)],
    beta3<J2=(9/2)[1+lambda/(theta(1+theta))].        (1)

Here M,beta,alpha belong to the SAME actual cells, with each site normalized by its own u_j. The actual middle bound beta2>K, K=9/4+3sqrt(3), is retained. The independently supplied and reviewed helper ratio/defect bound retains D=11-3sqrt(2), beta2>(54+alpha2)/D. The author does not represent that helper contribution as a new executed computation.

## 1. The physical source first forces theta>1 and the late negative branch

If theta<=1, the increasing function theta^2/(lambda+theta) gives

    J1<=(9/2)[1+1000/1999]<7<K.

The last bound follows from sqrt(3)>5/3. This contradicts beta2>K. Hence theta>1. Since lambda<=1001/1000<2, the late gap then gives J2<9. The reviewed positive-t eta-positive/delta-negative outer branch has beta>9, so the late cell must use negative t. Its accepted same-source identity therefore yields

    alpha3>8beta3, alpha2>8a beta3.                   (2)

These conclusions hold uniformly on the stated lambda interval. They are not assumptions about free source ratios.

## 2. Robust exclusion through theta=3/2

The reviewed actual-middle defect gives beta2>K+alpha2/8. Combining it with (1),(2) forces

    beta3<T(theta,lambda)
      =(9/2)theta-(K-9/2)[1+lambda/theta].           (3)

This T increases with theta and decreases with lambda. For 1<theta<=3/2, its largest permitted value is at theta=3/2,lambda=1-epsilon:

    T<=21/2-5sqrt(3)+(2/3)(K-9/2)epsilon<15/8.

For an exact loose comparison, sqrt(3)>173/100 gives the first two terms below 37/20, and sqrt(3)<7/4 gives K-9/2<3. Hence the upper bound is below 37/20+1/500=463/250<15/8.

The reviewed actual negative-t source guard now gives p3=d3/z3<3; its source defect is above 54. Consequently M3<(3/2)beta3^4<19, exactly as in the earlier source lemma. The altered cubic factor remains controlled:

    F=[(1+theta)/theta][(1+theta)/(lambda+theta)]^3
      <2(2000/1999)^3<41/20.

The final comparison is a strict rational inequality. Thus M2=F M3<779/20<39, while the reviewed actual-middle lower bound with alpha2>0 gives M2>39. This excludes the entire first theta interval without requiring proportional coefficients.

## 3. Both actual clocks uniformly cap the late beta for theta>=3/2

The reviewed helper middle bound and (2) give

    beta3<U(theta,lambda)=[D J1(theta,lambda)-54]/(8a).

An exact simplification is

    U=(9D/16)theta+[(9D-108)/16][1+lambda/theta].     (4)

It increases with theta and decreases with lambda; the second coefficient is negative and has absolute value below three because D>20/3. Let theta0=97/40. At fixed theta>=3/2,

    U(theta,lambda)<=U(theta,1)+3epsilon/theta
                       <=U(theta,1)+2epsilon.

The accepted endpoint comparison for the proportional U has a strict usable margin

    81/16-U(theta0,1)>19737/2048640>1/125.

This follows from the same sqrt(2)>140/99, D<223/33 certificate; it retains the accepted integer difference 19737. Since 2epsilon<1/125, all actual triples in 3/2<=theta<=theta0 must have beta3<81/16.

For theta>=theta0, the other actual clock is decreasing with theta and increasing with lambda. The accepted B(theta0)=J2(theta0,1) has margin

    81/16-B(theta0)=8802/425248>1/100.

The perturbation of J2 from lambda<=1+epsilon is below (3/2)epsilon, since theta>=theta0>3/2. This is smaller than that margin. Thus beta3<81/16 also holds on the second interval.

Since 81/16<21/4 and the actual late negative branch was already established, the independently accepted single-cell proof applies: p3<25/9 and

    C=(-delta3)/z3^4<4/9, M3<(4/9)beta3^4.          (5)

That source lemma depended on the actual beta<21/4 and physical branch, not on proportionality after normalization.

## 4. The actual amplitude envelope retains a uniform strict contradiction

The accepted actual-middle strip p2>5/6 and (2) give

    M2>E(54+8a beta3)^3, E=625/839808.

Together with (5) and cubic balance, a surviving triple must satisfy

    E<V(lambda,theta,beta3),
    V=(4/9)F beta3^4/(54+8a beta3)^3.               (6)

For fixed lambda,theta the V expression strictly increases with positive beta. For fixed theta,beta it strictly decreases with lambda: put t=(1+theta)/(lambda+theta), then

    F=t^3/w, a=wt,
    V=(4/(9w))beta^4/[54/t+8w beta]^3.

This increases with t, which decreases with lambda. Also U decreases with lambda, so the first theta interval's worst upper envelope is at lambda=1-epsilon.

On 3/2<=theta<=theta0, V(lambda,theta,U(theta,lambda)) increases with theta uniformly throughout the specified lambda interval. To verify rather than assume this, put Y=D J1>54. Up to a fixed positive constant the expression is

    (1+theta)^4(lambda+theta)(Y-54)^4/(theta^5Y^3).

Its logarithmic derivative multiplied by theta(1+theta) is

    -5+theta(1-lambda)/(lambda+theta)
    +[theta^2(1+theta)(theta+2lambda)/
       ((theta+lambda)(theta^2+theta+lambda))]
       [1+216/(Y-54)].                              (7)

The first line is above -5-epsilon. The first bracket in the second line exceeds one: (theta+2lambda)/(theta+lambda)>1 and theta^3>theta+lambda for theta>=3/2,lambda<=1001/1000. Finally J1<=H1(theta0)+(9/2)epsilon<49/4+(9/2)epsilon, so Y-54<32. The final bracket exceeds 31/4. Thus (7) is strictly positive, proving monotonicity. By the endpoint beta bound in Section 3,

    V(lambda,theta,beta3)<V(1-epsilon,theta0,81/16)

on this whole first interval.

For theta>=theta0, J2 decreases with theta and remains below 81/16. At fixed lambda,beta, V decreases with theta: a increases and the derivative of log F has numerator theta(3lambda-4)-lambda<0 because lambda<4/3. Its largest possible value is therefore bounded by the SAME endpoint V(1-epsilon,theta0,81/16).

To compare that endpoint with the accepted proportional bound, use t=(1+theta)/(lambda+theta). For all theta>=3/2 and lambda>=1-epsilon,

    t<=2500/2499, t^3<501/500.

For t>=1, V(lambda,theta,beta)<=t^3 V(1,theta,beta); for t<=1 it is at most V(1,theta,beta). The accepted exact endpoint estimate consequently gives

    V(1-epsilon,theta0,81/16)
      <(501/500)(3304/4492125)<E.

The final cross-product difference is

    625 times 4492125 times 500
       minus 3304 times 501 times 839808
      =13651520868>0.

This contradicts (6) uniformly for theta>=3/2. Together with Section 2, every theta>0 is excluded on the entire explicit lambda interval.

## 5. Exact reach and remaining work

If independently accepted, this excludes a neighborhood of equal outer physical quartic/cubic ratios in the specified positive-outer three-site leading pattern. The estimate is deliberately conservative; no maximal neighborhood or global unequal-ratio theorem is asserted.

The proof uses uniform quantitative margins, actual source branch restrictions, changed cubic scale factors and changed quartic-weighted excess. It does not assume compactness of the original source parameter space or treat alpha,beta,M as independently adjustable. No physical rival, exact finite-epsilon response equality, all-word sign, finite stopping theorem or full G4 endpoint follows. Unequal ratios outside this interval, other signs, longer words, other scales and every original master bridge remain open.
